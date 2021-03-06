(function (exports) {
    var Parser = exports.Parser,
        toolkit = {
            createApp: function (config) {
                return new Parser(config)
            },
            Store: exports.Store,
            EventCenter: exports.EventCenter,
            ajax: exports.ajax,
            randomStr: exports.randomStr,
            random: exports.random,
            getURLParam: exports.getURLParam,
            setCookie: exports.setCookie,
            getCookie: exports.getCookie,
            getCookies: exports.getCookies,
            removeCookie: exports.removeCookie,
            isType: exports.isType,
            toType: exports.toType,
            clone: exports.clone,
            compare: exports.compare,
            combine: exports.combine,
            inherit: exports.inherit,
            createPagingUpdater: exports.createPagingUpdater,
            createScrollPaging: exports.createScrollPaging,
            debounce: exports.debounce,
            throttle: exports.throttle,
            curry: exports.curry,
            base64ToBlob: exports.base64ToBlob,
            sort: exports.sort,
            autoFontSize: exports.autoFontSize,
            autoEllipsis: exports.autoEllipsis,
            toChineseNumber: exports.toChineseNumber,
            nodeOps: exports.nodeOps,
            env: exports.env,
            exportModules: exports.exportModules
        }

    window.exportComponent = exports.exportComponent
    window.importComponent = exports.importComponent
    window.registerComponent = exports.registerComponent

    window.toolkit_v5 = toolkit

    if (!window.toolkit) {
        window.toolkit = toolkit
    }
})(function () {
    'use strict'

    var isIE = navigator.userAgent.match(/(?:msie|rv:)\s*(\w+)/i),
        IEVersion = isIE && isIE[1],
        isLowIE = isIE && IEVersion < 10,
        isIE8 = IEVersion === "8",
        Undefined = void 0

    polyfill()

    return exportModules({
        "Parser": Parser,
        "Store": Store,
        "VirtualDOM": VirtualDOM,
        "Component": Component,
        "ComponentLibrary": ComponentLibrary,
        "Observer": Observer,
        "EventManager": EventManager,
        "EventCenter": EventCenter,
        "utils": utils,
        "nodeOps": nodeOps,
        "env": env,
        "exportModules": function (require, module, exports) {
            module.exports = exportModules
        }
    })

    function Parser(require, module, exports) {
        module.exports = Parser

        var VirtualDOM = require("VirtualDOM"),
            Observer = require("Observer"),
            Component = require("Component"),
            EventManager = require("EventManager"),
            nodeOps = require("nodeOps"),
            addClass = nodeOps.addClass,
            removeClass = nodeOps.removeClass,
            utils = require("utils"),
            pathResolve = utils.pathResolve,
            readData = utils.readData,
            replaceData = utils.replaceData,
            traveres = utils.traveres,
            combine = utils.combine,
            classStringify = utils.classStringify,
            styleStringify = utils.styleStringify,
            mergeClassOrStyle = utils.mergeClassOrStyle,
            ShortCache = utils.ShortCache,
            collectFunctionDeps = utils.collectFunctionDeps,
            clone = utils.clone,
            inherit = utils.inherit

        nodeOps = utils = null

        var hookName = function (hook) { return "hook:" + hook },
            hooks = [
                "receiveProps", "beforePatch",
                "beforeMount", "mounted", "allMounted",
                "beforeUpdate", "updated", "allUpdated",
                "beforeUnmount", "unmounted"
            ],
            isHookEvent = matchWith(hooks.map(hookName).join(",")),
            isReservedAttr = matchWith("style", "class", "key"),
            Reg$SplitComma = /\s*,\s*/,
            $$id = 0,
            currentInstance = null,
            patchCallbacks = []

        function Parser(config, componentData) {
            if (!config) throw this._logError("????????????????????????????????????????????????")

            this._init(config, componentData)

            if (this.state.isRoot && config.el) {
                this.mount(config.el)
            }

            return this.dataContext
        }

        Parser.prototype = {
            constructor: Parser,
            mount: function (el, refNode) {
                this.el = isString(el) ? document.querySelector(el) : el
                this.refNode = refNode

                if (this.state.isRoot) {
                    this.domEventManager = new EventManager(this.el)
                }

                this._startUpdate(true)

                this.rootContext.$el = this.el
            },
            destroy: function () {
                if (this.state.destroy) return

                this.state.destroy = true
                this.updateId = null

                this._emitHook("beforeUnmount")

                this._patch(this.vdom)

                this._emitHook("unmounted")
            },
            updateComponent: function (componentData) {
                var oldAttrs = this.componentAttrs,
                    oldProps = this.props

                this._handleComponentData(componentData)

                var newAttrs = this.componentAttrs,
                    newProps = this.props,
                    isAttrsChange = JSONStringify(oldAttrs) !== JSONStringify(newAttrs),
                    isPropsChange = this._updateDataContext(newProps),
                    shouldUpdate = 0
                        || isAttrsChange
                        || isPropsChange
                        || this.slotCaches

                if (isPropsChange) {
                    this._setDirty("props")
                    this._emitHook("receiveProps", oldProps, newProps)
                }

                if (isAttrsChange) {
                    this._setDirty("attrs")
                }

                if (this.slotCaches) {
                    this._setDirty("slots")
                }

                if (shouldUpdate) {
                    this.slotCaches = null
                    this._startUpdate(true)
                }
                else if (isFunction(this.componentCallback)) {
                    this.componentCallback()
                }
            },
            _init: function (config, componentData) {
                this.name = "Root"
                this.id = ++$$id
                this.el = null // ??? IOS ???????????????????????????????????????????????? body ?????????,?????? el ?????????????????? body??????????????? touchstart ???????????????????????????
                this.runtimeHooks = null
                this.refNode = null
                this.vdom = null
                this.onceCache = null
                this.observer = new Observer()
                this.shortCache = new ShortCache()

                this._normalizeConfig(config)

                this.template = config.template
                this.render = config.__render__ // ??????????????????????????????????????????????????????????????????????????????????????????????????????????????????

                this._initState(config)

                this._initHooks(config)

                this._initPrivateStyle(config)

                this._initStore(config.store)

                this._initComponents(config.components)

                this._initMethods(config.methods)

                this._initRootContext()

                this._initPropsConfig(config.props)

                this._initEmitsConfig(config.emits)

                this._handleComponentData(componentData)

                this._initDataContext(config)

                this._markObservables(this.dataContext, config.computed, config.methods)

                this._initComputed(config.computed)

                this._initWacth(config.watch)

                this._setDirty("init")

                this._compile(config.template)

                this.props && this._emitHook("receiveProps", null, this.props)

                this.watcher.immediate()
            },
            _normalizeConfig: function (config) {
                var instance = this,
                    mergeStrats = null

                this._normalizeProps(config)
                this._normalizeEmits(config)
                this._normalizeTemplate(config)

                if (config.mixins) {
                    mergeStrats = createStrats()
                    mergeConfig(config.mixins)
                    config.mixins = null
                }

                function mergeConfig(mixins) {
                    if (!isArray(mixins)) return

                    for (var i = 0, len = mixins.length; i < len; i++) {
                        var childConfig = mixins[i]

                        if (!isPlainObject(childConfig)) continue

                        instance._normalizeProps(childConfig)
                        instance._normalizeEmits(childConfig)
                        instance._normalizeTemplate(childConfig)

                        for (var key in childConfig) {
                            if (key === "mixins") continue

                            var mergeStrat = mergeStrats[key] || defaultStrat;
                            config[key] = mergeStrat(config[key], childConfig[key])
                        }

                        mergeConfig(childConfig.mixins)
                    }
                }

                function createStrats() {
                    var mergeStrats = {}

                    mergeStrats.data = mergeData
                    mergeStrats.watch = mergeWatch
                    mergeStrats.methods = mergeStrats.computed = mergeStrats.props = mergeStrats.emits = mergeObject

                    for (var i = 0; i < hooks.length; i++) {
                        var hook = hooks[i];
                        mergeStrats[hook] = mergeHook
                    }

                    return mergeStrats
                }

                function mergeObject(object, childObject, deep) {
                    if (!object || !childObject) return object || childObject

                    for (var key in childObject) {
                        var aVal = object[key],
                            bVal = childObject[key]

                        if (!object.hasOwnProperty(key)) {
                            object[key] = clone(bVal)
                        }
                        else if (deep && aVal !== bVal && isPlainObject(aVal) && isPlainObject(bVal)) {
                            mergeObject(aVal, bVal)
                        }
                    }

                    return object
                }

                function mergeHook(hook, childHook) {
                    if (!hook || !childHook) return hook || childHook

                    return isArray(childHook)
                        ? childHook.concat(hook)
                        : [childHook].concat(hook)
                }

                function mergeData(data, childData) {
                    return function () {
                        var data$ = isFunction(data) ? data.call(this) : data,
                            childData$ = isFunction(childData) ? childData.call(this) : childData

                        return mergeObject(data$, childData$)
                    }
                }

                function mergeWatch(watch, childWatch) {
                    if (!watch || !childWatch) return watch || childWatch

                    for (var key in childWatch) {
                        var aVal = watch[key],
                            bVal = childWatch[key]

                        if (!watch.hasOwnProperty(key)) {
                            watch[key] = bVal
                        }
                        else {
                            watch[key] = isArray(bVal)
                                ? bVal.concat(aVal)
                                : [bVal].concat(aVal)
                        }
                    }

                    return watch
                }

                function defaultStrat(option, childOption) {
                    return nvl(option, childOption)
                }
            },
            _normalizeTemplate: function (config) {
                var template = config.template

                if (isUndef(template)) return

                config.template = template = template.trim()

                if (template[0] === "#") {
                    var selector = "script[type=template]" + template,
                        templateElm = document.querySelector(selector)

                    if (templateElm) {
                        config.template = templateElm.innerText.replace(/^[\n\r]|[\n\r]$/g, "")
                    }
                }
            },
            _initState: function (config) {
                this.state = {
                    mounted: false,
                    destroy: false,
                    patching: false,
                    comments: Boolean(config.comments),
                    inheritAttrs: config.inheritAttrs !== false,
                    dirty: false,
                    isRoot: true,
                    updateLock: null,
                    shouldTemplateReRender: true
                }
            },
            _initHooks: function (config) {
                var instance = this

                hooks.forEach(function (hook) {
                    var callbacks = config[hook]

                    if (isUndef(callbacks)) return

                    each(callbacks, function (callback) {
                        if (!isFunction(callback) || callback.__exists) return

                        callback.__exists = true
                        instance._on(hook, callback)
                    })

                    each(callbacks, function (callback) {
                        if (isFunction(callback)) delete callback.__exists
                    })
                })
            },
            _initPrivateStyle: function (config) {
                if (config.style) {
                    var privateStyleId = processStyle(config.style)

                    delete config.style

                    if (!privateStyleId) return

                    config.privateStyleId = privateStyleId
                }

                if (config.privateStyleId) {
                    var privateStyleId = config.privateStyleId

                    this._on("create-vdom", function (vdom) {
                        addMeta(vdom, "private-style", privateStyleId)
                    })
                }
            },
            _initStore: function (store) {
                if (isUndef(store)) return

                if (store !== store.getRaw()) {
                    var instance = this,
                        release = store.onupdate(function (changeState, causes) {
                            if (!causes.length) return

                            instance._setDirty("store")
                            instance.observer.update(causes.map(function (causeKeyPath) {
                                return "$store." + causeKeyPath
                            }))
                            instance._startUpdate()
                        })

                    this._on("beforeUnmount", release)
                } else {
                    store = store.provide()
                }

                this.store = store
            },
            _initComponents: function (userDefineComponents) {
                var localComponents = isPlainObject(userDefineComponents) && Object.assign({}, userDefineComponents)

                this.getComponent = function (name) {
                    return localComponents && localComponents[name] || Component.public[name]
                }
            },
            _initMethods: function (userDefineMethods) {
                var methods = {}

                if (isUndef(userDefineMethods)) return this.methods = methods

                var instance = this,
                    initMethod = normailzeSurrogate(function (method, name) {
                        var isRenderDep = Undefined

                        return function () {
                            var context = instance.context || instance.dataContext,
                                renderDeps = instance.render && instance.render.deps

                            if (isUndef(context)) return instance._logWarning("??????????????????" + name + " ??????????????????")

                            /**
                             * ???????????????????????????????????????????????????????????????????????????????????????????????????????????????????????? rerender ?????????
                             */
                            if (isUndef(isRenderDep) && renderDeps && (isRenderDep = Boolean(~renderDeps.indexOf(name)))) {
                                var methodDeps = collectFunctionDeps(method, instance.observables)

                                if (methodDeps) {
                                    var onupdate = instance.observer.observe(methodDeps)

                                    onupdate.deep(function () {
                                        instance.observer.update(name)
                                    })
                                }
                            }

                            return method.apply(context, arguments)
                        }
                    })

                for (var name in userDefineMethods) {
                    methods[name] = initMethod(userDefineMethods[name], name)
                }

                this.methods = methods
            },
            _initRootContext: function () {
                function RootContext() { }// ????????????,??????????????????????????????
                function DataContext() { }// ???????????????,?????? data, props, computed ?????????
                function Context() { } // ??????????????????,?????? for ?????????????????????

                this.Context = inherit(Context, inherit(DataContext, RootContext))
                this.dataContext = Context.prototype
                this.rootContext = DataContext.prototype

                var instance = this,
                    $setData = this._setData.bind(this),
                    $nextTick = function (fn) {
                        return nextTick(fn, this)
                    }

                $setData.force = function (key, val) {
                    return instance._setData(key, val, true)
                }

                Object.assign(
                    this.rootContext,
                    this.methods,
                    {
                        $setData: $setData,
                        $nextTick: $nextTick,
                        $emit: this._emit.bind(this),
                        $mount: this.mount.bind(this),
                        $destroy: this.destroy.bind(this),
                        $refs: {},
                        $store: this.store,
                        $attrs: {},
                        $elements: [],
                        $watch: null,
                        $parent: null,
                        $el: null,
                        __instance__: this
                    }
                )
            },
            _normalizeProps: function (config) {
                var userDefineProps = config.props

                if (isUndef(userDefineProps)) return

                if (isArray(userDefineProps)) {
                    var props = {}

                    for (var i = 0, len = userDefineProps.length; i < len; i++) {
                        var propName = userDefineProps[i]

                        props[propName] = null
                    }

                    config.props = props
                }
                else if (!isPlainObject(userDefineProps)) {
                    this._logError("props ??????????????????????????????")
                    config.props = {}
                }
            },
            _initPropsConfig: function (userDefineProps) {
                if (!isPlainObject(userDefineProps)) return

                var propsConfig = {},
                    defaultConfig = {
                        type: Undefined,
                        required: false,
                        validator: Undefined,
                        "default": Undefined
                    }

                for (var propName in userDefineProps) {

                    if (isReservedAttr(propName)) {
                        throw this._logError(genErrorMsg("???????????????????????????????????? prop"))
                    }

                    var propDefine = userDefineProps[propName]

                    if (isPlainObject(propDefine)) {
                        var type = propDefine.type,
                            required = Boolean(propDefine.required),
                            validator = propDefine.validator,
                            defaultVal = propDefine["default"]

                        if (validator && !isFunction(validator)) {
                            this._logError(genErrorMsg('validator ????????????'))
                            validator = Undefined
                        }

                        if (
                            type &&
                            !isFunction(type) &&
                            (
                                !isArray(type) ||
                                type.some(function (_type) {
                                    return !isFunction(_type)
                                })
                            )
                        ) {
                            this._logError(genErrorMsg("type ??????????????????"))
                            type = Undefined
                        }

                        propsConfig[propName] = {
                            type: type,
                            required: required,
                            validator: validator,
                            "default": defaultVal
                        }
                    }
                    else if (isFunction(propDefine)) {
                        propsConfig[propName] = {
                            type: propDefine,
                            required: false,
                            validator: Undefined,
                            "default": Undefined
                        }
                    }
                    else {
                        propsConfig[propName] = defaultConfig
                    }
                }

                function genErrorMsg(message) {
                    return "props ????????????????????????" + propName + "??????" + message
                }

                this.propsConfig = propsConfig
            },
            _normalizeEmits: function (config) {
                var userDefineEmits = config.emits

                if (isUndef(userDefineEmits)) return

                if (isArray(userDefineEmits)) {
                    var emits = {}

                    for (var i = 0, len = userDefineEmits.length; i < len; i++) {
                        var name = userDefineEmits[i]

                        emits[name] = null
                    }

                    config.emits = emits
                }
                else if (!isPlainObject(userDefineEmits)) {
                    this._logError("emits ??????????????????????????????")
                    config.emits = {}
                }
            },
            _initEmitsConfig: function (userDefineEmits) {
                if (!isPlainObject(userDefineEmits)) return

                var emitsConfig = {}

                for (var name in userDefineEmits) {
                    var emitsValidator = userDefineEmits[name]

                    emitsConfig[name] = isFunction(emitsValidator) ? emitsValidator : null
                }

                this.emitsConfig = emitsConfig
            },
            _handleComponentData: function (componentData) {
                if (isUndef(componentData)) return

                this.state.isRoot = false

                this.componentData = componentData
                this.name = componentData.name
                this.domEventManager = componentData.domEventManager
                this.componentCallback = componentData.complete
                this.rootContext.$parent = componentData.parentContext

                this._installComponentChildren(componentData.children)
                this._installComponentEvents(componentData.events)
                this._installComponentProps(componentData.props)
                this._installComponentAttributes(componentData.props, componentData.events)
            },
            _initDataContext: function (config) {
                var dataContext = this.dataContext,
                    props = this.props

                if (isPlainObject(props)) {
                    for (var propName in props) {
                        dataContext[propName] = props[propName]
                    }
                }

                var initData = config.data

                if (isUndef(initData)) return

                if (!isFunction(initData)) throw this._logError("data ?????????????????????????????????")

                var data = initData.call(this.dataContext)

                if (!isPlainObject(data)) throw this._logError("data ????????????????????????")

                for (var key in data) {
                    if (!data.hasOwnProperty(key)) continue

                    if (props && props.hasOwnProperty(key)) {
                        this._logError("data ??? props ???????????????????????????????????????" + key)
                    }
                    else {
                        dataContext[key] = data[key]
                    }
                }
            },
            _updateDataContext: function (dataOrProps, force) {
                if (!isObject(dataOrProps) || this.state.destroy) return false

                var dataContext = this.dataContext,
                    context = this.context || dataContext,
                    isChange = false,
                    changePaths = []

                for (var path in dataOrProps) {
                    var value = dataOrProps[path],
                        oldValue = readData(context, path),
                        success = replaceData(context, path, value)

                    if (!success && !force) continue

                    isChange = true

                    changePaths.push(path)

                    var absolutePath = this._toAbsolutePath(path)

                    this.shortCache.set(absolutePath, oldValue)

                    if (absolutePath === path) continue

                    replaceData(dataContext, absolutePath, value)

                    changePaths.push(absolutePath)
                }

                if (isChange) {
                    this.observer.update(changePaths)
                }

                return isChange
            },
            _markObservables: function (dataContext, userDefineComputed, userDefineMethods) {
                var observables = {}

                for (var key in dataContext) {
                    if (dataContext.hasOwnProperty(key)) {
                        observables[key] = Undefined
                    }
                }

                if (userDefineComputed) {
                    for (var key in userDefineComputed) {
                        if (userDefineComputed.hasOwnProperty(key)) {
                            observables[key] = Undefined
                        }
                    }
                }

                if (this.rootContext.$store) {
                    observables["$store"] = Undefined
                }

                if (userDefineMethods) {
                    Object.assign(observables, userDefineMethods)
                }

                this.observables = observables
            },
            _initComputed: function (userDefineComputed) {
                if (isUndef(userDefineComputed)) return

                var dataContext = this.dataContext,
                    observer = this.observer,
                    observables = this.observables,
                    Reg$NestingPath = /[.\[]/,
                    computeds = {}

                for (var name in userDefineComputed) {
                    var errorMsg = 0
                        || Reg$NestingPath.test(name) && "????????????????????????????????????"
                        || dataContext.hasOwnProperty(name) && "??? data ??? props ??????????????????"
                        || !isFunction(userDefineComputed[name]) && "????????????????????????"

                    if (errorMsg) {
                        throw this._logError("computed ??????" + name + "???" + errorMsg)
                    }
                    else {
                        computeds[name] = userDefineComputed[name]
                    }
                }

                for (var name in computeds) {
                    var inited = dataContext.hasOwnProperty(name)

                    if (inited) continue

                    init(name, computeds[name])
                }

                /**?????????????????????????????? */
                computeds = observables = init = null

                function init(name, compute) {
                    var computeDeps = collectFunctionDeps(compute, observables)

                    if (computeDeps) {
                        computeDeps.forEach(function (keyPath) {
                            var pathKeys = pathResolve(keyPath),
                                name$ = pathKeys[0],
                                isUninitComputed = computeds.hasOwnProperty(name$) && !dataContext.hasOwnProperty(name$)

                            if (!isUninitComputed) return

                            init(name$, computeds[name$])
                        })

                        var onupdate = observer.observe(computeDeps)

                        onupdate.deep(function () {
                            var oldValue = dataContext[name],
                                newValue = compute.call(dataContext)

                            dataContext[name] = newValue

                            !isEqual(oldValue, newValue) && observer.update(name)
                        })
                    }

                    dataContext[name] = compute.call(dataContext)
                }
            },
            _initWacth: function (userDefineWatchs) {
                var instance = this,
                    observer = this.observer,
                    immediateHandlers,
                    handlers = {},
                    inTaskQueue = {},
                    taskQueue = [],
                    watcher = null

                watcher = this.watcher = {
                    add: function (keyPath, handler, config) {
                        config || (config = {})

                        if (!isString(keyPath)) return instance._logError("watch ?????????????????? keyPath ?????????????????????????????????" + keyPath + "???")
                        if (!isFunction(handler)) return instance._logError("watch ?????????????????? handler ???????????????")

                        var onupdate = observer.observe(keyPath),
                            immediate = Boolean(config.immediate),
                            deep = Boolean(config.deep),
                            handlerId = genHandlerId(keyPath),
                            release = deep ? onupdate.deep(addWatchTask) : onupdate(addWatchTask)

                        handlers[handlerId] = handler

                        if (immediate) {
                            immediateHandlers || (immediateHandlers = [])
                            immediateHandlers.push(handlerId)
                        }

                        function addWatchTask(causes) {
                            if (inTaskQueue[handlerId]) return

                            inTaskQueue[handlerId] = true

                            var context = instance.context || instance.dataContext,
                                isDeep = causes.every(function (causeKeyPath) {
                                    return causeKeyPath !== keyPath && causeKeyPath.indexOf(keyPath) === 0
                                }),
                                cacheValue = !isDeep && instance.shortCache.get(instance._toAbsolutePath(keyPath))

                            taskQueue.push(function () {
                                delete inTaskQueue[handlerId]

                                var newValue = readData(context, keyPath),
                                    oldValue = isDeep ? newValue : cacheValue

                                if (!isDeep && oldValue === newValue) return handlerId

                                handler.call(context, oldValue, newValue)

                                return handlerId
                            })
                        }

                        return function unwatch() {
                            release()
                            delete handlers[handlerId]
                        }
                    },
                    run: function () {
                        for (var i = 0; i < taskQueue.length; i++) {
                            taskQueue[i]()
                        }

                        taskQueue.length = 0
                    },
                    immediate: function () {
                        if (!immediateHandlers) return

                        var dataContext = instance.dataContext

                        immediateHandlers.forEach(function (handlerId) {
                            if (inTaskQueue[handlerId]) return

                            inTaskQueue[handlerId] = true

                            var handler = handlers[handlerId],
                                keyPath = extractKeyPath(handlerId)

                            taskQueue.push(function () {
                                delete inTaskQueue[handlerId]

                                var value = readData(dataContext, keyPath)

                                handler.call(dataContext, Undefined, value)

                                return handlerId
                            })
                        })

                        immediateHandlers = Undefined

                        this.run()
                    }
                }

                this.rootContext.$watch = function (keyPath, handler, config) {
                    var unwatch = watcher.add(keyPath, handler, config)

                    watcher.immediate()

                    return unwatch
                }

                var normalWatchs = this._normalizeWatch(userDefineWatchs)

                for (var i = 0, len = normalWatchs.length; i < len; i++) {
                    var tuple = normalWatchs[i],
                        keyPath = tuple[0],
                        watchDefine = tuple[1]

                    watcher.add(keyPath, watchDefine.handler, watchDefine)
                }

                function genHandlerId(keyPath) {
                    return keyPath + "#" + Math.random()
                }

                function extractKeyPath(handlerId) {
                    return handlerId.split("#")[0]
                }
            },
            _normalizeWatch: function (userDefineWatchs) {
                var instance = this,
                    watchConfigs = []

                if (!isPlainObject(userDefineWatchs)) return watchConfigs

                for (var keyPath in userDefineWatchs) {
                    var watchDefines = userDefineWatchs[keyPath]

                    each(watchDefines, function (watchDefine) {
                        if (isUndef(watchDefine)) return
                        addNormalWatch(keyPath, watchDefine)
                    })
                }

                function addNormalWatch(keyPath, watchDefine) {
                    var handler = isPlainObject(watchDefine) ? watchDefine.handler : watchDefine,
                        immediate = isPlainObject(watchDefine) ? Boolean(watchDefine.immediate) : false,
                        deep = isPlainObject(watchDefine) ? Boolean(watchDefine.deep) : false

                    if (isString(handler) && isPlainObject(instance.methods) && isFunction(instance.methods[handler])) {
                        handler = instance.methods[handler]
                    }

                    if (isFunction(handler)) {
                        var normalWatchDefine = {
                            handler: handler,
                            immediate: immediate,
                            deep: deep
                        }

                        watchConfigs.push([keyPath, normalWatchDefine])
                    }
                    else if (isString(handler)) {
                        _logError(keyPath, "??? methods ???????????????" + handler + "?????????")
                    }
                    else {
                        _logError(keyPath, "??????????????? handler")
                    }
                }

                function _logError(keyPath, message) {
                    instance._logError("watch ??????????????????" + keyPath + "??????" + message)
                }

                return watchConfigs
            },
            _setData: function (keyPath, val, force) {
                var dataPatch

                if (isString(keyPath)) {
                    dataPatch = {}
                    dataPatch[keyPath] = val
                } else if (isPlainObject(keyPath)) {
                    dataPatch = keyPath
                }

                if (!dataPatch) return

                var propsConfig = this.propsConfig,
                    data = {},
                    shouldUpdate = false

                for (var keyPath$ in dataPatch) {
                    if (!propsConfig || !(keyPath$ in propsConfig)) {
                        data[keyPath$] = dataPatch[keyPath$]
                        shouldUpdate = true
                    }
                    else {
                        this._logError("???????????? $setData ?????? props ?????????" + keyPath$)
                    }
                }

                if (!shouldUpdate) return

                var isDataChange = this._updateDataContext(data, force)

                if (!isDataChange) return

                this._setDirty("data")
                this._startUpdate()
            },
            _compile: function (template) {
                var instance = this,
                    render = this.render,
                    renderHelperMap = this._createRenderHelper(),
                    renderHelperNames = Object.keys(renderHelperMap),
                    renderHelpers = renderHelperNames.map(function (name) {
                        return renderHelperMap[name]
                    })

                /**?????????????????????????????? */
                renderHelperMap = null

                if (!render) {
                    var convertor = this._createConvertor(),
                        rootToken = parseTemplate(template)

                    traveres(rootToken, {
                        onWalkDown: function (token, i) {
                            if (token.type !== "tag") return

                            token.isComponent = Boolean(instance.getComponent(token.tagName))
                            convertor.processAttrs(token, i)
                        },
                        onWalkUp: function (token, i) {
                            var type = token.type

                            if (convertor[type]) {
                                convertor[type](token, i)
                            }
                            else {
                                throw Error("???????????? token ??????")
                            }
                        }
                    })

                    var renderCode = rootToken.code

                    try {
                        render = Function.apply(Function, renderHelperNames.concat(renderCode))
                    } catch (e) {
                        throw this._logError([
                            "????????????????????????",
                            ["???????????????", e],
                            ["???????????????", renderCode]
                        ])
                    }

                    render.deps = convertor.depCollector.getDeps()
                    this.render = render

                    /**?????????????????????????????? */
                    convertor = null
                }

                var state = this.state,
                    isRoot = state.isRoot,
                    name = this.name

                if (render.deps) {
                    var onupdate = this.observer.observe(render.deps)

                    onupdate.deep(function () {
                        state.shouldTemplateReRender = true
                    })
                }

                this.renderVdom = function (context) {
                    try {
                        var vdom = render.apply(context, renderHelpers)

                        if (!vdom) {
                            vdom = VirtualDOM.createComment(name)
                        }
                        else if (!isRoot) {
                            vdom.children.unshift(VirtualDOM.createComment(name + " Start"))
                            vdom.children.push(VirtualDOM.createComment(name + " End"))
                        }

                        return vdom
                    } catch (e) {
                        throw this._logError([
                            "????????????????????????",
                            ["???????????????", e],
                            ["???????????????", render]
                        ])
                    }
                }
            },
            _createConvertor: function () {
                var instance = this,
                    depCollector = createDepCollector(),
                    tokenStack = [],
                    uniq = {},
                    attrTypes = { "@": "event", "#": "slotInfo", "$": "dynamicProp", ":": "directive" },
                    Reg$LoopDirective = /^\s*(?:([\w$]+)|\(([^)]+)\))\s+in\s+(.+)$/,
                    Reg$MustacheContent = /{{((?:[^}]|}(?!})|}(?=}}))*)}}/,
                    Reg$MixedContent = new RegExp("([^{]+)|" + Reg$MustacheContent.source + "|({)", "g"),
                    Reg$RangeGrammar = /\((.+?)\.{3}([^)]+)\)/,
                    Reg$TestKeyPath = /^\s*[\w.$\[\]'"]+\s*$/,
                    Reg$ArrowFunction = /^\s*(?:([\w$]+)|\(([^\)]*)\))\s*=>\s*(?:\{(.+)\}|\((.+)\)|([^(\s].*))\s*$/

                return {
                    depCollector: depCollector,
                    "root": function (token) {
                        var childrenCode = genChildrenCode(token.children)

                        token.code = 'with(this){return ' + callMethod("__output__", childrenCode) + '}'

                        markLocation(null)
                    },
                    "tag": function (token) {
                        markLocation(token.open_loc)

                        var tagName = token.tagName

                        if (tagName === "slot") {
                            if (instance.state.isRoot) return instance._logWarning("????????????????????? slot ??????")

                            genSlotCode(token)
                        }
                        else if (tagName === "transition") {
                            genTransitionCode(token)
                        }
                        else if (tagName === "block") {
                            genBlockCode(token)
                        }
                        else if (token.isComponent) {
                            genComponentCode(token)
                        }
                        else {
                            genElementCode(token)
                        }

                        processModel(token)
                        processShow(token)
                        processRef(token)
                        processFor(token)
                        processOnce(token)
                        processSlot(token)
                        processIf(token)
                        processElseIf(token)
                        processElse(token)
                    },
                    "text": function (token) {
                        markLocation(token.loc)

                        var textContent = token.textContent

                        textContent = joinMixedContentParts(ensureText(splitMixedContent(textContent)))

                        var directives = token.parent && token.parent.directives

                        if (directives && directives.hasOwnProperty("allow-html")) {
                            return token.code = genCode(function () {
                                return callMethod("__createHTML__", textContent)
                            })
                        }

                        token.code = genCode(function () {
                            return callMethod("__createText__", textContent)
                        })

                        processSlot(token)
                    },
                    "comment": function (token) {
                        markLocation(token.loc)

                        var textContent = token.textContent

                        if (instance.state.comments) {
                            token.code = genCode(function () {
                                return callMethod("__createComment__", addDoubleQuot(textContent))
                            })

                            processSlot(token)
                        }
                        else {
                            token.code = null
                        }
                    },
                    "processAttrs": function (token) {
                        if (token.type !== "tag") return

                        var tagName = token.tagName,
                            isComponent = token.isComponent,
                            tokenAttrs = token.attrs

                        var staticAttrs = token.staticAttrs = {},
                            attrs = {},
                            attrsList = token.attrsList = [attrs],
                            directives = token.directives = {},
                            exist = {}

                        for (var i = 0, len = tokenAttrs.length; i < len; i++) {
                            var tokenAttr = tokenAttrs[i],
                                attrName = tokenAttr.name,
                                attrData = processAttrData(tokenAttr),
                                name = attrData.name,
                                type = attrData.type,
                                value = attrData.value,
                                hasMustache = attrData.hasMustache

                            markLocation(attrData.loc)

                            if (exist[attrName]) {
                                instance._logWarning('?????????????????????' + name + '???')
                            }

                            exist[attrName] = true

                            switch (type) {
                                case "event":
                                    if (hasMustache)
                                        throwError('???????????????????????? Mustache ??????')

                                    depCollector.collect(value)
                                    addEventInfo(name, value, attrData.modifers, attrs, token)

                                    continue
                                case "slotInfo":
                                    if (hasMustache)
                                        throwError('?????????????????????????????????????????????,???????????? Mustache ????????????????????????#default="paramA, paramB"')

                                    token.slotInfo = { name: name, slotScope: value || null }

                                    continue
                                case "directive":
                                    var isPureDirective = 0
                                        || name === "allow-html"
                                        || name === "else"
                                        || name === "once"

                                    if (!isPureDirective && !value)
                                        throwError(name + ' ???????????????????????????')

                                    if (isPureDirective && value) {
                                        instance._logWarning(name + ' ?????????????????????')
                                        value = Undefined
                                    }

                                    if (hasMustache)
                                        throwError('???????????????????????? Mustache ??????')

                                    /**
                                     * for ????????????????????????????????????????????????????????????
                                     */
                                    if (name !== "for" && value) {
                                        depCollector.collect(value)
                                    }

                                    if (name === "bind") {
                                        attrsList.push(value)
                                        attrsList.push(attrs = {})

                                        continue
                                    }

                                    if (isComponent && name === "model") {
                                        var propName = attrData.directiveProp || "modelValue"

                                        directives[name] || (directives[name] = [])
                                        directives[name].push({
                                            modelParam: propName,
                                            value: value,
                                            loc: attrData.loc
                                        })

                                        continue
                                    }

                                    directives[name] = {
                                        value: value,
                                        loc: attrData.loc
                                    }
                                    continue
                                case "dynamicProp":
                                case "prop":
                                    var isDynamic = type === "dynamicProp"

                                    if (tagName === "slot" && name === "name") {
                                        if (isDynamic || hasMustache)
                                            throwError('slot ????????? name ???????????????????????????????????????????????????????????? Mustache ??????')

                                        token.slotName = name
                                        continue
                                    }

                                    if (isDynamic && hasMustache)
                                        throwError('???????????????????????? Mustache ??????')

                                    if (isDynamic) {
                                        depCollector.collect(value)
                                    }
                                    else if (hasMustache) {
                                        var parts = splitMixedContent(value)

                                        if (name === "class" || name === "style") {
                                            parts.forEach(function (part) {
                                                if (part.type !== "expr") return
                                                part.content = callMethod(name === "class" ? "__class__" : "__style__", part.content)
                                            })
                                        }
                                        else {
                                            ensureText(parts)
                                        }

                                        value = joinMixedContentParts(parts)
                                    }
                                    else {
                                        staticAttrs[name] = value
                                        value = addDoubleQuot(value)
                                    }

                                    if (name === "key") {
                                        token.attrKey = value
                                    }
                                    else {
                                        attrs[name] = value
                                    }
                            }
                        }

                        token.lastAttrs = attrs

                        if (
                            token.parent.type === "root" && // ?????????
                            !instance.state.isRoot && // ???????????????
                            instance.state.inheritAttrs // ??????????????? prop ??????
                        ) {
                            attrsList.push('__inheritAttrs__()')
                        }
                    }
                }

                function processAttrData(attr) {
                    attr = Object.assign({
                        type: "prop",
                        modifiers: Undefined,
                        directiveProp: Undefined
                    }, attr)

                    processAttrType(attr)
                    processAttrModifiers(attr)

                    return attr
                }

                function processAttrType(attr) {
                    var name = attr.name,
                        type = attrTypes[name[0]]

                    if (!type) return

                    if (type === "directive" && ~name.indexOf("|")) {
                        var splited = name.split("|")
                        name = splited[0]
                        attr.directiveProp = splited[1]
                    }

                    attr.name = name.substring(1)
                    attr.type = type
                }

                function processAttrModifiers(attr) {
                    var name = attr.name,
                        Reg$Modifiers = /(\.[\w-]+)+/,
                        matcher = name.match(Reg$Modifiers)

                    if (!matcher) return

                    attr.name = name.replace(matcher[0], "")
                    attr.modifiers = genModifiers(matcher[0])
                }

                function genModifiers(modifierStr) {
                    var modifiers = []

                    modifierStr.split(".").forEach(function (modifier) {
                        if (modifier === "") return

                        modifiers.push(modifier)
                        modifiers[modifier] = true
                    })

                    return modifiers
                }

                /**
                 * ????????????????????????????????????????????????????????????????????????????????????
                 */
                function createDepCollector() {
                    var collects = {},
                        observables = {}

                    for (var name in instance.methods) {
                        if (instance.methods.hasOwnProperty(name)) {
                            observables[name] = Undefined
                        }
                    }

                    for (var name in instance.dataContext) {
                        if (instance.dataContext.hasOwnProperty(name)) {
                            observables[name] = Undefined
                        }
                    }

                    if (instance.rootContext.$store) {
                        observables["$store"] = Undefined
                    }

                    /**
                     * 'head.keyA[1].keyB["keyC"].indexOf(...)' -> head.keyA[1].keyB["keyC"] ??????????????????????????????
                     * 'methodCall()' -> methodCall ??????????????????
                     */
                    var keyPathReg = "(([\\w$]+)(?:(?=(\\.[\\w$]+|\\[\\s*(?:\\d+|([\"']).+?\\4)\\s*\\]))\\3(?!\\s*\\())*)",
                        Reg$KeyPathInTemplate = new RegExp("(?:^|[^\\s.\\[\"'])\\s*" + keyPathReg, "g")

                    return {
                        collect: function (expression) {
                            var matcher = null

                            while (matcher = Reg$KeyPathInTemplate.exec(expression)) {
                                var keyPath = matcher[1],
                                    head = matcher[2]

                                if (head in observables) {
                                    collects[keyPath] = Undefined
                                }
                            }
                        },
                        getDeps: function () {
                            var deps = Object.keys(collects)

                            return deps.length ? deps : null
                        }
                    }
                }

                function processModel(token) {
                    var binding = token.directives["model"]

                    if (!binding) return

                    var attrs = token.lastAttrs,
                        eventName = "",
                        eventHandler = "",
                        bindingData = "",
                        modifiers = null

                    if (token.isComponent) {
                        var bindings = binding

                        for (var i = 0, len = bindings.length; i < len; i++) {
                            var binding$ = bindings[i],
                                propName = binding$.modelParam

                            markLocation(binding$.loc)

                            eventName = "update:" + propName
                            eventHandler = "$model.component"
                            bindingData = dataOwns(binding$.value)

                            addEventInfo(eventName, callMethod(eventHandler, addDoubleQuot(bindingData), "$args[0]"), modifiers, attrs, token)
                            attrs[propName] = bindingData
                        }

                        return
                    }

                    markLocation(binding.loc)

                    if (token.genTransitionCode) return instance._logWarning("transition ???????????? model ??????")
                    if (token.genSlotCode) return instance._logWarning("slot ???????????? model ??????")

                    var tagName = token.tagName,
                        inputType = token.staticAttrs.type || 'text',
                        isInput = tagName === 'input' && ~'text,number,password,search,email,tel,url'.indexOf(inputType),
                        isCheckBox = tagName === 'input' && inputType === 'checkbox',
                        isRadio = tagName === 'input' && inputType === 'radio',
                        isTextarea = tagName === 'textarea',
                        isSelect = tagName === 'select',
                        bindingHandler = ""

                    bindingData = dataOwns(binding.value)

                    if (isInput || isTextarea) {
                        eventName = "input"
                        eventHandler = "$model.input"
                        bindingHandler = "$bind.input"
                        modifiers = genModifiers("ime")
                    }
                    else if (isCheckBox) {
                        eventName = "change"
                        eventHandler = "$model.checkbox"
                        bindingHandler = "$bind.checkbox"
                    }
                    else if (isRadio) {
                        eventName = "change"
                        eventHandler = "$model.radio"
                        bindingHandler = "$bind.radio"
                    }
                    else if (isSelect) {
                        eventName = "change"
                        eventHandler = "$model.select"
                        bindingHandler = "$bind.select"
                    }
                    else {
                        throwError("model ???????????????????????????????????????")
                    }

                    addEventInfo(eventName, callMethod(eventHandler, "$event", addDoubleQuot(bindingData)), modifiers, attrs, token)

                    token.code = genCode(function (code) {
                        return callMethod(bindingHandler, code(), bindingData)
                    }, token.code)
                }

                function dataOwns(dataKey) {
                    if (
                        instance.dataContext.hasOwnProperty(dataKey) &&
                        (!instance.props || !instance.props.hasOwnProperty(dataKey))
                    ) {
                        return dataKey
                    }
                    else {
                        throwError("model ?????????????????? data ???????????????????????????????????????" + dataKey + "???")
                    }
                }

                function processShow(token) {
                    var binding = token.directives["show"]

                    if (!binding) return

                    markLocation(binding.loc)

                    if (token.genTransitionCode) return instance._logWarning("transition ???????????? show ??????")

                    token.code = genCode(function (code) {
                        return callMethod("__show__", code(), binding.value)
                    }, token.code)
                }

                function processRef(token) {
                    var binding = token.directives["ref"]

                    if (!binding) return

                    markLocation(binding.loc)

                    if (token.genTransitionCode) return instance._logWarning("transition ???????????? ref ??????")
                    if (token.genSlotCode) return instance._logWarning("slot ???????????? ref ??????")
                    if (token.genBlockCode) return instance._logWarning("block ???????????? ref ??????")
                    if (uniq[binding.value]) return instance._logWarning("ref ??????????????????????????????" + binding.value)

                    token.code = genCode(function (code) {
                        var isArrayRef = tokenStack.length

                        return callMethod("__saveRef__", addDoubleQuot(binding.value), isArrayRef ? "true" : "false", code())
                    }, token.code)
                }

                function processFor(token) {
                    var binding = token.directives["for"]

                    if (!binding) return

                    markLocation(binding.loc)

                    if (token.genSlotCode) return instance._logWarning("slot ???????????? for ??????")

                    var matcher = binding.value.match(Reg$LoopDirective),
                        alias = (matcher[1] || matcher[2]).trim().split(Reg$SplitComma),
                        valueAlias = alias[0],// ?????????
                        indexAlias = alias[1],// ???????????? or ????????????
                        objectIndexAlias = alias[2],// ???????????????
                        source = matcher[3],// ?????????
                        rangeMatcher = source.match(Reg$RangeGrammar)

                    if (
                        valueAlias === indexAlias ||
                        valueAlias === objectIndexAlias ||
                        (indexAlias && indexAlias === objectIndexAlias)
                    ) {
                        throwError("for ??????????????????????????????")
                    }

                    if (rangeMatcher) {
                        var from = rangeMatcher[1].trim(),
                            to = rangeMatcher[2].trim()

                        depCollector.collect(from)
                        depCollector.collect(to)

                        source = codify({ from: from, to: to })
                    }
                    else {
                        depCollector.collect(source)
                    }

                    token.code = genCode(function (code) {
                        tokenStack.push(token)

                        var tokenCode = callMethod(
                            "__renderList__",
                            source,
                            createFunction("", [valueAlias, indexAlias, objectIndexAlias], "return " + code()),
                            addDoubleQuot(source),
                            addDoubleQuot(valueAlias),
                            addDoubleQuot(indexAlias),
                            objectIndexAlias && addDoubleQuot(objectIndexAlias)
                        )

                        tokenStack.pop()

                        return tokenCode
                    }, token.code)

                    token.code = genCode(function (code) {
                        var branchKey = token.branchKey

                        delete token.branchKey

                        return callMethod(
                            "__createFragment__",
                            branchKey ? codify({ key: branchKey }) : null,
                            code()
                        )
                    }, token.code)
                }

                function processOnce(token) {
                    var binding = token.directives["once"]

                    if (!binding) return

                    markLocation(binding.loc)

                    if (token.genTransitionCode) return instance._logWarning("transition ???????????? once ??????")
                    if (token.genSlotCode) return instance._logWarning("slot ???????????? once ??????")

                    token.code = genCode(function (code) {
                        return callMethod("__once__", genStaticId(), createFunction("", "", "return " + code()))
                    }, token.code)
                }

                function processSlot(token) {
                    var parent = token.parent

                    if (parent.type !== "tag" || !parent.isComponent) return

                    var slotInfo = token.slotInfo || { name: "default", slotScope: null },
                        slotName = slotInfo.name,
                        slotScope = slotInfo.slotScope

                    token.code = genCode(function (code) {
                        return codify({
                            slotName: addDoubleQuot(slotName),
                            slotScope: slotScope
                                ? JSON.stringify(slotScope.split(","))
                                : null,
                            render: createFunction("", slotScope, "return " + code())
                        })
                    }, token.code)
                }

                function processIf(token) {
                    var binding = token.directives["if"]

                    if (!binding) return

                    markLocation(binding.loc)

                    checkBranchDirective(token)

                    token.branchKey = genStaticId()

                    token.code = genCode(function (code) {
                        return binding.value + "?" + code() + ": null"
                    }, token.code)
                }

                function processElseIf(token) {
                    var binding = token.directives["else-if"]

                    if (!binding) return

                    markLocation(binding.loc)

                    checkBranchDirective(token)

                    var tokenWithIf = findIf(token)

                    token.branchKey = genStaticId()

                    token.code = genCode(function (code) {
                        return binding.value + "?" + code() + ": null"
                    }, token.code)

                    tokenWithIf.code = genCode(function (codeWithIf, code) {
                        var codeIf = codeWithIf(),
                            index = codeIf.lastIndexOf("null")

                        return codeIf.substring(0, index) + code() + codeIf.substring(index + 4)
                    }, tokenWithIf.code, token.code)

                    token.code = Undefined
                }

                function processElse(token) {
                    var binding = token.directives["else"]

                    if (!binding) return

                    markLocation(binding.loc)

                    checkBranchDirective(token)

                    var tokenWithIf = findIf(token)

                    token.branchKey = genStaticId()

                    tokenWithIf.code = genCode(function (codeWithIf, code) {
                        var codeIf = codeWithIf(),
                            index = codeIf.lastIndexOf("null")

                        return codeIf.substring(0, index) + code() + codeIf.substring(index + 4)
                    }, tokenWithIf.code, token.code)

                    token.code = Undefined
                }

                function genSlotCode(token) {
                    token.genSlotCode = true
                    token.code = genCode(function () {
                        return callMethod(
                            "__createSlot__",
                            addDoubleQuot(token.slotName || "default"),
                            genAttrs(token) || null,
                            genChildrenCode(token.children)
                        )
                    })
                }

                function genTransitionCode(token) {
                    token.genTransitionCode = true
                    if (isLowIE) return genBlockCode(token)

                    var childsWithoutKey = token.children.filter(function (child) {
                        return isUndef(child.attrKey || child.branchKey)
                    })

                    if (childsWithoutKey.length) {
                        instance._logWarning("transition ?????????????????? key"/*,childsWithoutKey.map(function (child) { return child.open_loc || child.loc }) */)

                        token.children = token.children.filter(function (child) {
                            return isDef(child.attrKey || child.branchKey)
                        })

                        if (!token.children.length) {
                            return token.code = Undefined
                        }
                    }

                    token.code = genCode(function () {
                        return callMethod(
                            "__setTransition__",
                            genAttrs(token) || null,
                            genChildrenCode(token.children)
                        )
                    })
                }

                function genComponentCode(token) {
                    token.genComponentCode = true
                    token.code = genCode(function () {
                        return callMethod(
                            "__createComponent__",
                            addDoubleQuot(token.tagName),
                            genAttrs(token) || null,
                            genChildrenCode(token.children)
                        )
                    })
                }

                function genBlockCode(token) {
                    token.genBlockCode = true
                    token.code = genCode(function () {
                        return callMethod(
                            "__createFragment__",
                            genAttrs(token) || null,
                            genChildrenCode(token.children)
                        )
                    })
                }

                function genElementCode(token) {
                    token.genElementCode = true
                    token.code = genCode(function () {
                        return callMethod(
                            "__createElement__",
                            addDoubleQuot(token.tagName),
                            genAttrs(token) || null,
                            genChildrenCode(token.children)
                        )
                    })
                }

                function genChildrenCode(tokens) {
                    var codes = []

                    for (var i = 0, len = tokens.length; i < len; i++) {
                        var token = tokens[i]

                        if (isUndef(token.code)) continue

                        codes.push(isFunction(token.code) ? (token.code = token.code()) : token.code)
                    }

                    return codify(codes)
                }

                function genCode(genFunc) {
                    var nestedGens = slice(arguments, 1)

                    return function () {
                        return genFunc.apply(null, nestedGens)
                    }
                }

                function genAttrs(token) {
                    var attrsList = token.attrsList,
                        key = token.attrKey || token.branchKey

                    if (isDef(key)) {
                        token.lastAttrs.key = key
                    }

                    attrsList = attrsList.filter(function (attrs) {
                        return isString(attrs) || isNotEmptyObject(attrs)
                    })

                    if (attrsList.length > 1) {
                        return callMethod("__mergeAttrs__", codify(attrsList))
                    }
                    else if (attrsList.length === 1) {
                        return codify(attrsList[0])
                    }
                }

                function genStaticId() {
                    return addDoubleQuot("#" + ++$$id)
                }

                function addEventInfo(name, userDefineHandler, modifiers, attrs, token) {
                    var type = name,
                        handler = token.isComponent
                            ? createComponentEventHandler(userDefineHandler, modifiers)
                            : createDOMEventHandler(userDefineHandler, modifiers),
                        eventInfo = {
                            type: addDoubleQuot(type),
                            handler: handler,
                            mode: genHanlderMode(modifiers)
                        }

                    if (!handler) return

                    attrs["@event"] || (attrs["@event"] = [])
                    attrs["@event"].push(eventInfo)

                    function createDOMEventHandler(userDefineHandler, modifiers) {
                        var handler = userDefineHandler || "",
                            isInlineHandler = isInline(handler),
                            modifierCode = ""

                        if (modifiers) {
                            modifierCode = modifiers.reduce(function (modifierCode, modifier) {
                                switch (modifier) {
                                    case "stop":
                                        return modifierCode += "$event.stopPropagation();"
                                    case "stop-imd":
                                        return modifierCode += "$event.stopImmediatePropagation();"
                                    case "prevent":
                                        return modifierCode += "$event.preventDefault();"
                                    case "self":
                                        return modifierCode += "if($event.rawEvent.target !== $event.target)return;"
                                    case "once":
                                        var once_id = modifiers.once = genStaticId()
                                        return modifierCode += "if(" + callMethod("__once__", once_id) + ")return;"
                                    default:
                                        return modifierCode
                                }
                            }, "")
                        }

                        if (isInlineHandler) {
                            var arrowHandler = compileArrowFunction(handler)

                            if (arrowHandler) {
                                handler = arrowHandler + "($event)"
                            }
                        }

                        if (modifierCode) {
                            !isInlineHandler && (handler += "($event)", isInlineHandler = true)
                            handler = modifierCode + handler
                        }

                        if (!handler)
                            throwError('??????????????????????????????????????????????????????')

                        return isInlineHandler
                            ? createFunction("", "$event", handler)
                            : handler
                    }

                    function createComponentEventHandler(userDefineHandler, modifiers) {
                        var handler = userDefineHandler || "",
                            isInlineHandler = isInline(handler),
                            modifierCode = ""

                        if (modifiers && modifiers.once) {
                            var once_id = modifiers.once = genStaticId()
                            modifierCode = "if(" + callMethod("__once__", once_id) + ")return;"
                        }

                        if (isInlineHandler) {
                            var arrowHandler = compileArrowFunction(handler)

                            if (arrowHandler) {
                                handler = arrowHandler + ".apply(null,$args)"
                            }
                        }

                        if (modifierCode) {
                            !isInlineHandler && (handler += ".apply(null, $args)", isInlineHandler = true)
                            handler = modifierCode + handler
                        }

                        if (!handler)
                            throwError('??????????????????????????????????????????????????????')

                        return isInlineHandler
                            ? createFunction("", "", "var $args = Array.prototype.slice.call(arguments);" + handler)
                            : handler
                    }

                    function genHanlderMode(modifiers) {
                        if (!modifiers) return null

                        var mode = token.isComponent
                            ? JSON.stringify({
                                once: modifiers.once
                            })
                            : JSON.stringify({
                                capture: modifiers.capture,
                                passive: modifiers.passive && !modifiers.prevent,
                                ignoreIME: modifiers.ime,
                                once: modifiers.once
                            })

                        return mode === "{}" ? null : mode
                    }

                    function isInline(handler) {
                        var found = isFunction(instance.methods[handler])
                        return !found
                    }

                    function compileArrowFunction(handler) {
                        if (!~handler.indexOf("=>")) return

                        var matcher = handler.match(Reg$ArrowFunction)

                        if (!matcher) return

                        /**
                         * ??? IE ????????????????????????????????????
                         */
                        if (!isIE && !isFunction(eval(handler))) {
                            throwError("??????????????????????????????" + handler)
                        }

                        var argList = matcher[1] || matcher[2],
                            body = matcher[3] || "return " + (matcher[4] || matcher[5]),
                            functionCode = "(" + createFunction("", argList, body) + ")"

                        return functionCode
                    }
                }

                function callMethod(methodName) {
                    var args = slice(arguments, 1),
                        methodArgs = []

                    for (var i = 0, len = args.length; i < len; i++) {
                        var arg = args[i]

                        if (arg || i < len - 1) {
                            methodArgs.push(arg || "void 0")
                        }
                    }

                    return methodName + "(" + methodArgs.join(",") + ")"
                }

                function createFunction(name, args, body) {
                    var argList = isArray(args) ? args.filter(isDef).join(",") : (args || "")

                    name && (name = " " + name)

                    return "function" + name + "(" + argList + "){" + body + "}"
                }

                function addDoubleQuot(text) {
                    text = String(text)
                    return '"' + (text ? text.replace(/"/g, '\\"') : "") + '"'
                }

                function codify(target) {
                    if (isArray(target)) {
                        return "[" + target.filter(isDef).map(function (item) {
                            return codify(item)
                        }).join(",") + "]"
                    }
                    else if (isPlainObject(target)) {
                        var arr = []

                        for (var key in target) {
                            arr.push(addDoubleQuot(key) + ":" + codify(target[key]))
                        }

                        return "{" + arr.join(",") + "}"
                    }

                    return String(target)
                }

                function ensureText(parts) {
                    parts.forEach(function (part) {
                        if (part.type === "expr") {
                            part.content = callMethod("__text__", part.content)
                        }
                    })

                    return parts
                }

                function joinMixedContentParts(parts) {
                    return joinExpression.apply(null, parts.map(function (part) {
                        return part.content
                    }))
                }

                function joinExpression() {
                    var args = slice(arguments)

                    return args.reduce(function (argA, argB) {
                        if (argA[argA.length - 1] === '"' && argB[0] === '"') {
                            return argA.substr(0, argA.length - 1) + argB.substr(1)
                        } else {
                            return argA + "+" + argB
                        }
                    })
                }

                function splitMixedContent(mixedContent) {
                    var parts = [],
                        text = "",
                        matcher

                    while (matcher = Reg$MixedContent.exec(mixedContent)) {
                        var _text = matcher[1] || matcher[3],
                            expression = matcher[2]

                        if (expression) {
                            text && (parts.push({ type: "string", content: addDoubleQuot(text) }), text = "")

                            depCollector.collect(expression)
                            parts.push({ type: "expr", content: Reg$TestKeyPath.test(expression) ? expression : "(" + expression + ")" })
                        }
                        else {
                            text += _text
                        }
                    }

                    if (text) {
                        parts.push({ type: "string", content: addDoubleQuot(text) })
                    }

                    return parts
                }

                function checkBranchDirective(token) {
                    var directives = token.directives,
                        hasIf = directives.hasOwnProperty("if"),
                        hasElseIf = directives.hasOwnProperty("else-if"),
                        hasELse = directives.hasOwnProperty("else"),
                        isBranch = hasIf + hasElseIf + hasELse

                    if (isBranch > 1) {
                        throwError("if/else-if/else ???????????????????????????????????????")
                    }
                }

                function findIf(token) {
                    var prevToken = token.prev

                    while (prevToken) {
                        var directives = prevToken.directives

                        if (
                            prevToken.type !== 'tag' ||
                            (!directives.hasOwnProperty("if") && !directives.hasOwnProperty("else-if"))
                        ) {
                            throwError("?????? else-if/else ??????????????????????????????????????? if/else-if ??????")
                        }

                        if (directives.hasOwnProperty("else")) {
                            throwError("?????? else-if/else ???????????????????????? else ??????")
                        }

                        if (directives.hasOwnProperty("if")) {
                            return prevToken
                        }

                        prevToken = prevToken.prev
                    }

                    throwError("?????? else-if/else ??????????????????????????? if ??????")
                }

                function throwError() {
                    throw instance._logError.apply(instance, arguments)
                }
            },
            _createRenderHelper: function () {
                var instance = this

                bindContext = normailzeSurrogate(bindContext)

                return {// ??????????????????????????????????????????
                    "$model": {
                        input: function (e, path) {
                            if (!path) return

                            var context = instance.context || instance.dataContext,
                                value = e.target.value

                            context.$setData(path, value)
                        },
                        checkbox: function (e, path) {
                            if (!path) return

                            var context = instance.context || instance.dataContext,
                                checkbox = e.target,
                                isChecked = Boolean(checkbox.checked),
                                checkboxData = readData(context, path),
                                value

                            if (isArray(checkboxData)) {
                                var val = checkbox._value

                                val = (val === "on" || isUndef(val)) ? null : val

                                if (isChecked) {
                                    checkboxData = checkboxData.concat(val)
                                }
                                else {
                                    checkboxData = checkboxData.filter(function (_val) {
                                        return _val !== val
                                    })
                                }

                                value = checkboxData
                            }
                            else {
                                value = isChecked
                                    ? checkbox.hasOwnProperty("true-value") ? checkbox["true-value"] : true
                                    : checkbox.hasOwnProperty("false-value") ? checkbox["false-value"] : false
                            }

                            context.$setData(path, value)
                        },
                        radio: function (e, path) {
                            if (!path) return

                            var context = instance.context || instance.dataContext,
                                value = e.target._value

                            value = (value === "on" || isUndef(value)) ? null : value

                            context.$setData(path, value)
                        },
                        select: function (e, path) {
                            if (!path) return

                            var context = instance.context || instance.dataContext,
                                select = e.target,
                                isMultiple = select.multiple,
                                value

                            if (isMultiple) {
                                var options = select.options

                                value = []

                                for (var i = 0, len = options.length; i < len; i++) {
                                    var option = options[i]

                                    if (!option.disabled && option.selected) {
                                        value.push(findOptionValue(option))
                                    }
                                }
                            }
                            else {
                                var option = select.options[select.selectedIndex]
                                value = findOptionValue(option)
                            }

                            context.$setData(path, value)

                            function findOptionValue(option) {
                                return "_value" in option ? option._value : option.innerText
                            }
                        },
                        component: function (path, value) {
                            if (!path) return

                            var context = instance.context || instance.dataContext

                            context.$setData(path, value)
                        }
                    },
                    "$bind": {
                        input: function (vdom, value) {
                            if (isUndef(value)) value = "";

                            vdom.setElementProperty("value", value)

                            return vdom
                        },
                        checkbox: function (vdom, value) {
                            if (isArray(value)) {
                                var value$ = vdom.getAttribute("value")

                                value$ = nvl(value$, null)
                                vdom.setElementProperty("checked", Boolean(~value.indexOf(value$)))
                            }
                            else {
                                var trueValue = true,
                                    falseValue = false

                                if (vdom.hasAttribute("true-value")) {
                                    trueValue = vdom.getAttribute("true-value")
                                    vdom.setElementProperty("true-value", trueValue)
                                }

                                if (vdom.hasAttribute("false-value")) {
                                    falseValue = vdom.getAttribute("false-value")
                                    vdom.setElementProperty("false-value", falseValue)
                                }

                                vdom.setElementProperty("checked", trueValue === true ? Boolean(value) : trueValue === value)
                            }

                            return vdom
                        },
                        radio: function (vdom, value) {
                            var value$ = vdom.getAttribute("value")

                            value$ = nvl(value$, null)
                            vdom.setElementProperty("checked", value === value$)

                            return vdom
                        },
                        select: function (vdom, value) {
                            var isMultiple = isDef(vdom.getAttribute("multiple")),
                                options = vdom.children,
                                found = isMultiple

                            if (isMultiple && !isArray(value)) {
                                vdom.setElementProperty("value", Undefined)
                                instance._logWarning("select ??????????????????????????????")

                                return vdom
                            }

                            for (var i = 0, len = options.length; i < len; i++) {
                                var option = options[i],
                                    optionValue = option.getAttribute("value")

                                isUndef(optionValue) && (optionValue = findInnerText(option))

                                if (isMultiple) {
                                    option.setElementProperty("selected", Boolean(~value.indexOf(optionValue)))
                                }
                                else if (optionValue === value) {
                                    found = true
                                    vdom.setElementProperty("selectedIndex", i)
                                    break;
                                }
                            }

                            if (!found) {
                                vdom.setElementProperty("selectedIndex", -1)
                            }

                            return vdom

                            function findInnerText(option) {
                                var text = ""

                                traveres(option, {
                                    onWalkDown: function (vdom, i, parent) {
                                        if (!parent || !vdom.isText) return

                                        text += vdom.text
                                    }
                                })

                                return text
                            }
                        }
                    },
                    "__output__": function (children) {
                        var vdom = VirtualDOM.createFragment(children)

                        return vdom
                    },
                    "__createComponent__": function (tagName, data, children) {
                        var component = instance.getComponent(tagName)

                        if (!component) return instance._logError("??????????????????" + tagName + "???")

                        data = normalizeData(data)

                        var _currentInstance = currentInstance,
                            updateId = _currentInstance.updateId,
                            once = false,
                            componentData = {
                                name: tagName,
                                props: data.props,
                                events: data.events,
                                children: children.filter(isDef),
                                parentContext: _currentInstance.context,
                                vdom: null,
                                domEventManager: instance.domEventManager,
                                complete: complete,
                                store: instance.store
                                    ? instance.store.getRaw()
                                    : instance.componentData && instance.componentData.store
                            },
                            vdom = componentData.vdom = VirtualDOM.createComponent(tagName, component, componentData, data.key)

                        if (componentData.children) {
                            componentData.children.forEach(function (child) {
                                child.render = bindContext(child.render)
                            })
                        }

                        instance._emitHook("create-vdom", vdom)

                        return vdom

                        function complete() {
                            if (once) return
                            once = true
                            componentData.complete = noop

                            if (updateId !== _currentInstance.updateId) return

                            if (_currentInstance.state.patching) return

                            _currentInstance._doneAsyncComponent(vdom)
                            _currentInstance = null
                        }
                    },
                    "__createElement__": function (tagName, data, children) {
                        data = normalizeData(data)

                        var attrs = data.props,
                            props = {},
                            vdom = VirtualDOM.createElement(tagName, attrs, props, children, data.key)

                        if (attrs.hasOwnProperty("value")) {
                            props._value = attrs.value
                        }

                        if (data.events) {
                            vdom.events = data.events
                            vdom.domEventManager = instance.domEventManager
                        }

                        instance._emitHook("create-vdom", vdom)

                        return vdom
                    },
                    "__createFragment__": function (data, children) {
                        data = normalizeData(data)

                        return VirtualDOM.createFragment(children, data.key)
                    },
                    "__createSlot__": function (slotName, data, children) {
                        data = normalizeData(data)

                        var slotCaches = instance.slotCaches,
                            slotCache = slotCaches && slotCaches[slotName],
                            componentSlotChildren = instance.componentChildren && instance.componentChildren[slotName],
                            hasComponentChildren = componentSlotChildren && componentSlotChildren.length,
                            useSlotProps = hasComponentChildren && componentSlotChildren.some(function (child) { return child.slotScope }),
                            slotProps = data.props,
                            slotVdoms = null

                        /**
                         * ???????????????/?????????,??????????????????/???????????????:
                         * !slotCache ???????????????,???????????????????????????????????????
                         * !hasComponentChildren ????????????????????? children ??????,children ????????????,??????????????????
                         * useSlotProps ??????componentChildren?????????????????????,??????????????????
                         */
                        if (
                            !slotCache ||
                            !hasComponentChildren ||
                            useSlotProps
                        ) {
                            if (hasComponentChildren) {
                                slotVdoms = []

                                try {
                                    for (var i = 0, len = componentSlotChildren.length; i < len; i++) {
                                        var child = componentSlotChildren[i],
                                            slotScope = child.slotScope,
                                            childVdoms = null

                                        childVdoms = slotScope
                                            ? child.render.apply(null, slotScope.map(function (key) { return slotProps[key] }))
                                            : child.render()

                                        if (childVdoms) slotVdoms.push(childVdoms)
                                    }
                                } catch (e) {
                                    instance._logError([
                                        "?????????????????????",
                                        ["???????????????", e],
                                        ["???????????? - ???" + (i + 1) + "??????????????????", getRawFn(componentSlotChildren[i])]
                                    ])
                                }
                            }
                            else {
                                slotVdoms = children
                            }

                            slotVdoms = slotVdoms.length
                                ? processChildren(slotVdoms)
                                : [VirtualDOM.createComment("slot")]

                            slotCache = {
                                vdoms: slotVdoms
                            }

                            instance.slotCaches || (instance.slotCaches = {})
                            instance.slotCaches[slotName] = slotCache
                        }
                        else {
                            slotVdoms = slotCache.vdoms
                        }

                        return VirtualDOM.createFragment(slotVdoms)
                    },
                    "__setTransition__": function (data, children) {
                        data = normalizeData(data)

                        var vdom = VirtualDOM.createFragment(children, data.key)

                        if (!vdom) return

                        var transition = vdom.transition = createTransition(data, instance)

                        addMeta(vdom, "transition", transition)

                        VirtualDOM.eachRealChild(vdom.children, function (child) {
                            var key = child.key

                            if (key) {
                                child.isComponent && addMeta(child, "transitionKey", key)
                            }
                            else {
                                instance._logWarning("transition ?????????????????? key")
                            }
                        })

                        return vdom
                    },
                    "__createComment__": function (textContent) {
                        textContent = String(textContent)

                        var vdom = VirtualDOM.createComment(textContent)

                        return vdom
                    },
                    "__createText__": function (textContent) {
                        textContent = String(textContent)

                        var vdom = VirtualDOM.createText(textContent)

                        return vdom
                    },
                    "__createHTML__": function (htmlContent) {
                        /**
                         * ??? html ???????????????????????????????????????
                         */
                        var wrapper = document.createElement("div")
                        wrapper.innerHTML = htmlContent
                        htmlContent = wrapper.innerHTML

                        var root = parseTemplate(htmlContent),
                            vdoms = toVdom(root.children)

                        return VirtualDOM.createFragment(vdoms)

                        function toVdom(tokens) {
                            return tokens.map(function (token) {
                                if (token.type === "tag") {
                                    var data = token.attrs && token.attrs.reduce(function (data, attr) {
                                        data[attr.name] = attr.value
                                        return data
                                    }, {})

                                    data = normalizeData(data)

                                    return VirtualDOM.createElement(token.tagName.toLowerCase(), data.props, {}, toVdom(token.children))
                                }
                                else if (token.type === "text") {
                                    return VirtualDOM.createText(token.textContent)
                                }
                            })
                        }
                    },
                    "__show__": function (vdom, expressionValue) {
                        addMeta(vdom, "show", Boolean(expressionValue))

                        return vdom
                    },
                    "__renderList__": function (source, iterator, expression, valueAlias, indexAlias, objectIndexAlias) {
                        if (isUndef(source)) return []

                        var context = instance.context,
                            pathInfo = context && context.__$pathInfo__,
                            vdomList = [],
                            shouldMarkPathInfo = false

                        var forEach = 0
                            || isPlainObject(source) && source.hasOwnProperty("from") && source.hasOwnProperty("to") && (shouldMarkPathInfo = true, iterRange)
                            || isPlainObject(source) && iterObject
                            || (isArray(source) || isString(source)) && (shouldMarkPathInfo = true, iterArray)
                            || isInteger(source) && iterNumber
                            || Undefined

                        if (isUndef(forEach)) {
                            throw instance._logError(["for ???????????????????????????????????????????????????", ["????????????", source]])
                        }

                        forEach(source, function (value, index, objIndex) {
                            var itemContext = instance.context = instance._createContext(context)

                            itemContext[valueAlias] = value
                            indexAlias && (itemContext[indexAlias] = index)
                            objectIndexAlias && (itemContext[objectIndexAlias] = objIndex)

                            if (shouldMarkPathInfo) {
                                var itemPathInfo = pathInfo ? clone(pathInfo) : {}

                                itemPathInfo[valueAlias] = expression + "[" + (isNaN(index) ? '"' + index + '"' : index) + "]"
                                indexAlias && (itemPathInfo[indexAlias] = index)
                                objectIndexAlias && (itemPathInfo[objectIndexAlias] = objIndex)
                                itemContext.__$pathInfo__ = itemPathInfo
                            }

                            var vdom = iterator.call(itemContext, value, index, objIndex)

                            if (isUndef(vdom)) return

                            push(vdomList, vdom)
                        })

                        instance.context = context

                        return vdomList

                        function iterObject(obj, fn) {
                            var objIndex = -1

                            for (var key in obj) {
                                if (obj.hasOwnProperty(key)) {
                                    fn(obj[key], key, ++objIndex)
                                }
                            }
                        }

                        function iterArray(arr, fn) {
                            for (var i = 0, len = arr.length; i < len; i++) {
                                fn(arr[i], i)
                            }
                        }

                        function iterNumber(number, fn) {
                            for (var i = 0; i < number; i++) {
                                fn(i + 1, i)
                            }
                        }

                        function iterRange(range, fn) {
                            var from = range.from,
                                to = range.to,
                                diff = to - from + 1

                            for (var i = 0; i < diff; i++) {
                                fn(i + from, i)
                            }
                        }
                    },
                    "__saveRef__": function saveRef(refName, isArrayRef, vdom) {
                        if (isUndef(vdom)) return

                        vdom.refName = refName
                        vdom.isArrayRef = isArrayRef

                        var vdomRefList = instance.vdomRefList || (instance.vdomRefList = [])
                        vdomRefList.push(vdom)

                        return vdom
                    },
                    "__class__": function (_class) {
                        return classStringify(_class)
                    },
                    "__style__": function (style) {
                        return styleStringify(style)
                    },
                    "__text__": function (value) {
                        if (isUndef(value)) return ""

                        if (isPlainObject(value) || isArray(value)) {
                            return JSON.stringify(value)
                        }

                        return String(value)
                    },
                    "__mergeAttrs__": function (attrsList) {
                        var merged = attrsList.reduce(function (merged, attrs) {
                            if (!attrs) return merged

                            for (var key in attrs) {
                                if (key === "@event") {
                                    merged["@event"] || (merged["@event"] = [])
                                    push(merged["@event"], attrs["@event"])
                                }
                                else if ((key === "style" || key === "class") && merged[key]) {
                                    merged[key] = mergeClassOrStyle(key, merged[key], attrs[key])
                                }
                                else {
                                    merged[key] = attrs[key]
                                }
                            }

                            return merged
                        }, {})

                        return merged
                    },
                    "__inheritAttrs__": function () {
                        return instance.state.inheritAttrs ? instance.componentAttrs : null
                    },
                    "__once__": function (once_id, onceCallback) {
                        var onceCache = instance.onceCache || (instance.onceCache = {})

                        if (onceCache.hasOwnProperty(once_id)) {
                            return onceCache[once_id]
                        }

                        if (isFunction(onceCallback)) {
                            return onceCache[once_id] = onceCallback()
                        }

                        onceCache[once_id] = true
                        return false
                    }
                }

                function normalizeData(data) {
                    var normalData = { props: {}, events: null, key: Undefined }

                    for (var key in data) {
                        if (!data.hasOwnProperty(key)) continue

                        var val = data[key]

                        if (key === "key") {
                            normalData.key = val
                        }
                        else if (key === "@event") {
                            var eventInfos = val,
                                eventInfos$ = []

                            for (var i = 0, len = eventInfos.length; i < len; i++) {
                                var eventInfo = eventInfos[i],
                                    once = eventInfo.mode && eventInfo.mode.once

                                if (once && instance.onceCache[once]) {
                                    continue
                                }

                                eventInfo.handler = bindContext(eventInfo.handler)

                                eventInfos$.push(eventInfo)
                            }

                            normalData.events = eventInfos$
                        }
                        else {
                            if (isFunction(val)) {
                                val = bindContext(val)
                            }

                            normalData.props[key] = val
                        }
                    }

                    return normalData
                }

                function processChildren(children) {
                    var children$ = []

                    if (!children.length) return children$

                    for (var i = 0, len = children.length; i < len; i++) {
                        var child = children[i]

                        if (isArray(child)) {
                            push(children$, processChildren(child))
                        }
                        else if (isFunction(child)) {
                            children[i] = child()
                            i--
                        }
                        else if (child) {
                            children$.push(child)
                        }
                    }

                    return children$
                }

                /**
                * ???????????????????????????????????????
                */
                function bindContext(fn) {
                    var closureContext = instance.context

                    return function () {
                        var currentContext = instance.context

                        instance.context = closureContext

                        var result = fn.apply(closureContext, arguments)

                        instance.context = currentContext

                        return result
                    }
                }
                // function bindContext(fn) {
                //     if (fn.__bindContextRaw__) {
                //         fn = fn.__bindContextRaw__
                //     }

                //     var rawFn = fn.__raw__ || fn

                //     var closureContext = instance.context,
                //         fnWithContext = function () {
                //             var currentContext = instance.context

                //             instance.context = closureContext

                //             var result = fn.apply(closureContext, arguments)

                //             instance.context = currentContext

                //             return result
                //         }

                //     fnWithContext._length = rawFn.length
                //     fnWithContext.__raw__ = rawFn
                //     fnWithContext.__bindContextRaw__ = fn

                //     return fnWithContext
                // }
            },
            _createContext: function () {
                var args = slice(arguments)

                args.unshift(new this.Context())

                return Object.assign.apply(Object, args)
            },
            _toAbsolutePath: function () {
                var pathSplitReg = /^([\w$]+)(.*)$/

                return function (path, pathInfo) {
                    pathInfo || (pathInfo = this.context && this.context.__$pathInfo__)

                    if (!pathInfo) return path

                    var pathCache = this.shortCache.get(pathInfo),
                        absolutePath = pathCache && pathCache[path]

                    if (absolutePath) return absolutePath

                    var matcher, prefix = "", suffix = ""

                    do {
                        matcher = path.match(pathSplitReg)
                        prefix = matcher[1]
                        suffix = (matcher[2] || "") + suffix
                    } while (path = pathInfo[prefix])

                    absolutePath = prefix + suffix

                    pathCache || (pathCache = {})
                    pathCache[path] = absolutePath
                    this.shortCache.set(pathInfo, pathCache)

                    return absolutePath
                }
            }(),
            _on: function (hook, handler) {
                this.runtimeHooks || (this.runtimeHooks = {})

                var handlers = this.runtimeHooks[hook] || (this.runtimeHooks[hook] = [])

                handlers.push(handler)
            },
            _emitHook: function (hook) {
                var handlers = this.runtimeHooks && this.runtimeHooks[hook],
                    args = null

                if (handlers) {
                    args = slice(arguments, 1)

                    for (var i = 0, len = handlers.length; i < len; i++) {
                        var handler = handlers[i]

                        handler.apply(this.dataContext, args)
                    }
                }

                var hookEventNm = hookName(hook)

                if (isHookEvent(hookEventNm)) {
                    this._emit.apply(this, [hookEventNm].concat(args || slice(arguments, 1)))
                }
            },
            _emit: function (eventType) {
                var args = slice(arguments, 1),
                    invoker = this.componentEvents && this.componentEvents[eventType],
                    emitsValidator = this.emitsConfig && this.emitsConfig[eventType]

                if (!invoker) return

                if (isFunction(emitsValidator) && !emitsValidator.apply(null, args)) {
                    this._logWarning(["?????????" + eventType + "????????????????????????", ["?????????", args]])
                    return
                }

                invoker.apply(null, args)
            },
            _installComponentChildren: function (contextChildren) {
                if (!isArray(contextChildren)) return

                var componentChildren = {}

                for (var i = 0, len = contextChildren.length; i < len; i++) {
                    var child = contextChildren[i]
                    componentChildren[child.slotName] || (componentChildren[child.slotName] = [])
                    componentChildren[child.slotName].push(child)
                }

                this.componentChildren = componentChildren
            },
            _installComponentEvents: function (contextEventInfos) {
                var eventMap = this._createEventMap(contextEventInfos)

                this.componentEvents = isNotEmptyObject(eventMap) ? eventMap : null
            },
            _installComponentProps: function (contextProps) {
                var propsConfig = this.propsConfig

                if (!propsConfig) return

                contextProps = contextProps || {}

                var props = {}

                for (var propName in propsConfig) {
                    var propVal = contextProps[propName],
                        propConfig = propsConfig[propName],
                        isValid = true,
                        type = propConfig.type,
                        required = propConfig.required,
                        validator = propConfig.validator,
                        defaultVal = propConfig["default"]

                    if (isDef(defaultVal) && isUndef(propVal)) {
                        propVal = isFunction(defaultVal) ? defaultVal() : defaultVal
                    }

                    if (required) {
                        isValid = isDef(propVal)

                        if (!isValid) {
                            this._logError("???" + propName + "?????????????????? prop")
                            continue
                        }
                    }

                    if (isFunction(validator)) {
                        isValid = validator(propVal)

                        if (!isValid) {
                            this._logWarning(["???" + propName + "???prop ?????????????????????", ["??????????????????", propVal]])
                            continue
                        }
                    }

                    if (isDef(propVal) && type) {
                        var baseTypes = isArray(type) ? type : [type]

                        isValid = baseTypes.some(function (baseType) {
                            return propVal.constructor === baseType
                        })

                        if (!isValid) {
                            var notMatchType = baseTypes.map(function (baseType) {
                                return baseType.name || (baseType + "").match(/function\s*([^\(]+)/)[1]
                            }).join(",")

                            this._logWarning(["???" + propName + "???prop ???????????????" + notMatchType + "?????????", ["??????????????????", propVal]])
                            continue
                        }
                    }

                    props[propName] = isValid ? propVal : Undefined
                }

                this.props = props
            },
            _installComponentAttributes: function (contextProps, contextEventInfos) {
                if (!contextProps && !contextEventInfos) return

                var componentAttrs = {},
                    propsConfig = this.propsConfig,
                    emitsConfig = this.emitsConfig

                if (contextProps) {
                    for (var name in contextProps) {
                        if (!contextProps.hasOwnProperty(name) || propsConfig && propsConfig[name]) continue

                        componentAttrs[name] = contextProps[name]
                    }
                }

                if (contextEventInfos) {
                    for (var i = 0, len = contextEventInfos.length; i < len; i++) {
                        var eventInfo = contextEventInfos[i],
                            type = eventInfo.type

                        if (
                            isHookEvent(type) ||
                            emitsConfig && emitsConfig.hasOwnProperty(type)
                        ) continue

                        componentAttrs["@event"] || (componentAttrs["@event"] = [])
                        componentAttrs["@event"].push(eventInfo)
                    }
                }

                this.rootContext.$attrs = componentAttrs
                this.componentAttrs = isNotEmptyObject(componentAttrs) ? componentAttrs : null
            },
            _setDirty: function (dirtyType) {
                var state = this.state

                if (dirtyType) {
                    state.dirty || (state.dirty = {})
                    state.dirty[dirtyType] = true

                    if (~"slots,init,attrs".indexOf(dirtyType)) {
                        state.shouldTemplateReRender = true
                    }
                }
                else {
                    state.dirty = false
                }
            },
            _syncComponentMeta: function (vdom) {
                if (vdom && this.componentData) {
                    var $vdom = this.componentData.vdom

                    if ($vdom.meta) {
                        addMeta(vdom, $vdom.meta)
                    }
                }
            },
            _createEventMap: function (events) {
                var eventMap = {}

                if (!isArray(events)) return eventMap

                for (var i = 0, len = events.length; i < len; i++) {
                    var eventInfo = events[i],
                        type = eventInfo.type,
                        invoker = eventMap[type] || (eventMap[type] = createInvoker())

                    invoker.add(eventInfo.handler)
                }

                return eventMap
            },
            _startUpdate: function (immediate) {
                var state = this.state

                if (state.destroy) return

                if (immediate) {
                    if (!this.el) throw this._logError("????????????????????????????????????")

                    state.updateLock = true

                    this._emitHook(this.state.mounted ? "beforeUpdate" : "beforeMount")

                    this._doUpdate()
                }
                else if (!state.updateLock) {
                    if (!this.el) return

                    var instance = this,
                        updateLock = state.updateLock = Promise.resolve().then(function () {
                            if (state.destroy || updateLock !== state.updateLock) return

                            instance._doUpdate()
                        })

                    this._emitHook(this.state.mounted ? "beforeUpdate" : "beforeMount")
                }
            },
            _doUpdate: function () {
                this.updateId = ++$$id

                var state = this.state

                if (!state.dirty) return state.updateLock = null

                this.watcher.run()

                state.updateLock = null

                if (!state.shouldTemplateReRender) {
                    this._setDirty(false)
                    return
                }

                state.shouldTemplateReRender = false
                this._setDirty(false)

                delete this.vdomRefList

                var restoreCurrentInstance = setCurentInstance(this),
                    context = this.context = this._createContext(),
                    oldVdom = this.vdom,
                    newVdom = this.renderVdom(context)

                this._syncComponentMeta(newVdom)

                if (state.shouldTemplateReRender) {
                    this._logWarning("??????????????????????????????????????????????????????")
                }

                this.context = null
                this.vdom = newVdom

                this._emitHook("beforePatch", oldVdom, newVdom)

                this._patch(oldVdom, newVdom)

                restoreCurrentInstance()

                this._doneUpdate()
            },
            _patch: function (oldVdom, newVdom) {
                if (oldVdom) this.refNode = null // ???????????????????????? oldVdom ??????

                this.state.patching = true
                VirtualDOM.patch(this.el, oldVdom, newVdom, this.refNode)
                this.state.patching = false
            },
            _rootElements: function () {
                var $elements = this.rootContext.$elements,
                    elements = []

                VirtualDOM.eachElement(this.vdom, function (element) {
                    elements.push(element)
                })

                $elements.length = 0
                push($elements, elements)

                return elements
            },
            _doneUpdate: function () {
                clearKeys(this.rootContext.$refs)
                this._collectRefs()

                if (isFunction(this.componentCallback)) {
                    this.componentCallback()
                }

                var instance = this

                patchCallbacks.push(function componentUpdated() {
                    var hook = instance.state.mounted
                        ? "updated"
                        : (instance.state.mounted = true, "mounted")

                    instance._emitHook(hook, instance._rootElements())
                })

                if (isUndef(currentInstance)) {
                    for (var i = 0, len = patchCallbacks.length; i < len; i++) {
                        if (isFunction(patchCallbacks[i])) {
                            patchCallbacks[i]()
                        }
                    }

                    patchCallbacks.length = 0
                }
            },
            _doneAsyncComponent: function (vdom) {
                vdom.refName && this._collectRefs()
                this._emitHook("updated", this._rootElements())
            },
            _collectRefs: function () {
                var $refs = this.rootContext.$refs,
                    vdomRefList = this.vdomRefList

                if (!vdomRefList || !vdomRefList.length) return delete this.vdomRefList

                var notFoundList = []

                for (var i = 0, len = vdomRefList.length; i < len; i++) {
                    var vdom = vdomRefList[i],
                        ref = getRef(vdom)

                    if (isUndef(ref)) {
                        notFoundList.push(vdom)
                        continue
                    }

                    var isArrayRef = vdom.isArrayRef,
                        refName = vdom.refName,
                        collectedRef = $refs[refName]

                    if (collectedRef) {
                        isArrayRef && isArray(collectedRef) ? collectedRef.push(ref) : this._logWarning("????????? ref???" + refName + "???")
                    }
                    else if (isArrayRef) {
                        $refs[refName] = [ref]
                    }
                    else {
                        $refs[refName] = ref
                    }
                }

                this.vdomRefList = notFoundList.length ? notFoundList : null

                function getRef(vdom) {
                    if (vdom.isComponent) {
                        var i
                        return isDef(i = vdom.component) && isDef(i = i.instance) && i.dataContext || null
                    }
                    else if (vdom.isFragment) {
                        return null
                    }
                    else {
                        return vdom.element
                    }
                }
            },
            _logError: function (messages, loc) {
                var head = this._genConsoleHead(),
                    loc$ = loc || LOC

                if (loc$) {
                    messages = [].concat(messages, "???????????????\n" + markTemplate(this.template, loc$))
                }

                genConsole().head(head).stdout(console.error).printLines(messages)
            },
            _logWarning: function (messages, loc) {
                var head = this._genConsoleHead(),
                    loc$ = loc || LOC

                if (loc$) {
                    messages = [].concat(messages, "???????????????\n" + markTemplate(this.template, loc$))
                }

                genConsole().head(head).stdout(console.warn).printLines(messages)
            },
            _genConsoleHead: function () {
                var id = this.state.isRoot ? "" : "(" + this.id + ")",
                    names = [this.name],
                    parentContext = this.rootContext.$parent

                while (parentContext) {
                    names.push(parentContext.__instance__.name)
                    parentContext = parentContext.$parent
                }

                var head = names.reverse().join("->") + id + ":"

                return head
            }
        }

        var vdomHooks = {
            "event": {
                create: function (vdom) {
                    if (vdom.events) {
                        vdom.domEventManager.set(vdom.element, vdom.events)
                    }
                },
                update: function (vdom) {
                    if (vdom.events) {
                        vdom.domEventManager.set(vdom.element, vdom.events)
                    }
                },
                remove: function (vdom, rm) {
                    if (vdom.events) {
                        vdom.domEventManager.remove(vdom.element)
                    }
                    rm()
                }
            },
            "show": {
                create: function (vdom) {
                    if (!hasMeta(vdom, "show")) return

                    display(vdom.element, vdom.meta.show)
                },
                update: function (vdom, oldVdom) {
                    if (hasMeta(vdom, "show")) {
                        var show = vdom.meta.show,
                            element = vdom.element,
                            curShow = hasMeta(oldVdom, "show") ? oldVdom.meta.show : true

                        if (show === curShow) return

                        if (hasMeta(vdom, "transition")) {
                            if (show) {
                                transitionEnter(vdom, function showElement() {
                                    display(element, true)
                                })
                            }
                            else {
                                transitionLeave(vdom, function hideElement() {
                                    display(element, false)
                                })
                            }
                        }
                        else {
                            display(element, show)
                        }
                    }
                    else if (hasMeta(oldVdom, "show") && !oldVdom.meta.show) {
                        display(vdom.element, true)
                    }
                }
            },
            "transition": {
                create: function (vdom) {
                    if (!hasMeta(vdom, "transition") || vdom.meta.show === false) return
                    transitionEnter(vdom)
                },
                remove: function (vdom, rm) {
                    if (hasMeta(vdom, "transition") && vdom.meta.show !== false) {
                        return transitionLeave(vdom, rm)
                    }
                    else if (vdom.transition) {
                        updateTransitionFragment(null, vdom)
                    }

                    rm()
                },
                update: function (vdom, oldVdom) {
                    if (vdom.transition && oldVdom.transition) {
                        updateTransitionFragment(vdom, oldVdom)
                    }
                }
            },
            "privateStyle": {
                create: function (vdom) {
                    if (!hasMeta(vdom, "private-style")) return

                    each(vdom.meta["private-style"], function (id) {
                        vdom.element.setAttribute(id, "")
                    })
                },
                update: function (vdom, oldVdom) {
                    var hasNew = hasMeta(vdom, "private-style"),
                        hasOld = hasMeta(oldVdom, "private-style")

                    if (
                        hasNew &&
                        hasOld &&
                        vdom.meta["private-style"] === oldVdom.meta["private-style"]
                    ) return

                    if (hasOld) {
                        each(oldVdom.meta["private-style"], function (id) {
                            vdom.element.removeAttribute(id)
                        })
                    }

                    if (hasNew) {
                        each(vdom.meta["private-style"], function (id) {
                            vdom.element.setAttribute(id, "")
                        })
                    }
                }
            }
        }

        for (var name in vdomHooks) {
            VirtualDOM.addHook(vdomHooks[name])
        }

        function createTransition(data, instance) {
            var props = data.props,
                eventMap = instance._createEventMap(data.events),
                isAppear = !instance.state.mounted,
                appear = props.appear,
                appearHook = eventMap["appear"],
                allowAppear = (isDef(appear) && appear !== false) || isFunction(appearHook)

            var transition = {
                type: props.type,
                name: props.name || "transition",
                mode: props.mode,
                move: isDef(props.move),
                useCSS: props.css !== false,
                isAppear: isAppear,
                allowAppear: allowAppear,
                props: props,
                eventMap: eventMap,
                lastTransition: null,
                connect: function (lastTransition) {
                    this.lastTransition = lastTransition
                    lastTransition.lastTransition = null
                }
            }

            return transition
        }

        function resolveTransition(transition) {
            if (transition.hooks) return transition

            var props = transition.props,
                eventMap = transition.eventMap,
                type = transition.type,
                name = transition.name,
                mode = transition.mode,
                useCSS = transition.useCSS,
                isAppear = transition.isAppear,

                addTransitionClass = useCSS ? addClass : noop,
                removeTransitionClass = useCSS ? removeClass : noop,

                enterClass = isAppear && props["appear-class"] || props["enter-class"] || name + "-enter",
                enterToClass = isAppear && props["appear-to-class"] || props["enter-to-class"] || name + "-enter-to",
                enterActiveClass = isAppear && props["appear-active-class"] || props["enter-active-class"] || name + "-enter-active",
                leaveClass = props["leave-class"] || name + "-leave",
                leaveToClass = props["leave-to-class"] || name + "-leave-to",
                leaveActiveClass = props["leave-active-class"] || name + "-leave-active",
                moveClass = props["move-class"] || name + "-move",

                enterDuration = parseFloat(isObject(props.duration) ? props.duration.enter : props.duration),
                leaveDuration = parseFloat(isObject(props.duration) ? props.duration.leave : props.duration),

                beforeEnterHook = isAppear && eventMap["before-appear"] || eventMap["before-enter"],
                enterHook = isAppear && eventMap["appear"] || eventMap["enter"],
                afterEnterHook = isAppear && eventMap["after-appear"] || eventMap["after-enter"],
                enterCancelledHook = isAppear && eventMap["appear-cancelled"] || eventMap["enter-cancelled"],
                beforeLeaveHook = eventMap["before-leave"],
                leaveHook = eventMap["leave"],
                afterLeaveHook = eventMap["after-leave"],
                leaveCancelledHook = eventMap["leave-cancelled"],

                endEnterByUser = isFunction(enterHook) && getHookArgsLength(enterHook) > 1,
                endLeaveByUser = isFunction(leaveHook) && getHookArgsLength(leaveHook) > 1,

                enterCSSInfo = null, leaveCSSInfo = null,

                lastTransition = transition.lastTransition,
                modeHandler = createModeHanlder(transition, lastTransition)

            if (modeHandler) {
                /**
                 * ????????? ??????/?????? ????????????out-in/in-out ?????? patch ??????????????? in/out
                 */
                patchCallbacks.push(function modeNotifyIfNoneLeader() {
                    if (!modeHandler) return

                    if (
                        (mode === "in-out" && (!transition.enterRecord || isEmptyObject(transition.enterRecord))) ||
                        (mode === "out-in" && (!transition.leaveRecord || isEmptyObject(transition.leaveRecord)))
                    ) {
                        modeHandler.notify()
                    }
                })

                transition.modeHandler = modeHandler

                modeHandler.addListener(function () {
                    modeHandler = transition.modeHandler = null
                })
            }

            transition.moveClass = moveClass
            transition.enterRecord = lastTransition && isNotEmptyObject(lastTransition.enterRecord) ? lastTransition.enterRecord : null
            transition.leaveRecord = lastTransition && isNotEmptyObject(lastTransition.leaveRecord) ? lastTransition.leaveRecord : null
            transition.props = transition.eventMap = transition.lastTransition = null

            transition.hooks = {
                beforeEnter: function (vdom) {
                    var element = vdom.element

                    if (element._enterCancel) return

                    markEntering(vdom)

                    callHook(beforeEnterHook, [element])

                    addTransitionClass(element, enterClass)
                    addTransitionClass(element, enterActiveClass)
                },
                onEnter: function (vdom, endEnter) {
                    endStaleLeaving(vdom)

                    var element = vdom.element

                    if (element._enterCancel) return

                    if (endEnterByUser) {
                        var done = endEnter.bind(null, false),
                            cancel = endEnter.bind(null, true)

                        callHook(enterHook, [element, done, cancel])
                    }
                    else {
                        callHook(enterHook, [element])
                    }

                    if (useCSS) {
                        nextFrame(function () {
                            removeTransitionClass(element, enterClass)

                            if (element._enterCancel) return

                            addTransitionClass(element, enterToClass)

                            if (!endEnterByUser) {
                                isNaN(enterDuration)
                                    ? whenTransitionEnd(element, enterCSSInfo || (enterCSSInfo = getTransitionInfo(element, type)), endEnter)
                                    : setTimeout(endEnter, enterDuration)
                            }
                        })
                    }
                    else if (!endEnterByUser) {
                        endEnter()
                    }
                },
                afterEnter: function (vdom) {
                    var element = vdom.element

                    eraseEntering(vdom)
                    removeTransitionClass(element, enterActiveClass)
                    removeTransitionClass(element, enterToClass)

                    callHook(afterEnterHook, [element])

                    if (modeHandler && mode === "in-out") {
                        modeHandler.notify()
                    }
                },
                enterCancelled: function (vdom) {
                    var element = vdom.element

                    element._enterCancel = true

                    eraseEntering(vdom)
                    removeTransitionClass(element, enterActiveClass)
                    removeTransitionClass(element, enterToClass)

                    callHook(enterCancelledHook, [element])
                },

                beforeLeave: function (vdom) {
                    var element = vdom.element

                    if (element._leaveCancel) return

                    markLeaving(vdom)

                    callHook(beforeLeaveHook, [element])

                    addTransitionClass(element, leaveClass)
                    addTransitionClass(element, leaveActiveClass)
                },
                onLeave: function (vdom, endLeave) {
                    var element = vdom.element

                    if (element._leaveCancel) return

                    if (endLeaveByUser) {
                        var done = endLeave.bind(null, false),
                            cancel = endLeave.bind(null, true)

                        callHook(leaveHook, [element, done, cancel])
                    }
                    else {
                        callHook(leaveHook, [element])
                    }

                    if (useCSS) {
                        nextFrame(function () {
                            removeTransitionClass(element, leaveClass)

                            if (element._leaveCancel) return

                            addTransitionClass(element, leaveToClass)

                            if (!endLeaveByUser) {
                                isNaN(leaveDuration)
                                    ? whenTransitionEnd(element, leaveCSSInfo || (leaveCSSInfo = getTransitionInfo(element, type)), endLeave)
                                    : setTimeout(endLeave, leaveDuration)
                            }
                        })
                    }
                    else if (!endLeaveByUser) {
                        endLeave()
                    }
                },
                afterLeave: function (vdom) {
                    var element = vdom.element

                    eraseLeaving(vdom)
                    removeTransitionClass(element, leaveActiveClass)
                    removeTransitionClass(element, leaveToClass)

                    callHook(afterLeaveHook, [element])

                    if (modeHandler && mode === "out-in") {
                        modeHandler.notify()
                    }
                },
                leaveCancelled: function (vdom) {
                    var element = vdom.element

                    element._leaveCancel = true

                    eraseLeaving(vdom)
                    removeTransitionClass(element, leaveActiveClass)
                    removeTransitionClass(element, leaveToClass)

                    callHook(leaveCancelledHook, [element])
                }
            }

            function markEntering(vdom) {
                var enterRecord = (transition.enterRecord || (transition.enterRecord = {})),
                    key = nvl(vdom.meta.transitionKey, vdom.key)

                if (isArray(enterRecord[key])) {
                    enterRecord[key].push(vdom)
                }
                else if (enterRecord[key]) {
                    enterRecord[key] = [enterRecord[key], vdom]
                }
                else {
                    enterRecord[key] = vdom
                }
            }

            function eraseEntering(vdom) {
                var enterRecord = transition.enterRecord,
                    key = nvl(vdom.meta.transitionKey, vdom.key)

                enterRecord && delete enterRecord[key]
            }

            function markLeaving(vdom) {
                var leaveRecord = (transition.leaveRecord || (transition.leaveRecord = {})),
                    key = nvl(vdom.meta.transitionKey, vdom.key)

                if (isArray(leaveRecord[key])) {
                    leaveRecord[key].push(vdom)
                }
                else if (leaveRecord[key]) {
                    leaveRecord[key] = [leaveRecord[key], vdom]
                }
                else {
                    leaveRecord[key] = vdom
                }
            }

            function eraseLeaving(vdom) {
                var leaveRecord = transition.leaveRecord,
                    key = nvl(vdom.meta.transitionKey, vdom.key)

                leaveRecord && delete leaveRecord[key]
            }

            function endStaleLeaving(vdom) {
                var i, key = nvl(vdom.meta.transitionKey, vdom.key)

                if (
                    isDef(key) &&
                    isDef(i = lastTransition) &&
                    isDef(i = i.leaveRecord) &&
                    isDef(i = i[key])
                ) {
                    each(i, function (staleVdom) {
                        if (staleVdom.element._endLeave) {
                            staleVdom.element._endLeave()
                        }
                    })
                }
            }

            return transition
        }

        function callHook(hook, args) {
            if (!isFunction(hook)) return
            hook.apply(null, args)
        }

        function getHookArgsLength(hook) {
            var fns = hook.fns,
                lengths = [0]

            each(fns, function (fn) {
                lengths.push(getArgsLength(fn))
            })

            return Math.max.apply(Math, lengths)
        }

        function createModeHanlder(transition, lastTransition) {
            var mode = transition.mode

            if (!mode || !lastTransition) return

            var lastModeHandler = lastTransition.modeHandler // ????????????????????? modeHandler ?????? listener ????????????

            if (lastModeHandler && mode === "out-in") return lastModeHandler // ?????? modeHandler????????? out-in ??????????????????????????????????????????

            if (lastModeHandler && mode === "in-out") lastModeHandler.end() // ????????????????????? in-out ?????????????????????????????????????????????????????????

            return genModeHandler()
        }

        function genModeHandler() {
            var invoker = createInvoker()

            return {
                notify: function () {
                    invoker()
                    invoker.remove()
                },
                end: function () {
                    invoker(true)
                    invoker.remove()
                },
                addListener: function (fn) {
                    invoker.add(fn)
                }
            }
        }

        function transitionEnter(vdom, showElement) {
            var element = vdom.element,
                transition = vdom.meta.transition

            if (element.nodeType !== 1) return

            if (element._endLeave) element._endLeave(true)

            if (transition.isAppear && !transition.allowAppear) return

            if (element._endEnter) return

            resolveTransition(transition)

            var hooks = transition.hooks,
                beforeEnter = hooks.beforeEnter,
                onEnter = hooks.onEnter,
                afterEnter = hooks.afterEnter,
                enterCancelled = hooks.enterCancelled,

                endEnter = element._endEnter = function endEnter(isCancel) {
                    if (endEnter._once_) return
                    endEnter._once_ = true

                    isCancel ? enterCancelled(vdom) : afterEnter(vdom)

                    element._endEnter = null
                }

            beforeEnter(vdom)

            if (transition.mode === "out-in" && transition.modeHandler) {
                visible(element, false)
                intoLayout(element, false)
                element._removeImmediate = true
                element._mode = transition.mode

                return transition.modeHandler.addListener(function enterAfterOut() {
                    element._mode = element._removeImmediate = null

                    if (element._enterCancel && !showElement) return

                    visible(element, true)
                    intoLayout(element, true)

                    if (element._enterCancel) return

                    if (isFunction(showElement)) {
                        showElement()
                    }
                    onEnter(vdom, endEnter)
                })
            }

            if (isFunction(showElement)) {
                showElement()
                onEnter(vdom, endEnter)
            }
            else {
                patchCallbacks.push(function transitionEnterNow() { // ????????????????????????
                    onEnter(vdom, endEnter)
                })
            }
        }

        function transitionLeave(vdom, callback) {
            var element = vdom.element,
                transition = vdom.meta.transition

            if (element.nodeType !== 1) return callback()

            if (element._endEnter) element._endEnter(true)

            if (element._removeImmediate) return callback()

            if (element._endLeave) return

            resolveTransition(transition)

            var hooks = transition.hooks,
                beforeLeave = hooks.beforeLeave,
                onLeave = hooks.onLeave,
                afterLeave = hooks.afterLeave,
                leaveCancelled = hooks.leaveCancelled,

                endLeave = element._endLeave = function endLeave(isCancel) {
                    if (endLeave._once_) return
                    endLeave._once_ = true

                    if (isCancel) {
                        leaveCancelled(vdom)
                    }
                    else {
                        afterLeave(vdom)
                        callback()
                    }

                    element._endLeave = null
                }

            beforeLeave(vdom)

            if (transition.mode === "in-out" && transition.modeHandler) {
                element._mode = transition.mode

                return transition.modeHandler.addListener(function leaveAfterIn(isEnd) {
                    element._mode = null
                    isEnd ? endLeave() : onLeave(vdom, endLeave)
                })
            }

            onLeave(vdom, endLeave)
        }

        var Reg$TransformProp = /\b(transform|all)(,|$)/,
            TRANSITION = 'transition',
            ANIMATION = 'animation',
            transitionProp = TRANSITION,
            transitionEndEvent = 'transitionend',
            animationProp = ANIMATION,
            animationEndEvent = 'animationend'

        if (isUndef(window.ontransitionend) && isDef(window.onwebkittransitionend)) {
            transitionProp = 'WebkitTransition'
            transitionEndEvent = 'webkitTransitionEnd'
        }

        if (isUndef(window.onanimationend) && isDef(window.onwebkitanimationend)) {
            animationProp = 'WebkitAnimation'
            animationEndEvent = 'webkitAnimationEnd'
        }

        function updateTransitionFragment(vdom, oldVdom) {
            var transition = vdom ? vdom.transition : oldVdom.transition,
                parentNode = vdom ? vdom.element : oldVdom.element,
                shouldMove = transition.move,
                allChildren = [],
                removeChildren = [],
                moveElements = [],
                newChildKeyMap = {}

            if (vdom) {
                transition.connect(oldVdom.transition)

                oldVdom.transition = transition
                addMeta(oldVdom, "transition", transition)

                VirtualDOM.eachRealChild(vdom.children, function (child) {
                    allChildren.push(child)
                    newChildKeyMap[child.key] = true
                })
            }

            if (shouldMove) {
                VirtualDOM.eachElement(oldVdom, function (element) {
                    if (element.nodeType !== 1) return
                    setPosition("_oldPos_", element)
                    moveElements.push(element)
                })
            }

            VirtualDOM.eachRealChild(oldVdom.children, function (child, i, children) {
                if (!newChildKeyMap.hasOwnProperty(child.key)) {
                    allChildren.push(child)
                    removeChildren.push(child)
                    children[i] = Undefined
                }
            })

            /**
             * ?????????????????????????????????????????? patch ??????????????????????????????????????????????????????????????????????????????
             */
            if (removeChildren.length) {
                VirtualDOM.patchChildren(parentNode, removeChildren)
            }

            if (shouldMove) {
                transitionMove(transition, moveElements, allChildren)
            }
        }

        function transitionMove(transition, moveElements, allChildren) {
            resolveTransition(transition)

            var moveClass = transition.moveClass

            patchCallbacks.push(function transitionMoveNow() {
                moveElements.forEach(endLastTransition) // ??????????????????????????????/??????????????????????????????????????????
                allChildren.forEach(fixModePlace)

                moveElements.forEach(saveNewPos) // getBoundingClientRect ?????????????????????????????????????????? transform ????????? stayAtOldPos ????????????
                moveElements.forEach(stayAtOldPos)

                document.body.offsetHeight // ????????????????????????????????????????????????????????????

                moveElements.forEach(moveToNewPos)
            })

            function endLastTransition(element) {
                if (element._endMove) {
                    element._endMove()
                }

                // if (element._endEnter) {
                //     element._endEnter()
                // }
            }

            function fixModePlace(vdom) {
                VirtualDOM.eachElement(vdom, function (element) {
                    if (element._mode === "out-in") {
                        intoLayout(element, true)
                    }
                    else if (element._mode === "in-out") {
                        intoLayout(element, false)
                    }
                })
            }

            function saveNewPos(element) {
                setPosition("_newPos_", element)
            }

            function stayAtOldPos(element) {
                var oldPos = element._oldPos_,
                    newPos = element._newPos_,
                    moveX = oldPos.left - newPos.left,
                    moveY = oldPos.top - newPos.top

                if (moveX || moveY) {
                    element._needMove_ = true

                    var style = element.style
                    style.transitionDuration = '0s'
                    style.transform = style.WebkitTransform = "translate(" + moveX + "px," + moveY + "px)"
                }
            }

            function moveToNewPos(element) {
                if (!element._needMove_) return

                addClass(element, moveClass)

                var style = element.style
                style.transform = style.WebkitTransform = style.transitionDuration = ''

                element.addEventListener(transitionEndEvent, element._endMove = function cb(e) {
                    if (e && e.target !== element) return

                    if (!e || /transform$/.test(e.propertyName)) {
                        element.removeEventListener(transitionEndEvent, cb)
                        element._endMove = null
                        removeClass(element, moveClass)
                    }
                })
            }
        }

        function setPosition(key, element) {
            element[key] = element.getBoundingClientRect()
        }

        function whenTransitionEnd(element, info, callback) {
            var type = info.type,
                timeout = info.timeout,
                propCount = info.propCount

            if (!type) { return callback() }

            var event = type === TRANSITION ? transitionEndEvent : animationEndEvent,
                ended = 0,
                end = function () {
                    element.removeEventListener(event, onEnd)
                    callback()
                },
                onEnd = function (e) {
                    if (e.target === element) {
                        if (++ended >= propCount) {
                            end()
                        }
                    }
                }

            setTimeout(function () {
                if (ended < propCount) {
                    end()
                }
            }, timeout + 1)

            element.addEventListener(event, onEnd)
        }

        function getTransitionInfo(element, type) {
            var style = window.getComputedStyle(element),
                transitionDelays = (style[transitionProp + 'Delay'] || '').split(', '),
                transitionDurations = (style[transitionProp + 'Duration'] || '').split(', '),
                animationDelays = (style[animationProp + 'Delay'] || '').split(', '),
                animationDurations = (style[animationProp + 'Duration'] || '').split(', '),
                transitionTimeout = getTimeout(transitionDelays, transitionDurations),
                animationTimeout = getTimeout(animationDelays, animationDurations)

            var timeout = 0, propCount = 0

            if (type === TRANSITION) {
                if (transitionTimeout > 0) {
                    timeout = transitionTimeout
                    propCount = transitionDurations.length
                }
            }
            else if (type === ANIMATION) {
                if (animationTimeout > 0) {
                    timeout = animationTimeout
                    propCount = animationDurations.length
                }
            }
            else {
                timeout = Math.max(transitionTimeout, animationTimeout)
                type = timeout > 0
                    ? transitionTimeout > animationTimeout
                        ? TRANSITION
                        : ANIMATION
                    : null
                propCount = type
                    ? type === TRANSITION
                        ? transitionDurations.length
                        : animationDurations.length
                    : 0
            }

            var hasTransform =
                type === TRANSITION &&
                Reg$TransformProp.test(style[transitionProp + 'Property'])

            return {
                type: type,
                timeout: timeout,
                propCount: propCount,
                hasTransform: hasTransform
            }
        }

        function getTimeout(delays, durations) {
            while (delays.length < durations.length) {
                delays = delays.concat(delays)
            }

            return Math.max.apply(null, durations.map(function (d, i) {
                return toMs(d) + toMs(delays[i])
            }))
        }

        function toMs(s) {
            return Number(s.slice(0, -1).replace(',', '.')) * 1000
        }

        function display(element, show) {
            if (isUndef(element.__displayOnShow)) {
                element.__displayOnShow = element.style.display === 'none' ? '' : element.style.display
            }

            element.style.display = show ? element.__displayOnShow : 'none'
        }

        function visible(element, show) {
            if (isUndef(element.__visibility)) {
                element.__visibility = element.style.visibility === "hidden" ? '' : element.style.visibility
            }

            element.style.visibility = show ? element.__visibility : 'hidden'
        }

        function intoLayout(element, isTrue) {
            if (isUndef(element.__position)) {
                element.__position = element.style.position
            }

            element.style.position = isTrue ? element.__position : 'absolute'
        }

        var raf = window.requestAnimationFrame || window.setTimeout

        function nextFrame(fn) {
            raf(function () {
                raf(fn)
            })
        }

        var Reg$PseudoSelector = /([^:])((?::{1,2}[^,]+)?\s*(?:,|$))/g,
            styleId = 0

        function processStyle(style) {
            if (!style) return

            var privateStyleId = "private-" + (++styleId),
                cssLines = parseCSS(style),
                cssText = cssLines.map(function (cssLine) {
                    if (isString(cssLine)) {
                        return cssLine
                    }
                    return cssLine.selector.replace(Reg$PseudoSelector, "$1[" + privateStyleId + "]$2") + " " + cssLine.content
                }).join("\n")

            if (document.createStyleSheet) {
                var sheet = document.createStyleSheet()

                sheet.cssText = cssText
            }
            else {
                var styleElm = document.createElement("style")

                styleElm.appendChild(document.createTextNode(cssText))
                styleElm.setAttribute("type", "text/css")
                document.head.appendChild(styleElm)
            }

            return privateStyleId
        }

        function parseCSS(cssObj) {
            var cssLines = []

            for (var selector in cssObj) {
                var styleObj = cssObj[selector]

                if (selector === "@keyframes") {
                    push(cssLines, parseKeyframes(styleObj))
                }
                else {
                    push(cssLines, parseSelectorStyle(selector, styleObj))
                }
            }

            return cssLines
        }

        function parseKeyframes(keyFrames) {
            var cssLines = []

            for (var animateName in keyFrames) {
                var animateFrames = keyFrames[animateName],
                    animateContent = ""

                for (var frameDesc in animateFrames) {
                    var styleObj = animateFrames[frameDesc],
                        styleContent = ""

                    for (var prop in styleObj) {
                        var propVal = styleObj[prop]

                        styleContent += processStyleProp(prop, propVal)
                    }

                    if (styleContent) {
                        animateContent += frameDesc + wrapCurly(styleContent)
                    }
                }

                if (animateContent) {
                    cssLines.push("@keyframes " + animateName + " " + wrapCurly(animateContent))
                }
            }

            return cssLines
        }

        function parseSelectorStyle(selector, styleObj) {
            var styleContent = "",
                cssLines = []

            for (var prop in styleObj) {
                var propVal = styleObj[prop]

                if (isPlainObject(propVal)) {
                    var childStyleObj = propVal,
                        childSelector = combine(selector.split(Reg$SplitComma), prop.split(Reg$SplitComma))
                            .map(function (item) {
                                var parent = item[0], child = item[1]

                                return ~child.indexOf("&") ? child.replace("&", parent) : parent + " " + child
                            })
                            .join(","),
                        childCssLines = parseSelectorStyle(childSelector, childStyleObj)

                    if (childCssLines.length) {
                        push(cssLines, childCssLines)
                    }
                }
                else {
                    styleContent += processStyleProp(prop, propVal)
                }
            }

            if (styleContent) {
                cssLines.unshift({ selector: selector, content: wrapCurly(styleContent) })
            }

            return cssLines
        }

        /**
         * ????????????????????????????????????????????????...todo
         * @param {String} prop 
         * @param {String} propVal 
         */
        function processStyleProp(prop, propVal) {
            propVal = nvl(propVal, "")

            switch (prop) {
                case "content":
                    return prop + ":" + '"' + propVal + '";'
                default:
                    return prop + ":" + propVal + ";"
            }
        }

        function wrapCurly(val) {
            return "{" + val + "}"
        }

        var mergeRules = {
            "private-style": function (cur, next) {
                if (~("," + cur + ",").indexOf("," + next + ",")) return cur
                return [].concat(cur, next)
            }
        }

        function addMeta(vdom, name, value) {
            if (isPlainObject(name)) {
                var meta$ = name

                for (name in meta$) {
                    if (meta$.hasOwnProperty(name)) {
                        addMeta(vdom, name, meta$[name])
                    }
                }

                return
            }

            if (vdom.isFragment) {
                for (var i = 0, len = vdom.children.length; i < len; i++) {
                    addMeta(vdom.children[i], name, value)
                }

                return
            }

            var meta = vdom.meta || (vdom.meta = {})

            if (meta.hasOwnProperty(name)) {
                value = isFunction(mergeRules[name]) ? mergeRules[name](meta[name], value) : value
            }

            meta[name] = value

            if (vdom.isComponent && vdom.component) {
                addMeta(vdom.component.getRootNode(), name, value)
            }
        }

        function hasMeta(vdom, name) {
            return vdom.meta && vdom.meta.hasOwnProperty(name)
        }

        function setCurentInstance(instance) {
            var prev = currentInstance
            currentInstance = instance
            return function () {
                currentInstance = prev
            }
        }

        function clearKeys(obj) {
            for (var k in obj) {
                if (obj.hasOwnProperty(k)) {
                    delete obj[k]
                }
            }
        }

        /**
         * ??????????????????????????????????????????????????????????????????
         * @param {*} createSurrogate 
         * @returns 
         */
        function normailzeSurrogate(createSurrogate) {
            return function (fn) {
                if (fn._createBy_ === createSurrogate) {
                    fn = fn._target_
                }

                var raw = fn._raw_ || fn,
                    surrogate = createSurrogate.apply(this, arguments)

                surrogate._raw_ = raw
                surrogate._target_ = fn
                surrogate._createBy_ = createSurrogate

                return surrogate
            }
        }

        function getRawFn(fn) {
            return fn._raw_ || fn
        }

        function getArgsLength(fn) {
            return getRawFn(fn).length
        }

        function createInvoker(fns) {
            var invoker = function () {
                if (isUndef(fns)) return

                var args = arguments

                each(fns, function (fn) {
                    fn.apply(null, args)
                })
            }

            invoker.fns = fns

            invoker.add = function (fn) {
                if (!isFunction(fn)) return

                if (isArray(fns)) {
                    if (fns.includes(fn)) return
                    fns.push(fn)
                }
                else if (fns) {
                    if (fns === fn) return
                    fns = [fns, fn]
                }
                else {
                    fns = fn
                }

                invoker.fns = fns
            }

            invoker.remove = function (fn) {
                if (isUndef(fn)) return fns = Undefined

                if (isArray(fns)) {
                    var i = fns.indexOf(fn)
                    ~i && fns.splice(i, 1)
                }
                else if (fns && fns === fn) {
                    fns = Undefined
                }

                invoker.fns = fns
            }

            return invoker
        }

        var LOC = null

        function markLocation(start, end) {
            LOC = isPlainObject(start)
                ? start
                : isDef(start) && isDef(end)
                    ? { start: start, end: end }
                    : null
        }

        function markTemplate(template, start, end) {
            if (isUndef(start)) return ""

            if (isPlainObject(start)) {
                var loc = start
                start = loc.start
                end = loc.end
            }

            var markText = template.substring(start, end).trim(),
                repeatTimes = findMatch(template.substring(0, start), markText).length,
                prettyTemplate = pretty(template),
                matchs = findMatch(prettyTemplate, markText),
                matcher = matchs[repeatTimes]

            start = matcher.index
            end = start + matcher[0].length

            var lines = prettyTemplate.split("\n"),
                hitLines = [],
                moreLines = 2,
                count = 0

            for (var i = 0, len = lines.length; i < len; i++) {
                var line = lines[i],
                    lineLen = line.length

                count += lineLen + 1// ??????????????????????????? \n

                var lineStart = count - lineLen - 1,
                    lineEnd = count

                /**
                 * ??????????????????????????????
                 */
                if (lineEnd > start && lineStart < end) {
                    if (!hitLines.length) {
                        push(hitLines, lines.slice(Math.max(0, i - moreLines), i))
                    }

                    hitLines.push(line)

                    var markLineStart = lineStart < start ? start - lineStart : 0,
                        markLineEnd = end < lineEnd ? end - lineStart : lineLen

                    markLineStart = Math.max(line.search(/\S/), markLineStart)
                    markLineStart = charLength(line.substring(0, markLineStart))
                    markLineEnd = charLength(line.substring(0, markLineEnd))

                    hitLines.push(genMarkLine(markLineStart, markLineEnd))

                    if (lineEnd >= end) {
                        push(hitLines, lines.slice(i + 1, Math.min(len - 1, i + 1 + moreLines)))
                    }
                }
                else if (hitLines.length) {
                    break;
                }
            }

            if (hitLines.length) {
                var outputLines = hitLines,
                    first = hitLines[0],
                    last = hitLines.at(-1),
                    minIndentLen = Math.min(first.match(/^\s*/)[0].length, last.match(/^\s*/)[0].length)

                if (minIndentLen) {
                    var removeIndent = new RegExp("^\\s{" + minIndentLen + "}")

                    outputLines = []

                    for (var i = 0, len = hitLines.length; i < len; i++) {
                        outputLines.push(hitLines[i].replace(removeIndent, ""))
                    }
                }

                var hr = "-".repeat(100)

                outputLines.unshift(hr)
                outputLines.push(hr)

                return outputLines.join("\n")
            }

            return ""

            function findMatch(template, markText) {
                var Reg$MarkText = new RegExp(markText.replace(/[\^?$.()+*{}\[\]]/g, "\\$&").replace(/>(?=\S)/g, "$&\\s*").replace(/(\S)(<)/g, "$1\\s*$2").replace(/\s+/g, "\\s*"), "g"),
                    matchers = [],
                    matcher

                while (matcher = Reg$MarkText.exec(template)) {
                    matchers.push(matcher)
                }

                return matchers
            }

            function genMarkLine(start, end) {
                return " ".repeat(start) + "^".repeat(end - start)
            }

            function pretty(template) {
                var prettyTemplate = template.replace(/\s{6,}/g, "\n$&"),
                    lines = prettyTemplate.split("\n"),
                    last = lines.at(-1),
                    indentCount = last.match(/^\s*/)[0].length,
                    indentReg = new RegExp("^\\s{" + indentCount + "}")

                if (indentCount) {
                    lines = lines.map(function (line) {
                        return line.replace(indentReg, "")
                    })
                }

                return lines.join("\n")
            }
        }

        var parseTemplate = function () {
            var Reg$ElemOpenStart = /^<([\w\u4e00-\u9fa5-]+)\s*/,
                Reg$ElemOpenEnd = /^(\/)?>\s*/,
                Reg$ElemClose = /^<\/([\w\u4e00-\u9fa5-]+)\s*>\s*/,
                Reg$Comment = /^<!--((?:[^-]|-(?!->))*)-->\s*/,
                Reg$Mustache = /{{((?:[^}]|}(?!})|}(?=}}))*)}}/,
                mustache = Reg$Mustache.source,
                parenthesis = '\\([^\)]*\\)',
                elemAttrValue = // ???mustache???????????????????????????????????????????????????????????????
                    '(["\'])' + // ?????????????????????
                    // ???????????????????????????????????????????????? | mustache | ????????? | ????????????????????????????????? | ?????????????????????????????? | ?????????mustache,parenthesis???{(
                    '((?:[^{("\'\\\\]|' + mustache + '|' + parenthesis + '|(?!\\3)["\']|\\\\\\3?|[{(])*)' +
                    '\\3', // ?????????????????????
                Reg$ElemAttr = new RegExp("^([\\w-@#:.$|]+)(\\s*=\\s*" + elemAttrValue + ")?\\s*"),// $1:????????????$2:????????????????????????????$3:?????????$4:????????????
                Reg$TextContent = new RegExp("^(?:[^<{]|" + mustache + "|{)+"),
                Reg$SingleElem = /^(?:img|input|br|hr|param|meta|link)$/,
                start = 0, end = 0,
                intactTemplate

            function doParse(template, context) {
                if (!template) {
                    if (context.type !== "root") {
                        throw parse_warn('???????????????', context.open_loc)
                    }
                    return
                }

                var matcher = null

                if (matcher = template.match(Reg$ElemOpenStart)) {
                    template = cutMatch(template, matcher)

                    var tagName = matcher[1],
                        attrs = [],
                        tagToken = null,
                        open_loc = LOC

                    while (matcher = template.match(Reg$ElemAttr)) {
                        template = cutMatch(template, matcher)

                        var attrName = matcher[1],
                            attrNameOnly = !matcher[2],
                            attrValue = attrNameOnly ? "" : matcher[4].trim(),
                            hasMustache = attrNameOnly ? false : Boolean(attrValue) && Reg$Mustache.test(attrValue)

                        attrs.push({
                            name: attrName,
                            value: attrValue,
                            hasMustache: hasMustache,
                            loc: LOC
                        })
                    }

                    if (matcher = template.match(Reg$ElemOpenEnd)) {
                        template = cutMatch(template, matcher)
                        open_loc.end = LOC.end

                        var isSingle = Boolean(matcher[1]) || Boolean(tagName.match(Reg$SingleElem))

                        tagToken = {
                            type: 'tag',
                            tagName: tagName,
                            isSingle: isSingle,
                            attrs: attrs,
                            children: [],
                            parent: context,
                            next: null,
                            prev: null,
                            loc: clone(open_loc),
                            open_loc: open_loc,
                            close_loc: null
                        }

                        var lastChild = context.children.at(-1)

                        lastChild && (lastChild.next = tagToken, tagToken.prev = lastChild)

                        context.children.push(tagToken)

                        doParse(template, isSingle ? context : tagToken)
                    }
                    else {
                        throw parse_warn('???????????????', open_loc.start, end)
                    }
                }
                else if (matcher = template.match(Reg$ElemClose)) {
                    template = cutMatch(template, matcher)

                    var tagName = matcher[1]

                    if (tagName != context.tagName) throw parse_warn('??????????????????', LOC)

                    context.loc.end = LOC.end
                    context.close_loc = LOC

                    doParse(template, context.parent)
                }
                else if (matcher = template.match(Reg$Comment)) {
                    template = cutMatch(template, matcher)

                    var textContent = matcher[1],
                        commentToken = {
                            type: 'comment',
                            textContent: textContent,
                            parent: context,
                            next: null,
                            prev: null,
                            loc: LOC
                        }

                    var lastChild = context.children.at(-1)

                    lastChild && (lastChild.next = commentToken, commentToken.prev = lastChild)

                    context.children.push(commentToken)

                    doParse(template, context)
                }
                else if (matcher = template.match(Reg$TextContent)) {
                    template = cutMatch(template, matcher)

                    var textContent = matcher[0].trim(),
                        textToken

                    if (textContent) {
                        textToken = {
                            type: 'text',
                            textContent: textContent,
                            parent: context,
                            next: null,
                            prev: null,
                            loc: LOC
                        }

                        var lastChild = context.children.at(-1)

                        lastChild && (lastChild.next = textToken, textToken.prev = lastChild)

                        context.children.push(textToken)
                    }

                    doParse(template, context)
                }
                else {
                    throw parse_warn('???????????????', start, start + 1)
                }
            }

            function parse_warn(message, start, end) {
                var markFrame = markTemplate(intactTemplate, start, end)

                logWarning(message + "\n" + markFrame)
            }

            function cutMatch(template, matcher) {
                var startIndex = matcher.index,
                    endIndex = startIndex + matcher[0].length

                start = end + startIndex
                end = end + endIndex

                markLocation(start, end)

                return template.substring(endIndex)
            }

            return function parseTemplate(template) {
                var root = { type: "root", children: [] }

                intactTemplate = template
                start = 0, end = 0
                doParse(template, root)

                markLocation(null)
                return root
            }
        }()
    }

    function Store(require, module, exports) {
        module.exports = Store

        var Observer = require("Observer"),
            utils = require("utils"),
            pathResolve = utils.pathResolve,
            readData = utils.readData,
            writeData = utils.writeData,
            hasKeyPath = utils.hasKeyPath,
            collectFunctionDeps = utils.collectFunctionDeps

        utils = null

        function Store(options) {
            if (!isPlainObject(options)) {
                throw logError("Store ?????????????????????????????? options ??????")
            }

            var state = options.state,
                getters = options.getters,
                actions = options.actions

            if (!isPlainObject(state)) {
                throw logError("Store ???????????????????????? options ???????????? state ????????????", options)
            }

            this.subStores = {}
            this.listeners = null
            this.observer = new Observer()
            this.actions = actions

            var allowModify = false

            this.state = deepProxy(state, {
                set: function (target, key, val) {
                    allowModify
                        ? Reflect.set(target, key, val)
                        : logError("???????????????" + key + "????????????state ???????????????????????????????????? commit ????????????")
                    return true
                },
                deleteProperty: function (target, key) {
                    logError("???????????????" + key + "????????????state ??????????????????????????????")
                }
            })

            var getterMap = Undefined

            if (isPlainObject(getters)) {
                this._initGetters(getters, unlock)
                getterMap = Object.keys(getters).reduce(function (obj, name) {
                    obj[name] = Undefined
                    return obj
                }, {})
            }

            this.commit = this.commit.bind(this, unlock, getterMap)

            function unlock(isAllow) {
                allowModify = isAllow
            }
        }

        Store.prototype = {
            constructor: Store,
            getRaw: function () {
                return this
            },
            provide: function () {
                var store = this,
                    keyPaths = slice(arguments).filter(function (keyPath) {
                        return store._checkKey(keyPath)
                    }),
                    index = this._cacheIndex(keyPaths),
                    subStore = this.subStores[index] || (this.subStores[index] = this._createSubStore(keyPaths))

                return subStore
            },
            commit: function (unlock, getterMap, keyPath, val) {
                var store = this,
                    state = this.state,
                    changeState = {},
                    dirtyKeyPaths = []

                unlock(true)

                if (isString(keyPath)) {
                    commitOnce(keyPath, val)
                }
                else if (isPlainObject(keyPath)) {
                    var data = keyPath

                    keyPath = ""

                    for (keyPath in data) {
                        if (!data.hasOwnProperty(keyPath)) continue

                        commitOnce(keyPath, data[keyPath])
                    }
                }

                unlock(false)

                if (!dirtyKeyPaths.length) return

                this._emitListener(changeState)

                this.observer.update(dirtyKeyPaths)

                function commitOnce(keyPath, val) {
                    if (isPlainObject(getterMap) && getterMap.hasOwnProperty(keyPath)) {
                        logWarning("Store ?????????" + keyPath + "?????? getter????????? commit")
                    }
                    else if (store._checkKey(keyPath) && readData(state, keyPath) !== val) {
                        writeData(state, keyPath, val)
                        writeData(changeState, keyPath, val)
                        dirtyKeyPaths.push(keyPath)
                    }
                }
            },
            dispatch: function (name, payload) {
                var actions = this.actions,
                    action = actions && actions[name]

                if (!isFunction(action)) return

                action.call(this, this.state, this.commit, payload)
            },
            onupdate: function (listener) {
                var listeners = this.listeners || (this.listeners = [])

                listeners.push(listener)

                return function stop() {
                    var index = listeners.findIndex(function (f) { return f === listener })
                    ~index && listeners.splice(index, 1)
                }
            },
            _emitListener: function (changeState) {
                var store = this

                this.listeners && this.listeners.forEach(function (listener) {
                    listener.call(store, changeState)
                })
            },
            _createSubStore: function (keyPaths) {
                var store = this,
                    subStore = {
                        getRaw: function () {
                            return store
                        },
                        commit: function () {
                            return store.commit.apply(store, arguments)
                        },
                        dispatch: function () {
                            return store.dispatch.apply(store, arguments)
                        },
                        onupdate: noop
                    }

                if (keyPaths && keyPaths.length) {
                    var onupdate = this.observer.observe(keyPaths),
                        state = this.state,
                        changeState = null

                    onupdate.deep(function (causes) {
                        changeState = {}

                        causes.forEach(function (causeKeyPath) {
                            var val = readData(state, causeKeyPath)

                            writeData(subStore, causeKeyPath, val)
                            writeData(changeState, causeKeyPath, val)
                        })
                    })

                    keyPaths.forEach(function (keyPath) {
                        writeData(subStore, keyPath, readData(state, keyPath))
                    })

                    subStore.onupdate = function (listener) {
                        return onupdate.deep(function (causes) {
                            listener.call(subStore, changeState, causes)
                        })
                    }
                }

                return subStore
            },
            _initGetters: function (userDefineGetters, unlock) {
                var store = this,
                    state = this.state,
                    observer = this.observer,
                    observables = {}

                for (var key in state) {
                    if (state.hasOwnProperty(key)) {
                        observables[key] = Undefined
                    }
                }

                var conflicts = []

                for (var name in userDefineGetters) {
                    if (userDefineGetters.hasOwnProperty(name)) {
                        observables[name] = Undefined

                        if (state.hasOwnProperty(name)) {
                            conflicts.push("???" + name + "???")
                        }
                    }
                }

                if (conflicts.length) {
                    throw logError("Store ????????????????????? getters ??? state ?????????????????????????????????" + conflicts.join(" "))
                }

                for (var name in userDefineGetters) {
                    var inited = state.hasOwnProperty(name)

                    if (inited) continue

                    initGetter(name)
                }

                userDefineGetters = observables = initGetter = null

                function initGetter(name) {
                    var getter = userDefineGetters[name],
                        getterDeps = collectFunctionDeps(getter, observables)

                    if (getterDeps) {
                        getterDeps.forEach(function (keyPath) {
                            var pathKeys = pathResolve(keyPath),
                                name$ = pathKeys[0],
                                isUninitGetter = userDefineGetters.hasOwnProperty(name$) && !state.hasOwnProperty(name$)

                            if (!isUninitGetter) return

                            initGetter(name$)
                        })

                        var onupdate = observer.observe(getterDeps)

                        onupdate.deep(function () {
                            var oldValue = state[name],
                                value = getter.call(state)

                            unlock(true)
                            state[name] = value
                            unlock(false)

                            if (!isEqual(oldValue, value)) {
                                var changeState = {}
                                changeState[name] = value

                                store._emitListener(changeState)
                                observer.update(name)
                            }
                        })
                    }

                    unlock(true)
                    state[name] = getter.call(state)
                    unlock(false)
                }
            },
            _checkKey: function (keyPath) {
                return hasKeyPath(this.state, keyPath) || (logWarning("Store ?????????????????????" + keyPath + "???"), false)
            },
            _cacheIndex: function (keyPaths) {
                return keyPaths.sort().join("_")
            }
        }
    }

    function VirtualDOM(require, module, exports) {
        module.exports = VirtualDOM

        var utils = require("utils"),
            classStringify = utils.classStringify,
            styleStringify = utils.styleStringify

        utils = null

        function VirtualDOM(type, options) {
            if (isUndef(type)) throw logError("VirtualDOM????????????????????????????????? type")
            if (isUndef(options)) throw logError("VirtualDOM????????????????????????????????? options")

            this.type = type
            this.isElement = type === "element"
            this.isComponent = type === "component"
            this.isText = type === "text"
            this.isComment = type === "comment"
            this.isFragment = type === "fragment"

            if (this.isComponent && isUndef(Component)) {
                this.type = "comment"
                this.isComponent = false
                this.isComment = true
                options.comment = options.tagName
            }

            switch (type) {
                case "element":
                    this.tagName = options.tagName // require
                    this.attrs = options.attrs
                    this.props = options.props
                    this.key = options.key
                    this.children = options.children
                    this.node = options.node
                    this.element = null
                    handleFormElemAttr(this)
                    break
                case "component":
                    this.tagName = options.tagName // require
                    this.componentDefinition = options.componentDefinition
                    this.componentData = options.componentData
                    this.key = options.key
                    break
                case "text":
                    this.text = options.text // require
                    this.element = null
                    break
                case "comment":
                    this.comment = options.comment // require
                    this.element = null
                    break
                case "fragment":
                    this.key = options.key
                    this.children = options.children // require
                    this.element = null // fragment ??? element ????????? vdom ??? element????????????????????? vdom ?????????
                    break
                default:
                    throw logError("VirtualDOM?????????????????????????????????????????????" + type + "???")
            }
        }

        VirtualDOM.prototype = {
            constructor: VirtualDOM,
            hasAttribute: function (key) {
                if (this.isElement && this.attrs) {
                    return this.attrs.hasOwnProperty(key)
                }
                else if (this.isComponent && this.componentData && isPlainObject(this.componentData.props)) {
                    return this.componentData.props.hasOwnProperty(key)
                }

                return false
            },
            getAttribute: function (key) {
                if (this.isElement && this.attrs) {
                    return this.attrs[key]
                }
                else if (this.isComponent && this.componentData && isPlainObject(this.componentData.props)) {
                    return this.componentData.props[key]
                }
            },
            setAttribute: function (key, val) {
                if (this.isElement) {
                    this.attrs || (this.attrs = {})
                    this.attrs[key] = val
                }
                else if (this.isComponent) {
                    this.componentData || (this.componentData = {})
                    this.componentData.props || (this.componentData.props = {})
                    this.componentData.props[key] = val
                }
            },
            hasElementProperty: function (key) {
                if (this.isElement && this.props) {
                    return this.props.hasOwnProperty(key)
                }

                return false
            },
            getElementProperty: function (key) {
                if (this.isElement && this.props) {
                    return this.props[key]
                }
            },
            setElementProperty: function (key, val) {
                if (!this.isElement) return

                this.props || (this.props = {})
                this.props[key] = val
            }
        }

        var Component = null,
            ComponentInterface = {
                create: function (context) {
                    interfaceError('create')
                },
                update: function (context) {
                    interfaceError('update')
                },
                mount: function (parentNode, refNode) {
                    interfaceError('mount')
                },
                remove: function () {
                    interfaceError('remove')
                },
                getRootNode: function () {
                    interfaceError('getRootNode')
                }
            },
            interfaceError = function (name) {
                logError("VirtualDOM??????????????????????????????????????????" + name + "?????????", Component)
            },
            hooksCallback = {}

        extend(VirtualDOM, {
            patch: patch,
            patchChildren: patchChildren,
            eachRealChild: eachRealChild,
            eachElement: eachElement,
            createElementWithNode: function (node, key) {
                if (isUndef(node) || node.nodeType !== 1) return

                return new VirtualDOM("element", {
                    tagName: node.nodeName,
                    node: node,
                    key: key
                })
            },
            createElement: function (tagName, attrs, props, children, key) {
                if (isUndef(tagName)) return

                return new VirtualDOM("element", {
                    tagName: tagName,
                    attrs: attrs,
                    props: props,
                    children: children,
                    key: key
                })
            },
            createComponent: function (tagName, componentDefinition, componentData, key) {
                if (isUndef(tagName)) return

                return new VirtualDOM("component", {
                    tagName: tagName,
                    componentDefinition: componentDefinition,
                    componentData: componentData,
                    key: key
                })
            },
            createText: function (text) {
                if (isUndef(text)) return

                return new VirtualDOM("text", { text: text })
            },
            createComment: function (comment) {
                if (isUndef(comment)) return

                return new VirtualDOM("comment", { comment: comment })
            },
            createFragment: function (children, key) {
                if (!isArray(children)) return

                children = children.filter(isDef)

                if (!children.length) return

                return new VirtualDOM("fragment", { children: children, key: key })
            },
            useComponent: function (_Component) {
                if (!isFunction(_Component)) return logWarning("??????????????????????????????")

                var success = true

                Component = _Component

                for (var method in ComponentInterface) {
                    if (!(method in _Component.prototype)) {
                        ComponentInterface[method]()
                        success = false
                    }
                }

                if (!success) {
                    Component = null
                }
            },
            addHook: function (name, cb) {
                if (isPlainObject(name)) {
                    var hooks = name

                    for (name in hooks) {
                        addHook(name, hooks[name])
                    }
                }
                else {
                    addHook(name, cb)
                }
            }
        })

        function eachRealChild(children, fn) {
            for (var i = 0, len = children.length; i < len; i++) {
                var child = children[i]

                if (isUndef(child)) continue

                if (child.isFragment) {
                    eachRealChild(child.children, fn)
                }
                else {
                    fn(child, i, children)
                }
            }
        }

        function eachElement(vdomOrNode, fn) {
            if (vdomOrNode.isComponent) {
                eachElement(vdomOrNode.component.getRootNode(), fn)
            }
            else if (vdomOrNode.isFragment) {
                eachRealChild(vdomOrNode.children, function (vdom) {
                    eachElement(vdom, fn)
                })
            }
            else if (vdomOrNode.element) {
                fn(vdomOrNode.element)
            }
            else if (vdomOrNode.nodeType) {
                fn(vdomOrNode)
            }
        }

        function addHook(name, cb) {
            if (isUndef(hooksCallback[name])) hooksCallback[name] = []

            hooksCallback[name].push(cb)
        }

        function emitHook(name) {
            if (isUndef(hooksCallback[name])) return

            var cbs = hooksCallback[name],
                args = slice(arguments, 1)

            for (var i = 0, len = cbs.length; i < len; i++) {
                cbs[i].apply(null, args)
            }
        }

        var isFormElem = matchWith("select,textarea,input")

        function handleFormElemAttr(vdom) {
            var tagName = vdom.tagName,
                attrs = vdom.attrs,
                props = vdom.props

            if (isFormElem(tagName)) {
                transplant("value")
                transplant("checked", true)

                if (tagName === "select") {
                    transplant("multiple", true)
                    transplant("selected", true)
                }

                vdom.props = props
            }

            function transplant(name, useBoolean) {
                if (attrs && attrs.hasOwnProperty(name)) {
                    props || (props = {})
                    props[name] = attrs[name]
                }

                if (useBoolean && props && props[name] === "") {
                    props[name] = true
                }
            }
        }

        function setAttribute(element, key, val) {
            if (key === "style") {
                val = styleStringify(val) || null
            }
            else if (key === "class") {
                val = classStringify(val) || null
            }

            if (val == null) {
                element.removeAttribute(key)
            }
            else {
                try {
                    element.setAttribute(key, String(val))
                } catch (e) {
                    logError("VirtualDOM???????????????????????????" + key + "?????????", val, element)
                    logError(e)
                }
            }
        }

        function setProp(element, key, val) {
            if (key === "checked") {
                val = (isUndef(val) || val === false) ? false : true
            }

            element[key] = val
        }

        function setTextContent(element, text) {
            if (isDef(element) && (element.nodeType === 3 || element.nodeType === 8)) {
                var textContent = "textContent" in element ? "textContent" : "data",
                    _text = decodeEntity(text)

                if (/&\w+;/.test(_text)) {
                    _text = createEntityTextNode(text)[textContent]
                }

                if (_text == Undefined) _text = ""

                element[textContent] = _text
            }
        }

        var entityMap = { 'amp': '&', 'gt': '>', 'lt': '<', 'quot': '"', 'apos': "'", 'ldquo': '???', 'rdquo': '???' }

        function decodeEntity(text) {
            if (!isString(text) || text === "") return text

            return text.replace(/&(\w+);/g, function (match, $1) {
                return entityMap[$1] || match
            })
        }

        function createEntityTextNode(text) {
            var textWrap = document.createElement("div")
            textWrap.innerHTML = text
            return textWrap.childNodes[0]
        }

        function isSame(a, b) {
            return a.key === b.key && a.type === b.type && a.tagName === b.tagName && isSameInputType(a, b)
        }

        var isValueInputType = matchWith('text,number,password,search,email,tel,url')

        function isSameInputType(a, b) {
            if (a.tagName !== 'input') return true

            var typeA = a.attrs && a.attrs.type,
                typeB = b.attrs && b.attrs.type
            return typeA === typeB || isValueInputType(typeA) && isValueInputType(typeB)
        }

        function createElement(vdom) {
            var element

            if (vdom.isElement) {
                element = vdom.node || document.createElement(vdom.tagName)

                var attrs = vdom.attrs,
                    props = vdom.props,
                    children = vdom.children

                if (isDef(children)) {
                    addChildren(element, children)
                }

                if (isDef(attrs)) {
                    for (var key in attrs) {
                        var val = attrs[key]
                        setAttribute(element, key, val)
                    }
                }

                if (isDef(props)) {
                    for (var key in props) {
                        var val = props[key]
                        setProp(element, key, val)
                    }
                }
            }
            else if (vdom.isText) {
                var text = vdom.text,
                    _text = decodeEntity(text)

                if (/&\w+/.test(_text)) {
                    element = createEntityTextNode(text)
                }
                else {
                    element = document.createTextNode(_text)
                }
            }
            else if (vdom.isComment) {
                element = document.createComment(vdom.comment)
            }

            return element
        }

        function addChild(parentNode, vdom, ref) {
            if (isUndef(parentNode) || isUndef(vdom)) return

            var refNode = getRefNode(ref)

            if (vdom.isComponent) {
                vdom.component = new Component(vdom.tagName, vdom.componentDefinition)
                vdom.component.create(vdom.componentData)
                vdom.component.mount(parentNode, refNode)
            }
            else if (vdom.isFragment) {
                vdom.element = parentNode
                addChildren(parentNode, vdom.children, Undefined, Undefined, refNode)
                emitHook("create", vdom)
            }
            else {
                var element = createElement(vdom)

                if (isDef(element)) {
                    vdom.element = element
                    vdom.isElement && emitHook("create", vdom)
                    insert(parentNode, element, refNode)
                }
                else {
                    logError("VirtualDOM????????? DOM ????????????", vdom)
                }
            }
        }

        function addChildren(parentNode, vdoms, startIdx, endIdx, ref) {
            isUndef(startIdx) && (startIdx = 0)
            isUndef(endIdx) && (endIdx = vdoms.length - 1)

            var refNode = getRefNode(ref)

            for (var i = startIdx; i <= endIdx; i++) {
                addChild(parentNode, vdoms[i], refNode)
            }
        }

        function removeElement(element) {
            if (isUndef(element)) return

            var parentNode = element.parentNode

            if (isDef(parentNode))
                parentNode.removeChild(element)
        }

        function createRemoveHandle(removeFn) {
            var count = 1 + (hooksCallback.remove ? hooksCallback.remove.length : 0)

            return function remove() {
                if (--count === 0) {
                    removeFn()
                }
            }
        }

        function removeChild(vdom) {
            if (isUndef(vdom)) return

            if (vdom.isComponent) {
                vdom.component.remove()
            }
            else if (vdom.isFragment) {
                var rm = createRemoveHandle(function () {
                    removeChildren(vdom.children)
                })
                rm()
                emitHook("remove", vdom, rm)
            }
            else if (vdom.isElement) {
                /** ?????????????????????????????? remove hook ??????????????????????????? rm ???????????????????????? */
                var rm = createRemoveHandle(function () {
                    removeElement(vdom.element)
                })
                rm()
                emitHook("remove", vdom, rm)
            }
            else {
                removeElement(vdom.element)
            }
        }

        function removeChildren(vdoms, startIdx, endIdx) {
            isUndef(startIdx) && (startIdx = 0)
            isUndef(endIdx) && (endIdx = vdoms.length - 1)

            for (var i = startIdx; i <= endIdx; i++) {
                removeChild(vdoms[i])
            }
        }

        function insert(parentNode, node, refNode) {
            if (isUndef(parentNode) || isUndef(node)) return

            if (isDef(refNode) && refNode.parentNode === parentNode) {
                parentNode.insertBefore(node, refNode)
            }
            else {
                parentNode.appendChild(node)
            }
        }

        function insertChild(parentNode, vdomOrNode, ref) {
            var refNode = getRefNode(ref)

            eachElement(vdomOrNode, function (element) {
                insert(parentNode, element, refNode)
            })
        }

        function getRefNode(vdomOrNode) {
            if (isUndef(vdomOrNode)) return null

            if (vdomOrNode.isComponent) {
                return getRefNode(vdomOrNode.component.getRootNode())
            }
            else if (vdomOrNode.isFragment) {
                return getRefNode(firstChild(vdomOrNode.children))
            }
            else if (vdomOrNode.element) {
                return vdomOrNode.element
            }
            else if (vdomOrNode.nodeType) {
                return vdomOrNode
            }
        }

        function getNextSibling(vdomOrNode) {
            if (isUndef(vdomOrNode)) return null

            if (vdomOrNode.isComponent) {
                return getNextSibling(vdomOrNode.component.getRootNode())
            }
            else if (vdomOrNode.isFragment) {
                return getNextSibling(lastChild(vdomOrNode.children))
            }
            else if (vdomOrNode.element) {
                return vdomOrNode.element.nextSibling
            }
            else if (vdomOrNode.nodeType) {
                return vdomOrNode.nextSibling
            }
        }

        function firstChild(children) {
            for (var i = 0, len = children.length; i < len; i++) {
                if (isDef(children[i])) return children[i]
            }
        }

        function lastChild(children) {
            for (var i = children.length - 1; i >= 0; i--) {
                if (isDef(children[i])) return children[i]
            }
        }

        function createKeyMap(children, startIdx, endIdx) {
            var keyMap = {}
            for (var i = startIdx; i <= endIdx; i++) {
                var vdom = children[i]
                if (isDef(vdom) && isDef(vdom.key)) {
                    keyMap[vdom.key] = i
                }
            }
            return keyMap
        }

        function checkRepeatKey(children) {
            var keys = {}

            for (var i = 0; i < children.length; i++) {
                var vdom = children[i]

                if (isDef(vdom) && isDef(vdom.key)) {
                    if (keys[vdom.key]) {
                        logWarning("VirtualDOM??????????????????????????? key???" + vdom.key + "???")
                    }
                    else {
                        keys[vdom.key] = true
                    }
                }
            }
        }

        function updateAttributes(oldVdom, newVdom) {
            var oldAttrs = oldVdom.attrs || {},
                newAttrs = newVdom.attrs || {},
                element = oldVdom.element

            if (!element) return

            for (var key in oldAttrs) {
                if (isUndef(newAttrs[key])) {
                    setAttribute(element, key, null)
                }
            }

            for (var key in newAttrs) {
                if (oldAttrs[key] !== newAttrs[key]) {
                    setAttribute(element, key, newAttrs[key])
                }
            }
        }

        function updateProps(oldVdom, newVdom) {
            var oldProps = oldVdom.props || {},
                newProps = newVdom.props || {},
                element = oldVdom.element

            if (!element) return

            for (var key in oldProps) {
                if (isUndef(newProps[key])) {
                    setProp(element, key, Undefined)
                }
            }

            for (var key in newProps) {
                if (oldProps[key] !== newProps[key]) {
                    setProp(element, key, newProps[key])
                }
            }
        }

        function patch(parentNode, oldVdom, newVdom, ref) {
            if (isDef(oldVdom) && isDef(newVdom)) {
                if (tryPatch(oldVdom, newVdom)) return
                ref = getNextSibling(oldVdom)
            }

            if (isDef(oldVdom)) {
                removeChild(oldVdom)
            }

            if (isDef(newVdom)) {
                addChild(parentNode, newVdom, ref)
            }
        }

        function patchChildren(parentNode, oldChildren, newChildren, ref) {
            newChildren && checkRepeatKey(newChildren)

            if (isDef(oldChildren) && isDef(newChildren)) {
                var oldStartIdx = 0,
                    newStartIdx = 0,
                    oldEndIdx = oldChildren.length - 1,
                    newEndIdx = newChildren.length - 1,
                    oldKeyMap

                while (oldStartIdx <= oldEndIdx && newStartIdx <= newEndIdx) {
                    var oldChildStartVdom = oldChildren[oldStartIdx],
                        newChildStartVdom = newChildren[newStartIdx],
                        oldChildEndVdom = oldChildren[oldEndIdx],
                        newChildEndVdom = newChildren[newEndIdx]

                    if (isUndef(oldChildStartVdom)) {
                        ++oldStartIdx
                    }
                    else if (isUndef(oldChildEndVdom)) {
                        --oldEndIdx
                    }
                    else if (isUndef(newChildStartVdom)) {
                        ++newStartIdx
                    }
                    else if (isUndef(newChildEndVdom)) {
                        --newEndIdx
                    }
                    else if (tryPatch(oldChildStartVdom, newChildStartVdom)) {
                        ++oldStartIdx
                        ++newStartIdx
                    }
                    else if (tryPatch(oldChildEndVdom, newChildEndVdom)) {
                        --oldEndIdx
                        --newEndIdx
                    }
                    else if (tryPatch(oldChildStartVdom, newChildEndVdom)) {
                        var _ref = getNextSibling(oldChildEndVdom)
                        insertChild(parentNode, newChildEndVdom, _ref)
                        ++oldStartIdx
                        --newEndIdx
                    }
                    else if (tryPatch(oldChildEndVdom, newChildStartVdom)) {
                        insertChild(parentNode, newChildStartVdom, oldChildStartVdom)
                        --oldEndIdx
                        ++newStartIdx
                    }
                    else {
                        if (isUndef(oldKeyMap)) {
                            oldKeyMap = createKeyMap(oldChildren, oldStartIdx, oldEndIdx)
                        }

                        var patchIdx = Undefined

                        if (isDef(newChildStartVdom.key)) {
                            var keyIdx = oldKeyMap[newChildStartVdom.key]

                            if (isDef(keyIdx) && tryPatch(oldChildren[keyIdx], newChildStartVdom)) {
                                patchIdx = keyIdx
                            }
                        }
                        else {
                            for (var i = oldStartIdx + 1; i < oldEndIdx; i++) {
                                var oldChildVdom = oldChildren[i]

                                if (isDef(oldChildVdom) && tryPatch(oldChildVdom, newChildStartVdom)) {
                                    patchIdx = i
                                    break;
                                }
                            }
                        }

                        if (isDef(patchIdx)) {
                            insertChild(parentNode, oldChildren[patchIdx], oldChildStartVdom)
                            oldChildren[patchIdx] = Undefined
                        }
                        else {
                            addChild(parentNode, newChildStartVdom, oldChildStartVdom)
                        }

                        ++newStartIdx
                    }
                }

                if (newStartIdx <= newEndIdx) {// ?????????????????????????????????????????????????????????
                    var _ref = isDef(newChildren[newEndIdx + 1])
                        ? newChildren[newEndIdx + 1]
                        : ref

                    addChildren(parentNode, newChildren, newStartIdx, newEndIdx, _ref)
                }
                else if (oldStartIdx <= oldEndIdx) {// ????????????????????????
                    removeChildren(oldChildren, oldStartIdx, oldEndIdx)
                }
            }
            else if (isDef(newChildren)) {
                addChildren(parentNode, newChildren, 0, newChildren.length - 1, ref)
            }
            else if (isDef(oldChildren)) {
                removeChildren(oldChildren)
            }
        }

        function tryPatch(oldVdom, newVdom) {
            if (oldVdom === newVdom) return true
            if (!isSame(oldVdom, newVdom)) return false

            if (newVdom.isComponent) {
                newVdom.component = oldVdom.component
                newVdom.component.update(newVdom.componentData)
                return true
            }

            var element = newVdom.element = oldVdom.element,
                ref = null

            if (newVdom.isText) {// ????????????
                if (oldVdom.text !== newVdom.text) {
                    setTextContent(element, newVdom.text)
                }
                return true
            }

            if (newVdom.isComment) {// ????????????
                if (oldVdom.comment !== newVdom.comment) {
                    setTextContent(element, newVdom.comment)
                }
                return true
            }

            if (newVdom.isFragment) {
                ref = getNextSibling(oldVdom)
            }

            if (newVdom.isElement) {
                updateAttributes(oldVdom, newVdom)
                updateProps(oldVdom, newVdom)
            }

            emitHook("update", newVdom, oldVdom)

            var oldChildren = oldVdom.children,
                newChildren = newVdom.children

            try {
                patchChildren(element, oldChildren, newChildren, ref)
            } catch (e) {
                logError(e)
            }

            return true
        }
    }

    function Component(require, module, exports) {
        module.exports = Component

        var VirtualDOM = require("VirtualDOM"),
            Parser = require("Parser")

        var component_id = 0,
            ComponentCache = {},
            RenderCache = {}

        function Component(name, options) {
            if (isFunction(options)) {
                options = { initComponent: options }
            }

            this.name = name
            this.option = options
            this.instance = null
            this.asyncLoading = null
            this.state = "init"
        }

        Component.public = {}

        Component.prototype = {
            constructor: Component,
            _createParser: function (config, componentData) {
                return new Parser(config, componentData).__instance__
            },
            _createPlaceholder: function (parentNode, refNode) {
                var placeholder = this.placeholder = VirtualDOM.createComment("Component - [" + this.name + "]")

                VirtualDOM.patch(parentNode, null, placeholder, refNode)

                placeholder.remove = function () {
                    VirtualDOM.patch(parentNode, placeholder)
                }

                return placeholder
            },
            _createError: function (parentNode, refNode) {
                var error = this.option.error

                if (isString(error)) {
                    error = Component.public[error]
                }

                if (!error) return

                if (!isFunction(error) && error.nodeType !== 1) return

                var errorComp = null

                if (isFunction(error)) { /* error ?????? */
                    errorComp = VirtualDOM.createComponent("error", error, {
                        name: "error",
                        parentContext: this.componentData.parentContext,
                        vdom: this.componentData.vdom,
                        domEventManager: this.componentData.domEventManager,
                        complete: this.componentData.complete
                    })
                }
                else { /* DOM ?????? */
                    errorComp = VirtualDOM.createElementWithNode(error)
                }

                VirtualDOM.patch(parentNode, null, errorComp, refNode)

                errorComp.remove = function () {
                    VirtualDOM.patch(parentNode, errorComp)
                }

                this.errorComp = errorComp
            },
            _createLoading: function (parentNode, refNode) {
                var _self = this,
                    loading = this.option.loading,
                    delay = this.option.loadingDelay,
                    duration = this.option.loadingMinDuration

                if (isString(loading)) {
                    loading = Component.public[loading]
                }

                if (!loading) return

                if (!isFunction(loading) && loading.nodeType !== 1) return

                function create() {
                    if (!_self.asyncLoading) return

                    var loadingComp = null

                    if (isFunction(loading)) { /* loading ?????? */
                        loadingComp = VirtualDOM.createComponent("loading", loading, {
                            name: "loading",
                            parentContext: _self.componentData.parentContext,
                            vdom: _self.componentData.vdom,
                            domEventManager: _self.componentData.domEventManager
                        })
                    }
                    else { /* DOM ?????? */
                        loadingComp = VirtualDOM.createElementWithNode(loading)
                    }

                    VirtualDOM.patch(parentNode, null, loadingComp, refNode)

                    loadingComp.remove = function () {
                        VirtualDOM.patch(parentNode, loadingComp)
                    }

                    _self.loadingComp = loadingComp

                    if (duration) {
                        _self.loadingDuration = Promise.delay(duration)
                    }
                }

                delay ? setTimeout(create, delay) : create()
            },
            _callError: function (errMessage) {
                this.instance = null

                errMessage = "Component:???" + this.name + "???" + errMessage

                isFunction(this._errCallback) && this._errCallback(errMessage)

                logError.apply(null, [errMessage].concat(slice(arguments, 1)))
            },
            create: function (componentData) {
                if (this.state !== "init") return

                if (isUndef(componentData)) {
                    return this._callError("?????????????????????")
                }

                if (!isObject(componentData)) {
                    return this._callError("????????????????????????", componentData)
                }

                this.componentData = componentData
                this._errCallback = componentData.complete

                var _self = this,
                    option = this.option,
                    initComponent = isFunction(option.lazyLoad)
                        ? option.lazyLoad()
                        : option.initComponent

                if (initComponent instanceof Promise) {
                    this.asyncLoading = new Promise(function (resolve) {
                        var tid = null

                        if (option.timeout) {
                            tid = setTimeout(function () {
                                tid = null
                                _self._callError("????????????????????????")
                                resolve()
                            }, option.timeout)
                        }

                        initComponent.then(function () {
                            tid && clearTimeout(tid)
                            return _self.loadingDuration
                        }).then(function () {
                            _self.asyncLoading = _self.loadingDuration = null
                            _self.create(componentData)
                            resolve()
                        })["catch"](function (err) {
                            tid && clearTimeout(tid)
                            _self._callError("????????????????????????", err)
                            resolve()
                        })
                    })
                }
                else {
                    if (!initComponent) {
                        return this._callError("???????????????")
                    }

                    if (!isFunction(initComponent)) {
                        return this._callError("??????????????????????????????")
                    }

                    var id = initComponent.id || (initComponent.id = ++component_id),
                        store = componentData.store,
                        tuple = ComponentCache[id],
                        configCache = tuple && tuple[0],
                        storeCache = tuple && tuple[1],
                        render = RenderCache[id],
                        config

                    if (configCache && storeCache === store) {
                        config = configCache
                    }
                    else {
                        var ctx = { store: store }

                        config = initComponent(ctx)
                        ComponentCache[id] = [config, store]

                        delete config.el
                    }

                    if (render) {
                        config.__render__ = render
                    }

                    var instance = this.instance = null

                    try {
                        instance = this.instance = this._createParser(config, componentData)

                        if (!render) {
                            RenderCache[id] = instance.render
                        }
                    } catch (err) {
                        this._callError("??????????????????", err)
                    }
                }
            },
            mount: function (parentNode, refNode) {
                if (this.state !== "init") return

                if (this.asyncLoading) { // ?????????????????????
                    if (this.placeholder) return

                    var _self = this,
                        placeholder = this._createPlaceholder(parentNode, refNode)

                    this._createLoading(parentNode, placeholder)

                    this.asyncLoading
                        .then(this.mount.bind(this, parentNode, placeholder)) // ???????????????????????????????????????
                        .then(function () {
                            if (_self.loadingComp) {
                                _self.loadingComp.remove()
                                _self.loadingComp = null
                            }
                        })
                }
                else if (this.instance) { // ????????????????????????
                    this.state = "success"
                    this.instance.mount(parentNode, refNode)

                    if (this.placeholder) {
                        this.placeholder.remove()
                        this.placeholder = null
                    }
                }
                else { // ????????????????????????
                    this.state = "fail"
                    this._createError(parentNode, refNode)

                    if (this.errorComp && this.placeholder) {
                        this.placeholder.remove()
                        this.placeholder = null
                    }
                    else if (!this.errorComp && !this.placeholder) {
                        this._createPlaceholder(parentNode, refNode)
                    }
                }
            },
            update: function (componentData) {
                if (this.state === "remove") return

                if (!isObject(componentData)) {
                    this._callError("componentData ???????????????")
                }

                this.componentData = componentData

                if (this.asyncLoading) {
                    this.asyncLoading.then(this.update.bind(this, componentData))
                }
                else if (this.instance) {
                    this.instance.updateComponent(componentData)
                }
            },
            remove: function () {
                if (this.state === "remove") return

                this.state = "remove"

                if (this.asyncLoading) {
                    this.placeholder.remove()
                }
                else if (this.instance) {
                    this.instance.destroy()
                }
                else {
                    this.errorComp && this.errorComp.remove()
                    this.placeholder && this.placeholder.remove()
                }
            },
            getRootNode: function () {
                if (this.asyncLoading) {
                    return this.loading ? VirtualDOM.createFragment([this.loading, this.placeholder]) : this.placeholder
                }
                else if (this.instance) {
                    return this.instance.vdom
                }
                else {
                    return this.errorComp || this.placeholder
                }
            }
        }

        VirtualDOM.useComponent(Component)
    }

    function ComponentLibrary(require, module, exports) {
        exports.importComponent = importComponent
        exports.registerComponent = registerComponent
        exports.exportComponent = exportComponent

        var Component = require("Component")

        var componentSpaces = {},
            isDocReady = false,
            onDocReady = new Promise(function (resolve) {
                if (document.addEventListener) {
                    document.addEventListener("DOMContentLoaded", function onready() {
                        document.removeEventListener("DOMContentLoaded", onready)
                        ready()
                    }, false)
                }
                else if (window.doScroll && window.frameElement == null) {
                    var doc = document.documentElement

                    !function doScroll() {
                        try {
                            doc.doScroll("left")
                        } catch (err) {
                            return setTimeout(doScroll, 30)
                        }

                        ready()
                    }()
                }
                else {
                    /**
                     * ?????? doScroll ??? iframe ??????????????? doScroll ???
                     */
                    setTimeout(ready, 1000)

                    document.attachEvent("onreadystatechange", function onready() {
                        if (document.readyState === "complete") {
                            document.detachEvent("onreadystatechange", onready)
                            ready()
                        }
                    })
                }

                function ready() {
                    isDocReady = true
                    resolve()
                }
            })

        function importComponent(name, url, options) {
            if (!isString(name)) throw logError("importComponent??????????????? name")
            if (!isString(url)) throw logError("importComponent??????????????? url")

            options = Object.assign({
                loading: null,
                error: null,
                timeout: 0,
                lazy: false,
                loadingDelay: 200,
                loadingMinDuration: 200
            }, options, {
                lazyLoad: Undefined,
                initComponent: Undefined
            })

            url = url.replace(location.protocol, "")
            location.host && (url = url.replace("//" + location.host, ""))

            var componentSpace = componentSpaces[url],
                isLazy = Boolean(options && options.lazy)

            if (!componentSpace && !isLazy) {
                componentSpace = loadComponentLibrary(url)
            }

            if (componentSpace instanceof Promise) {
                options.initComponent = componentSpace.then(function (componentSpace) {
                    /**
                     * ?????????????????????????????????????????????????????????????????????????????????????????????????????????
                     */
                    return options.initComponent = componentSpace[name]
                })
            }
            else if (componentSpace) {
                options.initComponent = componentSpace[name]
            }
            else if (isLazy) {
                options.lazyLoad = function () {
                    options.lazy = false
                    options.lazyLoad = Undefined

                    var _options = importComponent(name, url, options)

                    if (_options.initComponent instanceof Promise) {
                        return options.initComponent = _options.initComponent.then(function (initComponent) {
                            options.initComponent = initComponent
                        })
                    }
                    else {
                        return options.initComponent = _options.initComponent
                    }
                }
            }

            return options
        }

        function loadComponentLibrary(url) {
            return componentSpaces[url] = onDocReady.then(function () {
                return new Promise(function (resolve) {
                    var script = document.createElement("script")

                    if ("onreadystatechange" in script) {
                        /**
                         * ??? IE ??????????????????????????? script ??????????????? script ??? onreadystatechange/onload ??????????????????????????? script ????????????????????????
                         * ??????????????????????????? marcotask ???????????????????????? script ???????????????????????? marcotask ??????????????????
                         */
                        defer(function () {
                            script.src = url
                            script.onreadystatechange = function () {
                                var readyState = script.readyState
                                if (readyState === "complete" || readyState === "loaded") {
                                    onload()
                                }
                            }
                            document.body.appendChild(script)
                        }, 5)
                    }
                    else if ("onload" in script) {
                        script.src = url
                        script.onload = onload
                        script.onerror = onload
                        document.body.appendChild(script)
                    }

                    function onload() {
                        var componentSpace = {},
                            success = exportComponentsTo(componentSpace)

                        if (!success) logError("importComponent?????????????????????" + url + "?????????")

                        componentSpaces[url] = componentSpace
                        resolve(componentSpace)

                        script.onload = script.onreadystatechange = null
                        document.body.removeChild(script)
                    }
                })
            })
        }

        function registerComponent(name, component, options) {
            if (!isFunction(component)) {
                return logError("registerComponent???????????????????????????????????????" + name + "????????????????????????")
            }

            var componentSpace = componentSpaces["global"] || (componentSpaces["global"] = Component.public)

            handleComponent(name, component, options, componentSpace)
        }

        var exportCallbacks = null

        function exportComponent(name, component, options) {
            if (!isFunction(component)) {
                return logError("exportComponent?????????????????????????????????" + name + "????????????????????????")
            }

            if (!isDocReady) {
                /**
                 * ?????? js ???????????????????????? exportComponent ???????????????????????????????????????????????? html ????????? script ?????????????????????
                 */
                var scripts = document.querySelectorAll("script"),
                    componentScript = scripts[scripts.length - 1],
                    url = componentScript.getAttribute("src"),
                    componentSpace = componentSpaces[url] || (componentSpaces[url] = {})

                handleComponent(name, component, options, componentSpace)
            }
            else {
                if (!exportCallbacks) {
                    exportCallbacks = []
                }

                exportCallbacks.push(function exportComponentTo(componentSpace) {
                    handleComponent(name, component, options, componentSpace)
                })
            }
        }

        function exportComponentsTo(componentSpace) {
            if (!exportCallbacks) return

            exportCallbacks.forEach(function (exportComponentTo) {
                exportComponentTo(componentSpace)
            })

            exportCallbacks = null

            return true
        }

        function handleComponent(name, component, options, componentSpace) {
            componentSpace[name] = function initComponent() {
                var config = component.apply(null, arguments)

                if (options && options.style) {
                    config.style = options.style
                }

                return config
            }
        }

        var defer = function () {
            var times = 0

            return function (fn, interval) {
                var times$ = ++times

                isUndef(interval) && (interval = 5)

                if (times$ === 1) {
                    fn()
                    setTimeout(function () {
                        reset(times$)
                    })
                } else {
                    setTimeout(function () {
                        fn()
                        reset(times$)
                    }, interval * (times$ - 1))
                }
            }

            function reset(times$) {
                var isLast = times === times$
                if (isLast) times = 0
            }
        }()
    }

    function Observer(require, module, exports) {
        module.exports = Observer

        var utils = require("utils"),
            pathResolve = utils.pathResolve

        utils = null

        var $$dep_id = 0,
            CIRCULAR_THRESHOLD = isIE ? Infinity : 100,
            Reg$TestNested = /[.\[]/

        function Observer() {
            this.obs = null
            this.deepObs = null
            this.deepMarks = null
        }

        Observer.prototype = {
            constructor: Observer,
            observe: function (keyPaths) {
                keyPaths = isArray(keyPaths) ? keyPaths : slice(arguments)

                if (!keyPaths.length) return noop.deep = noop, noop

                var observer = this,
                    keys = [],
                    deepKeys = [],
                    deepMarkKeys = []

                for (var i = 0, len = keyPaths.length; i < len; i++) {
                    var keyPath = keyPaths[i],
                        isNesting = Reg$TestNested.test(keyPath)

                    if (isNesting) {
                        var pathKeys = pathResolve(keyPath),
                            maxIndex = pathKeys.length - 1,
                            pathKeys$ = []

                        for (var j = 0; j <= maxIndex; j++) {
                            pathKeys$.push(pathKeys[j])

                            var key = genObserveKey(pathKeys$)

                            keys.push(key)

                            if (j === 0) deepMarkKeys.push(key)
                            if (j === maxIndex) deepKeys.push(key)
                        }
                    }
                    else {
                        keys.push(keyPath)
                        deepMarkKeys.push(keyPath)
                        deepKeys.push(keyPath)
                    }
                }

                keys = distinct(keys)
                deepKeys = distinct(deepKeys)
                deepMarkKeys = distinct(deepMarkKeys)

                function distinct(arr) {
                    var map = {}
                    return arr.filter(function (o) {
                        return map[o] ? false : map[o] = 1
                    })
                }

                function onupdate(fn) {
                    if (!isFunction(fn)) return

                    var dependent = createDependent(fn),
                        obs = observer.obs || (observer.obs = {})

                    keys.forEach(function (key) {
                        var dependents = obs[key] || (obs[key] = [])

                        dependents.push(dependent)
                    })

                    return function release() {
                        releaseDependent(obs, keys, dependent)
                    }
                }

                function onupdate_deep(fn) {
                    if (!isFunction(fn)) return

                    var dependent = createDependent(fn),
                        deepObs = observer.deepObs || (observer.deepObs = {}),
                        release = onupdate(dependent)

                    deepKeys.forEach(function (key) {
                        var dependents = deepObs[key] || (deepObs[key] = [])

                        dependents.push(dependent)
                    })

                    /**
                     * ????????????????????????????????????????????? key ?????????????????? update ?????????????????????????????????????????????????????????
                     * ?????????
                     * ???????????? ???a.b??? ?????????a??? ????????????????????????
                     * ??? update ???a.b.c.d??? ???????????? ???a??? ???????????????????????????????????????????????????
                     * ??? update ???x.y.z??? ???????????? ???x??? ??????????????????????????????????????????????????????
                     */
                    if (deepMarkKeys) {
                        var deepMarks = observer.deepMarks || (observer.deepMarks = {})

                        deepMarkKeys.forEach(function (markKey) {
                            deepMarks[markKey] = true
                        })

                        deepMarkKeys = null
                    }

                    return function release_deep() {
                        release()
                        releaseDependent(deepObs, deepKeys, dependent)
                    }
                }

                onupdate.deep = onupdate_deep

                return onupdate
            },
            update: function (keyPaths) {
                if (!this.obs) return

                keyPaths = isArray(keyPaths) ? keyPaths : slice(arguments)

                var obs = this.obs,
                    deepObs = this.deepObs,
                    deepMarks = this.deepMarks,
                    once = this.once || (this.once = {}),
                    queue = this.queue || []

                for (var i = 0, len = keyPaths.length; i < len; i++) {
                    var keyPath = keyPaths[i],
                        isNesting = Reg$TestNested.test(keyPath),
                        key = isNesting ? genObserveKey(keyPath) : keyPath

                    addTaskForKeyPath(keyPath, obs[key])

                    if (!deepObs || !isNesting) continue

                    var pathKeys = pathResolve(keyPath),
                        maxIndex = pathKeys.length - 1,
                        pathKeys$ = []

                    if (!deepMarks || !deepMarks[pathKeys[0]]) {
                        continue
                    }

                    for (var j = 0; j < maxIndex; j++) {
                        pathKeys$.push(pathKeys[j])

                        var deepKey = genObserveKey(pathKeys$)

                        addTaskForKeyPath(keyPath, deepObs[deepKey])
                    }
                }

                /**
                 * ?????????????????????????????????????????????????????????????????????????????????
                 */
                var updateRecord = this.updateRecord || (this.updateRecord = [])
                updateRecord.push(keyPaths.join())

                if (!this.queue) {
                    var circular = null

                    this.queue = queue

                    for (var m = 0; m < queue.length; m++) {
                        var task = queue[m]

                        if (updateRecord.length > CIRCULAR_THRESHOLD && (circular = checkCircular(updateRecord))) {
                            logError("Observer???????????????????????????????????????????????????" + circular.path.join("->") + "???,???????????????" + circular.times + "???")

                            break
                        }

                        isFunction(task) && task()
                    }

                    this.queue = this.once = null

                    /**
                     * ?????????????????????????????????????????????
                     */
                    nextTick(function () {
                        this.updateRecord = null
                    }, this)
                }

                function addTaskForKeyPath(keyPath, dependents) {
                    if (isUndef(dependents)) return

                    dependents.forEach(function (dependent) {
                        var dep_id = dependent.dep_id

                        if (once[dep_id]) {
                            once[dep_id].push(keyPath)
                            return
                        }
                        else {
                            once[dep_id] = [keyPath]
                        }

                        queue.push(function task() {
                            var causes = once[dep_id]

                            delete once[dep_id]

                            dependent(causes)
                        })
                    })
                }
            }
        }

        function createDependent(fn) {
            if (isDef(fn.dep_id)) return fn

            dependent.dep_id = ++$$dep_id

            function dependent(causes) {
                if (dependent.__released) return

                try {
                    fn(causes)
                } catch (err) {
                    console.error(err)
                }
            }

            return dependent
        }

        function releaseDependent(obs, keys, dependent) {
            dependent.__released = true

            keys.forEach(function (key) {
                var dependents = obs[key]

                obs[key] = dependents.filter(function (f) {
                    return f !== dependent
                })
            })
        }

        function checkCircular(updateRecord) {
            var nodes = updateRecord.nodes || (updateRecord.nodes = {}),
                path = updateRecord.path || "",
                circularPath = updateRecord.circularPath || "",
                startIndex = updateRecord.startIndex || 0,
                len = updateRecord.length,
                wholePath = ""

            if (len - startIndex < 30) return // ????????????????????????????????????????????? 30 ????????????

            for (var i = startIndex; i < len - 1; i++) {
                var a = updateRecord[i],
                    b = updateRecord[i + 1],
                    aNode = nodes[a] || (nodes[a] = {}),
                    bNode = nodes[b] || (nodes[b] = {})

                path += a + "#"

                if (aNode[b]) {
                    circularPath += a + "#"

                    if (!~path.lastIndexOf(circularPath + circularPath)) continue

                    wholePath || (wholePath = updateRecord.join("#") + "#")

                    var circularReg = new RegExp("(?:" + circularPath + ")+"),
                        matcher = wholePath.match(circularReg),
                        matchPath = matcher[0],
                        maxLen = matcher.index + matchPath.length,
                        times = 0

                    if (
                        wholePath.length - maxLen < circularPath.length &&
                        (times = matchPath.split(circularPath).length - 1) > 10
                    ) {
                        return {
                            path: circularPath.replace(/#$/, "").split("#"),
                            times: times
                        }
                    }
                }
                else {
                    aNode[b] = bNode
                    circularPath = ""
                }
            }

            updateRecord.path = path
            updateRecord.circularPath = circularPath
            updateRecord.startIndex = i
        }

        function genObserveKey(keyPath) {
            var pathKeys = isArray(keyPath) ? keyPath : pathResolve(keyPath)

            return pathKeys.join("/")
        }
    }

    function EventManager(require, module, exports) {
        module.exports = EventManager

        var isNonBubbleType = isLowIE
            ? matchWith("scroll,focus,blur,mouseenter,mouseleave,propertychange,change")
            : matchWith("scroll,focus,blur,mouseenter,mouseleave,propertychange"),
            isCheckInputType = matchWith('checkbox,radio'),
            isSupportsPassive = false,
            id$ = 0

        if (Object.defineProperty) {
            try {
                var opts = {}
                Object.defineProperty(opts, 'passive', ({
                    get: function get() {
                        isSupportsPassive = true
                    }
                }))
                window.addEventListener('test-passive', null, opts)
            } catch (e) { }
        }

        function EventManager(delegateNode) {
            if (delegateNode.__eventManager__) return delegateNode.__eventManager__

            this.eventListeners = {}
            this.delegateNode = delegateNode
            this.delegate_id = ++id$
            delegateNode.__eventManager__ = this
        }

        EventManager.prototype = {
            constructor: EventManager,
            set: function (node, eventInfos) {
                if (!node) return
                this.setup(eventInfos)
                this.updateListeners(node, eventInfos)
            },
            remove: function (node) {
                if (!node) return
                this.updateListeners(node)
            },
            addListener: function (node, listener) {
                var type = listener.type,
                    realType = listener.realType

                if (listener.isDelegate) {
                    var delegateCount = listener.delegateCount || (listener.delegateCount = { count: 0 }),
                        id = node.__event_id || (node.__event_id = ++id$)

                    if (!delegateCount[id]) {
                        delegateCount[id] = true
                        delegateCount.count++
                    }

                    if (listener.listening) return

                    addListener(this.delegateNode, realType, listener, listener.isCapture, listener.isPassive)

                    listener.listening = true
                }
                else if (!node["event_" + type]) {
                    addListener(node, realType, listener, listener.isCapture, listener.isPassive)

                    node["event_" + type] = true

                    /**
                     * IE8 ??????????????? onpropertychange ??????????????????????????????????????????
                     */
                    if (isIE8 && realType === "propertychange" && node.nodeName.toLowerCase() === "input") {
                        node.value = node.value
                    }
                }
            },
            removeListener: function (node, listener) {
                var type = listener.type,
                    realType = listener.realType

                if (listener.isDelegate) {
                    if (!listener.listening) return

                    var delegateCount = listener.delegateCount,
                        id = node.__event_id

                    if (delegateCount[id]) {
                        delete delegateCount[id]
                        delegateCount.count--
                    }

                    if (delegateCount.count > 0) return

                    node = this.delegateNode

                    removeListener(node, realType, listener, listener.isCapture)

                    listener.listening = false
                    delete listener.delegateCount
                }
                else if (node["event_" + type]) {
                    removeListener(node, realType, listener, listener.isCapture)

                    node["event_" + type] = Undefined
                }
            },
            updateListeners: isLowIE ? updateListenersForIE : function (node, eventInfos) {
                var eventListeners = this.eventListeners,
                    isRemove = !eventInfos,
                    nodeEvents = isRemove ? node.events : node.events = { delegate_id: this.delegate_id }

                if (!nodeEvents) return

                if (!isRemove) {
                    for (var i = 0, len = eventInfos.length; i < len; i++) {
                        var eventInfo = eventInfos[i],
                            type = eventInfo.type,
                            mode = eventInfo.mode,
                            useCapture = false,
                            usePassive = false

                        if (mode) {
                            useCapture = Boolean(mode.capture)
                            usePassive = isSupportsPassive && Boolean(mode.passive)

                            if (useCapture) type = "!" + type
                            if (usePassive) type = "&" + type
                        }

                        var typeEventInfos = nodeEvents[type] || (nodeEvents[type] = [])

                        typeEventInfos.push(eventInfo)
                    }
                }

                for (var type in nodeEvents) {
                    if (type === "delegate_id") continue

                    var listener = eventListeners[type]

                    if (isRemove) {
                        listener && this.removeListener(node, listener)
                    }
                    else {
                        if (!listener) {
                            listener = eventListeners[type] = this.createListener(type)
                        }
                        this.addListener(node, listener)
                    }
                }
            },
            createListener: isLowIE ? createListenerForIE : function (type) {
                var manager = this,
                    isCapture = Boolean(~type.indexOf("!")),
                    isPassive = Boolean(~type.indexOf("&")),
                    realType = (isCapture || isPassive) ? type.replace(/[!&]/g, "") : type,
                    isDelegate = !isPassive && !isNonBubbleType(realType)

                function listener(rawEvent) {
                    var target = rawEvent.target || rawEvent.srcElement,
                        e = new EventCopy(rawEvent)

                    if (isDelegate) {
                        var root = manager.delegateNode,
                            delegate_id = manager.delegate_id,
                            node = target,
                            nodeEventList = []

                        while (node && node !== root && node.nodeType === 1) {
                            if (node.events && node.events.delegate_id === delegate_id && node.events[type]) {
                                var typeEventInfos = node.events[type]

                                if (typeEventInfos.length) {
                                    typeEventInfos.target = node
                                    nodeEventList.push(typeEventInfos)
                                }
                            }

                            node = node.parentNode
                        }

                        for (var i = 0, max = nodeEventList.length - 1; i <= max; i++) {
                            if (!isCapture && e.isStopPropagation) return

                            var typeEventInfos = nodeEventList[isCapture ? max - i : i]

                            e.target = typeEventInfos.target

                            manager.run(typeEventInfos, e)
                        }
                    }
                    else if (target.events && target.events[type]) {
                        var typeEventInfos = target.events[type]

                        manager.run(typeEventInfos, e)
                    }
                }

                listener.isDelegate = isDelegate
                listener.isPassive = isPassive
                listener.isCapture = isCapture
                listener.type = type
                listener.realType = realType

                return listener
            },
            run: function (eventInfos, e) {
                for (var i = 0; i < eventInfos.length; i++) {
                    if (e.isStopImmediatePropagation) return

                    var eventInfo = eventInfos[i],
                        handler = eventInfo.handler

                    handler(e)
                }
            },
            setup: function () {
                var setup = {}

                if (isLowIE) {
                    setup.change = function (eventInfo, eventInfos) {
                        replaceHandler(eventInfo, function (e, handler) {
                            var node = e.target,
                                eventType = e.type,
                                isInput = node.nodeName.toLowerCase() === "input",
                                inputType = isInput ? node.getAttribute("type") || "text" : ""

                            if (isInput && isCheckInputType(inputType)) {
                                if (eventType === "propertychange") {
                                    var pname = e.rawEvent.propertyName

                                    if (pname !== "checked") return
                                    if (inputType === "radio" && !e.target.checked) return

                                    handler(e)
                                }
                            }
                            else if (eventType === "change") {
                                handler(e)
                            }
                        })

                        eventInfo = Object.assign({}, eventInfo)

                        eventInfo.type = "propertychange"
                        eventInfos.push(eventInfo)
                    }

                    setup.input = function (eventInfo, eventInfos) {
                        replaceHandler(eventInfo, function (e, handler) {
                            var pname = e.rawEvent.propertyName

                            if (pname !== "value") return

                            handler(e)
                        })

                        eventInfo.type = "propertychange"
                    }
                }
                else {
                    setup.input = function (eventInfo, eventInfos) {
                        if (eventInfo.mode && eventInfo.mode.ignoreIME) {
                            var IME = false

                            eventInfos.push({
                                type: "compositionstart",
                                handler: function () {
                                    IME = true
                                }
                            })

                            eventInfos.push({
                                type: "compositionend",
                                handler: function () {
                                    IME = false
                                }
                            })

                            replaceHandler(eventInfo, function (e, handler) {
                                setTimeout(function () {
                                    if (IME) return

                                    handler(e)
                                })
                            })
                        }
                    }
                }

                function replaceHandler(eventInfo, handlerProxy) {
                    var handler = eventInfo.handler

                    eventInfo.handler = function (e) {
                        return handlerProxy(e, handler)
                    }
                }

                return function (eventInfos) {
                    for (var i = 0, len = eventInfos.length; i < len; i++) {
                        var eventInfo = eventInfos[i],
                            type = eventInfo.type

                        if (setup[type]) {
                            setup[type](eventInfo, eventInfos)
                        }
                    }
                }
            }()
        }

        function updateListenersForIE(node, eventInfos) {
            var eventListeners = this.eventListeners,
                isRemove = !eventInfos,
                nodeEvents = isRemove ? node.events : node.events = { delegate_id: this.delegate_id },
                captureRecord = this.captureRecord || (this.captureRecord = {})

            if (!nodeEvents) return

            if (!isRemove) {
                for (var i = 0, len = eventInfos.length; i < len; i++) {
                    var eventInfo = eventInfos[i],
                        type = eventInfo.type,
                        mode = eventInfo.mode,
                        useCapture = false

                    if (mode) {
                        useCapture = Boolean(mode.capture)
                    }

                    var eventPhase = nodeEvents[type] || (nodeEvents[type] = {}),
                        typeEventInfos = useCapture
                            ? eventPhase.capture || (eventPhase.capture = [])
                            : eventPhase.bubble || (eventPhase.bubble = [])

                    typeEventInfos.push(eventInfo)
                }
            }

            for (var type in nodeEvents) {
                if (type === "delegate_id") continue

                var listener = eventListeners[type],
                    hasCapture = Boolean(nodeEvents[type].capture)

                if (isRemove) {
                    listener && this.removeListener(node, listener)
                }
                else {
                    if (!listener) {
                        listener = eventListeners[type] = this.createListener(type)
                    }
                    this.addListener(node, listener)
                }

                if (hasCapture) {
                    captureRecord[type] = (captureRecord[type] || 0) + (isRemove ? -1 : 1)
                }
            }
        }

        function createListenerForIE(type) {
            var manager = this,
                isDelegate = !isNonBubbleType(type)

            function listener(rawEvent) {
                var hasCapture = manager.captureRecord && manager.captureRecord[type] > 0,
                    enterCapturePhase = hasCapture && !rawEvent.runCapturePhase,
                    bubbleNodeEventList = null,
                    target = rawEvent.target || rawEvent.srcElement,
                    e = new EventCopy(rawEvent)

                /**
                 * ?????????????????????
                 * ???????????????????????????????????????????????????????????????????????????????????????????????????????????????????????????????????????????????????
                 * ???????????????????????????????????? runCapturePhase ??????????????????????????????????????????
                 */
                if (enterCapturePhase) {
                    var root = document.body,
                        node = target,
                        bubbleRoot = manager.delegateNode,
                        isReachBubbleRoot = node === bubbleRoot,
                        captureNodeEventList = []

                    e.eventPhase = 1
                    bubbleNodeEventList = []
                    rawEvent.runCapturePhase = true

                    while (node && node !== root && node.nodeType === 1) {
                        if (node.events && node.events[type]) {
                            var eventPhase = node.events[type],
                                captureEventInfos = eventPhase.capture,
                                bubbleEventInfos = eventPhase.bubble

                            if (captureEventInfos && captureEventInfos.length) {
                                captureEventInfos.target = node
                                captureNodeEventList.push(captureEventInfos)
                            }

                            if (isDelegate) {
                                if (!isReachBubbleRoot) {
                                    isReachBubbleRoot = bubbleRoot === node
                                }

                                if (!isReachBubbleRoot && bubbleEventInfos && bubbleEventInfos.length) {
                                    bubbleEventInfos.target = node
                                    bubbleNodeEventList.push(bubbleEventInfos)
                                }
                            }
                        }

                        node = node.parentNode
                    }

                    for (var i = captureNodeEventList.length - 1; i >= 0; i--) {
                        var typeEventInfos = captureNodeEventList[i]

                        e.target = typeEventInfos.target

                        manager.run(typeEventInfos, e)
                    }

                    e = new EventCopy(rawEvent)
                }

                if (isDelegate) {
                    if (!bubbleNodeEventList) {
                        var root = manager.delegateNode,
                            delegate_id = manager.delegate_id,
                            node = target

                        bubbleNodeEventList = []

                        while (node && node !== root && node.nodeType === 1) {
                            if (node.events && node.events.delegate_id === delegate_id && node.events[type]) {
                                var eventPhase = node.events[type],
                                    bubbleEventInfos = eventPhase.bubble

                                if (bubbleEventInfos && bubbleEventInfos.length) {
                                    bubbleEventInfos.target = node
                                    bubbleNodeEventList.push(bubbleEventInfos)
                                }
                            }

                            node = node.parentNode
                        }
                    }

                    for (var i = 0; i < bubbleNodeEventList.length; i++) {
                        if (e.isStopPropagation) return

                        var typeEventInfos = bubbleNodeEventList[i]

                        e.target = typeEventInfos.target

                        manager.run(typeEventInfos, e)
                    }
                }
                else if (target.events && target.events[type]) {
                    var eventPhase = target.events[type],
                        typeEventInfos = eventPhase.bubble

                    manager.run(typeEventInfos, e)
                }
            }

            listener.isDelegate = isDelegate
            listener.isPassive = false
            listener.isCapture = false
            listener.type = type
            listener.realType = type

            return listener
        }

        function EventCopy(e) {
            var type = e.type,
                typeProps = this._matchKeyBoard.test(type)
                    ? this._keyboardProps
                    : this._matchMouse.test(type)
                        ? this._mouseProps
                        : null,
                props = typeProps ? this._baseProps.concat(typeProps) : this._baseProps

            for (var i = 0; i < props.length; i++) {
                var prop = props[i]

                this[prop] = e[prop]
            }

            this.target || (this.target = this.srcElement || document)
            this.metaKey = Boolean(this.metaKey)
            this.rawEvent = e
        }

        EventCopy.prototype = {
            constructor: EventCopy,
            _matchKeyBoard: /^key/,
            _matchMouse: /^(?:mouse|contextmenu)|click/,
            _baseProps: "altKey bubbles cancelBubble cancelable composed ctrlKey currentTarget defaultPrevented detail eventPhase isTrusted metaKey path repeat returnValue relatedNode relatedTarget shiftKey srcElement target timeStamp type view which".split(" "),
            _mouseProps: "button buttons clientX clientY fromElement layerX layerY movementX movementY offsetX offsetY pageX pageY screenX screenY toElement x y".split(" "),
            _keyboardProps: "code char charCode key keyCode location isComposing".split(" "),
            preventDefault: function () {
                var e = this.rawEvent

                e.preventDefault && e.preventDefault()
                e.returnValue = false
            },
            stopPropagation: function () {
                var e = this.rawEvent

                this.isStopPropagation = true

                e.stopPropagation && e.stopPropagation()
                e.cancelBubble = true
            },
            stopImmediatePropagation: function () {
                var e = this.rawEvent

                this.isStopImmediatePropagation = true

                e.stopImmediatePropagation && e.stopImmediatePropagation()
                this.stopPropagation()
            }
        }

        function addListener(node, type, listener, capture, passive) {
            !isLowIE
                ? node.addEventListener(type, listener, isSupportsPassive ? { capture: capture, passive: passive } : capture)
                : node.attachEvent('on' + type, listener)
        }

        function removeListener(node, type, listener, capture) {
            !isLowIE
                ? node.removeEventListener(type, listener, capture)
                : node.detachEvent('on' + type, listener)
        }
    }

    function EventCenter(require, module, exports) {
        module.exports = EventCenter

        function EventCenter(config) {
            var defConfig = {
                useOffline: false,
                context: null
            }

            this.config = Object.assign({}, defConfig, config)
            this.cache = {}
            this.offlineActionsMap = {}
        }

        EventCenter.prototype = {
            constructor: EventCenter,
            listen: function (key, fn, context, last) {
                var cache = this.cache,
                    listener = { fn: fn, context: context }

                if (!cache[key]) cache[key] = []

                cache[key].push(listener)
                this.config.useOffline && this._triggerOffline(key, last)
            },
            trigger: function (key) {
                var _self = this,
                    args = slice(arguments),
                    action = function () {
                        _self._trigger.apply(_self, args)
                    }

                this.cache[key] ? action() : (this.config.useOffline && this._addOffline(key, action))
            },
            remove: function (key, fn) {
                var _self = this

                if (this._trigging) return void Promise.resolve().then(function () { _self.remove(key, fn) })

                var cache = this.cache, listeners = cache[key]

                if (listeners) {
                    if (fn) {
                        for (var i = 0, len = listeners.length; i < len; i++) {
                            var listener = listeners[i]

                            if (listener.fn === fn) {
                                listeners.splice(i, 1)
                                break;
                            }
                        }
                    }
                    else {
                        cache[key] = null;
                    }
                }
            },
            _trigger: function (key) {
                var args = slice(arguments, 1),
                    listeners = this.cache[key],
                    gContext = this.config.context

                if (!listeners || !listeners.length) return

                this._trigging = true
                listeners.forEach(function (listener) {
                    var fn = listener.fn,
                        context = listener.context || gContext || window

                    isFunction(context) && (context = context())
                    fn.apply(context, args)
                })
                this._trigging = false
            },
            _addOffline: function (key, action) {
                var offlineActions = this.offlineActionsMap[key] || (this.offlineActionsMap[key] = [])

                offlineActions.push(action)
            },
            _triggerOffline: function (key, last) {
                var offlineActions = this.offlineActionsMap[key]

                if (!offlineActions) return

                if (last === 'last') {
                    offlineActions.length && offlineActions.pop()()
                }
                else {
                    offlineActions.forEach(function (offlineAction) {
                        offlineAction()
                    })
                }

                this.offlineActionsMap[key] = null
            }
        }
    }

    function utils(require, module, exports) {
        exports.pathResolve = pathResolve
        exports.readData = readData
        exports.hasKeyPath = hasKeyPath
        exports.writeData = writeData
        exports.replaceData = replaceData
        exports.classObjectify = classObjectify
        exports.classStringify = classStringify
        exports.styleObjectify = styleObjectify
        exports.styleStringify = styleStringify
        exports.mergeClassOrStyle = mergeClassOrStyle
        exports.traveres = traveres
        exports.collectFunctionDeps = collectFunctionDeps
        exports.ShortCache = ShortCache
        exports.ajax = ajax
        exports.randomStr = randomStr
        exports.random = random
        exports.getURLParam = getURLParam
        exports.setCookie = setCookie
        exports.getCookie = getCookie
        exports.getCookies = getCookies
        exports.removeCookie = removeCookie
        exports.isType = isType
        exports.toType = toType
        exports.clone = clone
        exports.compare = compare
        exports.combine = combine
        exports.inherit = inherit
        exports.createPagingUpdater = createPagingUpdater
        exports.createScrollPaging = createScrollPaging
        exports.debounce = debounce
        exports.throttle = throttle
        exports.curry = curry
        exports.base64ToBlob = base64ToBlob
        exports.sort = sort
        exports.autoFontSize = autoFontSize
        exports.autoEllipsis = autoEllipsis
        exports.toChineseNumber = toChineseNumber

        var Reg$SplitKeyPath = /^(?:([\w$]+)|\.([\w$]+)|\[\s*(?:(\d+)|(["'])(.+?)\4)\s*\])/,
            pathResolvedCache = {},
            ARRAY_INDEX = 1,
            OBJECT_KEY = 2

        function pathResolve(keyPath) {
            if (!isString(keyPath)) throw logTypeError("??????????????????????????????????????? keyPath", "String", toType(keyPath))

            if (!keyPath) throw logError("?????????????????????????????? keyPath ????????????")

            if (isArray(pathResolvedCache[keyPath])) return pathResolvedCache[keyPath]

            var matcher,
                pathKeys = [],
                remainPath = keyPath,
                prevPath = ""

            pathKeys.types = []

            while (remainPath) {
                if (matcher = remainPath.match(Reg$SplitKeyPath)) {
                    var pathKey = matcher[1] || matcher[2] || matcher[3] || matcher[5],
                        type = matcher[3]
                            ? ARRAY_INDEX
                            : OBJECT_KEY

                    pathKeys.push(pathKey)
                    pathKeys.types.push(type)
                    cutMatch()
                }
                else {
                    throw logError("???????????????????????????" + keyPath + "???????????????????????????")
                }
            }

            return pathResolvedCache[keyPath] = pathKeys

            function cutMatch() {
                var startIndex = matcher.index,
                    endIndex = startIndex + matcher[0].length

                prevPath += remainPath.substring(0, endIndex)
                remainPath = remainPath.substring(endIndex)
            }
        }

        function readData(data, keyPath) {
            if (!isObject(data)) throw logTypeError("???????????????????????????????????? data", "Object", toType(data))

            if (isUndef(keyPath) || !isString(keyPath)) throw logTypeError("???????????????????????????????????? keyPath", "String", toType(keyPath))

            if (!keyPath) throw logError("??????????????????????????? keyPath ????????????")

            var pathKeys = pathResolve(keyPath),
                value = Undefined

            for (var i = 0, len = pathKeys.length; i < len; i++) {
                var key = pathKeys[i]

                if (!isObject(data)) break

                if (i === len - 1) {
                    value = data[key]
                }
                else {
                    data = data[key]
                }
            }

            return value
        }

        function hasKeyPath(data, keyPath) {
            if (!isObject(data)) throw logTypeError("?????? keyPath ???????????????????????? data", "Object", toType(data))

            if (isUndef(keyPath) || !isString(keyPath)) throw logTypeError("?????? keyPath ???????????????????????? keyPath", "String", toType(keyPath))

            if (!keyPath) throw logError("?????? keyPath ??????????????? keyPath ????????????")

            var pathKeys = pathResolve(keyPath),
                has = false

            for (var i = 0, len = pathKeys.length; i < len; i++) {
                var key = pathKeys[i]

                if (!isObject(data)) break

                if (i === len - 1) {
                    has = data.hasOwnProperty(key)
                }
                else {
                    data = data[key]
                }
            }

            return has
        }

        function writeData(data, keyPath, value) {
            if (!isObject(data)) throw logTypeError("???????????????????????????????????? data", "Object", toType(data))

            if (isUndef(keyPath) || !isString(keyPath)) throw logTypeError("???????????????????????????????????? keyPath", "String", toType(keyPath))

            if (!keyPath) throw logError("??????????????????????????? keyPath ????????????")

            var pathKeys = pathResolve(keyPath),
                types = pathKeys.types,
                success = false

            for (var i = 0, len = pathKeys.length; i < len; i++) {
                var key = pathKeys[i]

                if (!isObject(data)) break

                if (i === len - 1) {
                    if (!(key in data) || !isEqual(data[key], value)) {
                        data = findKeyOwner(data, key)
                        data[key] = value
                        success = true
                    }
                    break
                }

                if (isObject(data[key])) {
                    data = data[key]
                    continue
                }

                var nextKeyType = types[i + 1]

                if (nextKeyType == ARRAY_INDEX) {
                    data = findKeyOwner(data, key)
                    data = data[key] = []
                }
                else if (nextKeyType === OBJECT_KEY) {
                    data = findKeyOwner(data, key)
                    data = data[key] = {}
                }
            }

            return success
        }

        function replaceData(data, keyPath, value) {
            if (!isObject(data)) throw logTypeError("???????????????????????????????????? data", "Object", toType(data))

            if (isUndef(keyPath) || !isString(keyPath)) throw logTypeError("???????????????????????????????????? keyPath", "String", toType(keyPath))

            if (!keyPath) throw logError("??????????????????????????? keyPath ????????????")

            var pathKeys = pathResolve(keyPath),
                success = false

            for (var i = 0, len = pathKeys.length; i < len; i++) {
                var key = pathKeys[i]

                if (!isObject(data)) break

                if (i === len - 1) {
                    if (!isEqual(data[key], value)) {
                        data = findKeyOwner(data, key)
                        data[key] = value
                        success = true
                    }
                    break
                }

                data = data[key]
            }

            return success
        }

        function findKeyOwner(data, key) {
            if (key in data) {
                while (!data.hasOwnProperty(key)) {
                    if (data !== data.constructor.prototype) {
                        data = data.constructor.prototype
                    } else if (data.$_proto_) {
                        data = data.$_proto_
                    } else {
                        break
                    }
                }
            }

            return data
        }

        function classObjectify(_class) {
            if (isPlainObject(_class)) return _class

            if (isString(_class)) {
                if (!_class) return null

                var classObject = {},
                    classList = _class.split(/\s+/)

                for (var i = 0, len = classList.length; i < len; i++) {
                    var className = classList[i]

                    if (!className) continue

                    classObject[className] = true
                }

                return isNotEmptyObject(classObject) ? classObject : null
            }
            else if (isArray(_class)) {
                if (!_class.length) return null

                var classObject = {}

                for (var i = 0, len = _class.length; i < len; i++) {
                    var _class$ = _class[i]

                    Object.assign(classObject, classObjectify(_class$))
                }

                return isNotEmptyObject(classObject) ? classObject : null
            }

            return null
        }

        function classStringify(_class) {
            if (isString(_class)) return _class

            if (isPlainObject(_class)) {
                var classList = []

                for (var className in _class) {
                    if (_class[className]) {
                        classList.push(className)
                    }
                }

                return classList.join(" ")
            }
            else if (isArray(_class)) {
                _class = classObjectify(_class)

                return _class ? classStringify(_class) : ""
            }

            return _class == null ? "" : String(_class)
        }

        function styleObjectify(_style) {
            if (isPlainObject(_style)) return _style

            if (isString(_style)) {
                if (!_style) return null

                var styleObject = {},
                    styleList = _style.split(/\s*;\s*/)

                for (var i = 0, len = styleList.length; i < len; i++) {
                    var style = styleList[i]

                    if (!style) continue

                    var tuple = style.split(":"),
                        name = tuple[0],
                        value = tuple[1] || ""

                    if (isDef(name)) {
                        styleObject[name] = value
                    }
                }

                return isNotEmptyObject(styleObject) ? styleObject : null
            }
            else if (isArray(_style)) {
                if (!_style.length) return null

                var styleObject = {}

                for (var i = 0, len = _style.length; i < len; i++) {
                    var _style$ = _style[i]

                    Object.assign(styleObject, styleObjectify(_style$))
                }

                return isNotEmptyObject(styleObject) ? styleObject : null
            }

            return null
        }

        function styleStringify(_style) {
            if (isString(_style)) return _style

            if (isPlainObject(_style)) {
                var style = ""

                for (var key in _style) {
                    var value = _style[key]

                    if (isUndef(value)) {
                        continue
                    }

                    style += key + ":" + String(value) + ";"
                }

                return style
            }
            else if (isArray(_style)) {
                _style = styleObjectify(_style)

                return _style ? styleStringify(_style) : ""
            }

            return _style == null ? "" : String(_style)
        }

        function mergeClassOrStyle(key, source, val) {
            if (val === false || isUndef(source)) return val

            var objectify = {
                "style": styleObjectify,
                "class": classObjectify
            }[key]

            if (objectify) {
                val = Object.assign({}, objectify(source), objectify(val))
            }

            return val
        }

        function traveres(tree, config) {
            var onWalkDown = isFunction(config.onWalkDown) ? config.onWalkDown : null,
                onWalkUp = isFunction(config.onWalkUp) ? config.onWalkUp : null,
                getChildren = isFunction(config.children) ? config.children : null

            read(tree)

            function read(node, index, parent) {
                onWalkDown && onWalkDown(node, index, parent)

                var children = getChildren ? getChildren(node) : node.children

                if (children) {
                    for (var i = 0, len = children.length; i < len; i++) {
                        var child = children[i]
                        read(child, i, node)
                    }
                }

                onWalkUp && onWalkUp(node, index, parent)
            }
        }

        function collectFunctionDeps(_function, observables) {
            if ("__deps__" in _function) return _function.__deps__

            var keyPathReg = "(([\\w$]+)(?:(?=(\\.[\\w$]+|\\[\\s*(?:\\d+|([\"']).+?\\4)\\s*\\]))\\3(?!\\s*\\())*)",
                funcString = String(_function),
                collects = {},
                otherRefs = findContextRefs()

            _function.collecting = true

            collectDepsWith("this")

            if (otherRefs) {
                for (var i = 0, len = otherRefs.length; i < len; i++) {
                    collectDepsWith(otherRefs[i])
                }
            }

            delete _function.collecting

            var deps = Object.keys(collects)

            if (!deps.length) {
                deps = null
            }

            _function.__deps__ = deps

            return deps

            /**
             * ??????????????????????????? head ???????????????????????????????????????
             * @param {string} head
             */
            function collectDepsWith(head) {
                var reg = new RegExp(head + "\\." + keyPathReg + "(?!\\s*=(?!=))", "g"),
                    matcher = null

                while (matcher = reg.exec(funcString)) {
                    var keyPath = matcher[1],
                        keyPathHead = matcher[2]

                    if (!(keyPathHead in observables)) continue

                    var dep = observables[keyPathHead]

                    if (isFunction(dep)) {
                        if (dep.collecting) continue

                        var deps$ = collectFunctionDeps(dep, observables)

                        if (!deps$) continue

                        deps$.forEach(function (keyPath) {
                            collects[keyPath] = Undefined
                        })
                    }
                    else {
                        collects[keyPath] = Undefined
                    }
                }
            }

            /**
             * ??????????????????????????? this ???????????????????????????????????????
             */
            function findContextRefs() {
                var refs = []

                find("this", funcString)

                return refs.length ? refs : null

                function find(refVar, content) {
                    var Reg$AssignStatement = new RegExp(keyPathReg + "\\s*=\\s*" + refVar + "\s*[,;\\n]", "g"),// new RegExp(keyPathReg + "\\s*=\\s*" + contextRef + "(?![\\w$])", "g"),
                        matcher = null

                    while (matcher = Reg$AssignStatement.exec(content)) {
                        var ref = matcher[1]

                        refs.push(ref)

                        find(ref, content.substring(matcher.index + matcher[0].length))
                    }
                }
            }
        }

        function ShortCache() {
            this.map = null
        }

        ShortCache.prototype = {
            constructor: ShortCache,
            set: function (key, val) {
                if (!this.map) {
                    var shortCache = this

                    this.map = new Map()

                    Promise.resolve().then(function () {
                        shortCache.map = null
                    })
                }

                this.map.set(key, val)
            },
            get: function (key) {
                return this.map ? this.map.get(key) : null
            }
        }

        function ajax(options) {
            if (!(this instanceof ajax)) return new ajax(options);

            this.validateAndInit(options)
            this.setConfig(options)

            if (this.noPending()) {
                var cacheData = this.getCache()

                this.isAvailableCache(cacheData)
                    ? this.useCache(cacheData)
                    : this.sendAjax(options)

                this.setPending()
            }

            return this.makeResponse(options)
        }
        ajax.prototype = {
            constructor: ajax,
            _canStore: testLocalStorage(),
            _pendingDef: {},
            _cacheStore: {},
            _jsonpSyncFlag: false,
            validateAndInit: function (options) {
                var url = options.url, data = options.data || (options.data = {});

                if (!url) throw new Error('ajax????????????url??????');

                this.cacheKey = url + "?" + (data && isPlainObject(data) ? decodeURIComponent($.param(data)) : (this.allowCache = false, ""));
            },
            noPending: function () {
                var cacheKey = this.cacheKey;
                this.def = this._pendingDef[cacheKey];

                return !this.def;
            },
            setConfig: function (options) {
                this.allowCache = options.allowCache != false
                this.cacheAge = options.cacheAge || 5 * 60 * 1000
                this.alwaysUseCache = options.alwaysUseCache || false
                this.useLocalStorage = options.useLocalStorage || false
                this.returnPromise = (options.returnPromise && window.Promise) != false
                this.sendJsonpWithoutJquery = options.sendJsonpWithoutJquery || false
                this.successCallback = typeof options.success === 'function' && options.success;

                // options.error || (options.error = function (xhr, type, exception) {
                //     genConsole().stdout(console.error)
                //         .print("????????????")
                //         .print("??????url", options.url)
                //         .print("?????????", xhr.status)
                //         .print("??????", xhr.responseText)
                // })
                options.cache = this.allowCache;
                // options.timeout = options.timeout === Undefined ? 10000 : options.timeout
            },
            getCache: function () {
                if (!this.allowCache) return false;

                var cacheKey = this.cacheKey, cacheData = this._cacheStore[cacheKey];

                if (!cacheData && this.useLocalStorage) {
                    cacheData = JSON.parse(this._canStore ? w.localStorage.getItem(cacheKey) : getCookie(cacheKey));
                    this._cacheStore[cacheKey] = cacheData;
                }

                return cacheData;
            },
            isAvailableCache: function (cacheData) {
                var isAvailable = Boolean(cacheData) && (this.alwaysUseCache || cacheData.expires > +new Date);
                !isAvailable && this.removeCache();

                return isAvailable;
            },
            removeCache: function () {
                if (this.useLocalStorage)
                    this._canStore ? window.localStorage.removeItem(this.cacheKey) : removeCookie(this.cacheKey)
            },
            useCache: function (cacheData) {
                this.def = $.Deferred().resolve(clone(cacheData.data))
            },
            setPending: function () {
                var cacheKey = this.cacheKey,
                    _pendingDef = this._pendingDef

                _pendingDef[cacheKey] = this.def

                this.def.always(function () {
                    delete _pendingDef[cacheKey]
                })
            },
            repairJSON: function (options) {
                if (options.repairJSON && options.dataType.match(/^json$/i)) {
                    var _dataFilter = options.dataFilter

                    options.dataFilter = function (content) {
                        _dataFilter && (content = _dataFilter.call(this, content))

                        var replaceMap = { "\r": "\\r", "\n": "\\n", "\t": "\\t" },
                            _content = $.trim(content).replace(/(")((?:[^"]|"\s*(?!\s*[}\]]|[:,]\s*(?:["\[{]|\d+\b)))*)(")/g, function (match, $1, quotString, $3) {

                                return $1 + quotString.replace(/[\r\n\t]/g, function (match) {/*???????????????????????????????????????*/
                                    return replaceMap[match] || match
                                }).replace(/[\\]?"/g, '\\"')/*??????????????????????????????????????????*/ + $3

                            }).replace(/[\r\n\t]/g, "")/*?????????????????????????????????*/.replace(/,\s*([}\]])/g, "$1")/*??????????????????*/

                        return _content
                    }
                }

                return options
            },
            sendAjax: function (options) {
                var newOption = delProps(this.repairJSON(clone(options)), ['repairJSON', 'allowCache', 'cacheAge', 'alwaysUseCache', 'returnPromise', 'useLocalStorage', 'success']),
                    cacheKey = this.cacheKey,
                    _self = this,
                    def = newOption.dataType === 'jsonp' && this.sendJsonpWithoutJquery
                        ? this.sendJsonpWithScript(newOption)
                        : $.ajax(newOption)

                this.def = def.done(function (res) {
                    if (_self.allowCache) {
                        var expiresDate = +new Date + _self.cacheAge,
                            cacheData = { data: res, expires: expiresDate };

                        _self._cacheStore[cacheKey] = cacheData;

                        if (_self.useLocalStorage && isType(res, ['object', 'array', 'string'])) {
                            var cacheDataStr = JSON.stringify(cacheData);

                            _self._canStore ? (window.localStorage.setItem(cacheKey, cacheDataStr), _self.setStorageExpireRecord(cacheKey, expiresDate))
                                : setCookie(cacheKey, cacheDataStr, { expires: new Date(expiresDate) });
                        }
                    };
                });
                this.clearExpiredStorage();

                function delProps(obj, props) {
                    props = isType(props, 'array') ? props : [props];
                    props.forEach(function (v, i) {
                        isString(v) && delete obj[v]
                    })

                    return obj
                }
            },
            sendJsonpWithScript: function () {// ?????????????????????jsonp??????????????????????????????????????????????????????????????????????????????1??????????????????jquery???jsonp????????????
                var prototype = ajax.prototype

                return function (options) {
                    var script = document.createElement('script'),
                        def = $.Deferred(),
                        sid = setTimeout(error, 1000),
                        jsonpCallbackName = options.jsonpCallback,
                        callback = window[jsonpCallbackName],
                        userCallbackName = jsonpCallbackName + '2',
                        userCallback = callback && (callback != successCallback ? (window[userCallbackName] = callback) : window[userCallbackName])

                    window[jsonpCallbackName] = successCallback
                    script.src = options.url
                    script.onload = script.onreadystatechange = function (e, t) {
                        if (!script.readyState || /loaded|complete/.test(script.readyState)) {
                            prototype.jsonpResult === Undefined ? error() : success()
                        }
                    }
                    script.onerror = error
                    document.getElementsByTagName('head')[0].appendChild(script)

                    return def

                    function error() {
                        clearTimeout(sid)
                        script.onload = script.onreadystatechange = null, $(script).remove(), script = null
                        def.reject('404')
                    }

                    function success() {
                        clearTimeout(sid)
                        script.onload = script.onreadystatechange = null, $(script).remove(), script = null

                        var args = prototype.jsonpResult

                        prototype.jsonpResult = Undefined
                        def.done(function () {
                            args && typeof userCallback === 'function' && userCallback.apply(args)
                        })
                        def.resolve.apply(def, args)
                    }
                }

                function successCallback() {
                    prototype.jsonpResult = slice(arguments)
                }
            }(),
            setStorageExpireRecord: function (key, expiresDate) {
                if (this._canStore) {
                    var record = JSON.parse(window.localStorage.getItem('_toolkit_storage_record')) || {}

                    record[key] = expiresDate
                    window.localStorage.setItem('_toolkit_storage_record', JSON.stringify(record));
                }
            },
            clearExpiredStorage: function () {
                var isClear = false;

                if (this._canStore) {
                    var record = JSON.parse(window.localStorage.getItem('_toolkit_storage_record')), now = +new Date;

                    for (var key in record) {
                        var expiresDate = record[key];

                        (expiresDate < now) && (window.localStorage.removeItem(key), delete record[key], isClear = true);
                    }

                    isClear && window.localStorage.setItem('_toolkit_storage_record', JSON.stringify(record));
                }
            },
            makeResponse: function (options) {
                var res = this.returnPromise ? this.toPromise(options) : this.def;

                this.res = this.successCallback ? res.then(this.successCallback) : res;

                return this.res
            },
            toPromise: function (options) {
                var def = this.def

                return new Promise(function (resolve, reject) {
                    def.done(function (res) {
                        typeof res === "object" && (res = clone(res))
                        resolve(res)
                    }).fail(function (xhr, state, exception) {
                        reject(options.url + " " + xhr.status + "\n" + exception)
                    })
                })
            }
        }

        function randomStr(count) {
            var baseStr = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789",
                max = baseStr.length - 1,
                str = ""

            while (count--) {
                var index = random(0, max)

                str += baseStr[index]
            }

            return str
        }

        function random(min, max) {
            min = min || 0

            return (Math.random() * (max - min + 1) | 0) + min
        }

        var paramObjDecoded
        /**
         * ????????????URL??????
         * @param {string} name
         * @param {Object} options
         */
        function getURLParam(name, options) {
            if (isUndef(paramObjDecoded)) {
                paramObjDecoded = {}

                var paramString = location.search.substr(1);

                paramString.split('&').forEach(function (param) {
                    if (!param) return

                    var index = param.indexOf("="),
                        name = ~index ? param.substring(0, index) : param,
                        value = ~index ? param.substring(index + 1) : ""

                    if (!name) return

                    paramObjDecoded[name] = value && _checkXSS(decodeURIComponent(value.replace(/%(?![0-9a-f]{2})/gi, '%25')));
                })
            }

            if (!name) return Object.assign({}, paramObjDecoded)

            var value = paramObjDecoded[name]

            if (isUndef(options)) return value

            if (!isPlainObject(options)) {
                throw logTypeError("getURLParam?????????????????? options", "Object", toType(options))
            }

            options = Object.assign({
                required: false,
                optional: Undefined,
                onerror: Undefined
            }, options)

            var optional = options.optional

            if (isDef(optional) && !isArray(optional)) {
                throw logTypeError("getURLParam?????????????????? optional", "Array", toType(optional))
            }
            else if (
                isArray(optional) &&
                optional.some(function (a) { return !isString(a) || !a })
            ) {
                throw logError("getURLParam????????? optional ?????????????????????????????????")
            }

            if (options.required && !value) {
                handleError("required", "getURLParam?????????????????? URL ?????????" + name + "???")
            }

            if (value && isArray(optional) && !~optional.indexOf(value)) {
                handleError("optional", "getURLParam???URL ?????????" + name + "????????????" + value + "?????????????????? optional ???????????????")
            }

            return value

            function _checkXSS(str) {
                return str && str.replace(/<[^>]+>/gi, function (match) {
                    return encodeURIComponent(match);
                })
            }

            function handleError(errType, errMsg) {
                if (isFunction(options.onerror)) {
                    var val = options.onerror(errType, value)

                    if (isString(val)) {
                        return value = val
                    }
                }

                logError(errMsg)
            }
        }

        // ??????COOKIE
        function setCookie(name, value, options) {
            options = Object.assign({
                domain: null,
                path: '/',
                expires: null
            }, options)

            var cookieOption = ''

            for (var optionNm in options) {
                var optionValue = options[optionNm]

                if (isUndef(optionValue)) continue

                if (optionNm === 'expires' && isType(optionValue, 'Date')) {
                    optionValue = optionValue.toGMTString()
                }

                cookieOption += optionNm + "=" + optionValue + ";";
            }

            document.cookie = name + "=" + encodeURIComponent(String(value)) + ";" + cookieOption
        }

        // ????????????COOKIE
        function getCookie(name) {
            var reg = new RegExp(name + "=([^;]*)"),
                cookie = document.cookie.match(reg)

            return cookie && decodeURIComponent(cookie[1]);
        }

        // ????????????COOKIE
        function getCookies(names) {
            return names.reduce(function (obj, key) {
                return obj[key] = getCookie(key), obj;
            }, {})
        }

        // ????????????COOKIE
        function removeCookie(key, option) {
            option = option || {}

            var value = getCookie(key),
                date = new Date()

            date.setTime(date.getTime() - 1)
            option.expires = date;
            setCookie(key, value, option);
        }

        var _toString = Object.prototype.toString

        function toType(value) {
            var type = _toString.call(value).slice(8, -1)

            if (type === "Object") {
                type = nvl(value.constructor.name, "Object")
            }

            return type
        }

        function isType(value, optionalTypes) {
            var type = toType(value)

            optionalTypes =
                "," +
                (isArray(optionalTypes)
                    ? optionalTypes.join(",")
                    : optionalTypes) +
                ","

            return Boolean(~optionalTypes.toLowerCase().indexOf("," + type.toLowerCase() + ","))
        }

        // ??????????????????
        function clone(obj, record) {
            if (!isObject(obj) || (record && ~record.indexOf(obj))) return obj;

            record ? record.push(obj) : (record = [obj])

            if (isArray(obj)) {
                return obj.map(function (a) {
                    return clone(a, record)
                })
            }
            else if (obj instanceof Date) {
                return new Date(obj.getTime())
            }
            else {
                var cloneObj

                if (isPlainObject(obj)) {
                    cloneObj = {}
                }
                else {
                    try {
                        cloneObj = new obj.constructor()
                    } catch (e) {
                        return obj
                    }
                }

                for (var key in obj) {
                    if (obj.hasOwnProperty(key)) {
                        cloneObj[key] = clone(obj[key], record);
                    }
                }

                return cloneObj
            }
        }

        // ????????????
        function compare(a, b) {
            if (a === b) return true

            var isObjectA = isObject(a),
                isObjectB = isObject(b)

            if (isObjectA && isObjectB) {
                var isArrayA = isArray(a),
                    isArrayB = isArray(b)

                if (isArrayA && isArrayB) {
                    return a.length === b.length && a.every(function (e, i) {
                        return compare(e, b[i])
                    })
                }
                else if (a instanceof Date && b instanceof Date) {
                    return a.getTime() === b.getTime()
                }
                else if (!isArrayA && !isArrayB) {
                    var keysA = Object.keys(a),
                        keysB = Object.keys(b)

                    return keysA.length === keysB.length && keysA.every(function (key) {
                        return compare(a[key], b[key])
                    })
                }
                else {
                    return false
                }
            }
            else if (!isObjectA && !isObjectB) {
                return String(a) === String(b)
            }
            else {
                return false
            }
        }

        /**
         * ??????
         * combine(["a","b"],[1,2,3]) => [ ["a",1],["a",2],["a",3],["b",1],["b",2],["b",3] ]
         */
        function combine() {
            if (arguments.length < 2) throw logError("combine???????????????????????????????????????")

            var groups = slice(arguments),
                result = groups.reduce(function (groupA, groupB, index) {
                    var newGroup = [],
                        useConcat = index > 1

                    groupA.forEach(function (a) {
                        groupB.forEach(function (b) {
                            useConcat
                                ? newGroup.push(a.concat(b))
                                : newGroup.push([a, b])
                        })
                    })

                    return newGroup
                })

            return result
        }

        // ??????
        function inherit(ChildClass, ParentClass) {
            function ChildProtoClass() { this.$_proto_ = ChildProtoClass.prototype }
            ChildProtoClass.prototype = ParentClass.prototype

            var childProto = new ChildProtoClass()

            function ChildClass$() {
                ChildClass.apply(this, arguments)

                this.$_proto_ = ChildClass$.prototype

                noop.prototype = this// ?????????chrome???????????????????????????????????????????????????????????????????????? ???ChildClass$???
                noop.prototype = null
            }

            ChildClass$.prototype = ChildClass.prototype = Object.assign(childProto, ChildClass.prototype)
            ChildClass$.prototype.constructor = ChildClass
            ChildClass$.prototype.hasOwnProperty = hasOwn

            return ChildClass$
        }

        function hasOwn(key) {
            return Object.prototype.hasOwnProperty.call(this, key) && key !== "$_proto_" && key !== "constructor" && key !== "hasOwnProperty"
        }

        // ?????????
        function createPagingUpdater(startPage, updatePage) {
            var page = Number(startPage),
                pendding = false,
                hasNext = true,
                usePromise = updatePage.length <= 1,
                callbacks = null

            return function updateNextPage(onUpdated) {
                addCallback(onUpdated)

                if (!hasNext) return invokeCallback()

                if (!pendding) {
                    pendding = true

                    if (usePromise) {
                        var promise = updatePage(page)

                        if (!(promise instanceof Promise)) {
                            throw Error("?????????????????????????????????????????????????????? Promise????????? Promise ??????????????? hasNext??????????????? Promise???????????????????????????????????????????????????????????? {Number}nextPage, {Function}done, {Function}fail")
                        }

                        promise.then(done)["catch"](fail)
                    }
                    else {
                        updatePage(page, done, fail)
                    }
                }
            }

            function done(hasNext$) {
                pendding = false
                hasNext = Boolean(hasNext$)
                page = page + 1

                invokeCallback()
            }

            function fail() {
                pendding = false
                hasNext = false

                invokeCallback()
            }

            function addCallback(callback) {
                if (!isFunction(callback)) return

                callbacks || (callbacks = [])
                callbacks.push(callback)
            }

            function invokeCallback() {
                if (!callbacks) return

                for (var i = 0, len = callbacks.length; i < len; i++) {
                    callbacks[i](hasNext, page)
                }

                callbacks = null
            }
        }

        /**
         * ???????????????
         * @param {Element} scrollRef ????????????
         * @param {Element} contentRef ????????????[??????,?????????????????????????????????(?????????????????????)???????????????]
         * @param {Number} page ?????????
         * @param {Function} pageUpdater ??????????????????
         * 
         * <div ????????????>  
         *    <div ????????????></div>  
         *    <ul ????????????>  
         *      <li ?????????????????????></li>  
         *    </ul>  
         *    <div ????????????></div>  
         * </div>
         */
        function createScrollPaging(scrollRef, contentRef, page, pageUpdater) {
            var $contentRef = null

            if (pageUpdater == null && typeof page === "function") {
                pageUpdater = page
                page = contentRef
                contentRef = null
            }
            else {
                $contentRef = $(contentRef)
            }

            var updateNextPage = createPagingUpdater(page, pageUpdater),
                $scrollRef = $(scrollRef),
                isDoc = scrollRef === document,
                active = true,
                _loadPage = throttle(loadPageIfNeed, 200)

            $scrollRef.on("scroll", _loadPage)

            var sid = setTimeout(function () {
                loadUntilScrollable(true)
            })

            return {// ?????????,????????????????????????????????????????????????,?????????????????????????????????
                deactive: function () {
                    active = false
                },
                active: function () {
                    active = true
                },
                destroy: function () {
                    sid && clearTimeout(sid)
                    $scrollRef.off("scroll", _loadPage)
                }
            }

            function loadPageIfNeed(onUpdated) {
                if (!active) return

                var remainHeight = getRemainHeight()

                if (remainHeight < 500) {
                    updateNextPage(onUpdated)
                }
            }

            function getRemainHeight() {
                var scrollTop = $scrollRef.scrollTop(),
                    scrollHeight = getScrollHeight(),
                    viewHeight = isDoc ? window.innerHeight : $scrollRef.height(),
                    tailHeight = $contentRef ? scrollHeight - $contentRef.height() - $contentRef.offset().top : 0,
                    remainHeight = scrollHeight - scrollTop - viewHeight - tailHeight

                return remainHeight
            }

            function getScrollHeight() {
                var scrollHeight = 0

                $scrollRef.children().each(function (i, v) {
                    scrollHeight += $(v).height()
                })

                return scrollHeight
            }

            function loadUntilScrollable(force) {
                (force
                    ? updateNextPage
                    : loadPageIfNeed)
                    (function (hasNext, page) {
                        if (hasNext) {
                            sid = setTimeout(loadUntilScrollable, 300)
                        }
                        else {
                            sid = Undefined
                        }
                    })
            }
        }

        /**
         * ????????????????????????????????????????????????{wait}??????
         * @param {Function} fn ????????????
         * @param {Number} wait ????????????????????????
         * @param {Boolean|Function} immediate ??????????????????
         * 
         * * debounce(fn,1000) ???????????????,???1????????????????????????????????????????????? fn ?????????????????????
         * * debounce(fn,1000,true) ??????????????????????????????????????? fn??????1?????????????????????????????????????????????
         * * debounce(fn,1000,()=>alert("?????????????????????")) ??????????????????????????????????????? fn??????1??????????????????????????????????????????,??????1???????????????????????????{immediate}??????
         */
        function debounce(fn, wait, immediate) {
            var timer, args, context, timestamp

            function later() {
                var last = +new Date - timestamp

                if (last < wait) {
                    timer = setTimeout(later, wait - last)
                }
                else {
                    timer = null

                    if (!immediate) {
                        fn.apply(context, args)
                        context = args = null
                    }
                }
            }

            return function () {
                context = this, args = arguments, timestamp = +new Date

                if (!timer) {
                    timer = setTimeout(later, wait)

                    if (immediate) {
                        fn.apply(context, args)
                        context = args = null
                    }
                }
                else if (typeof immediate === "function") {
                    immediate()
                }
            }
        }

        /**
         * ??????????????????????????????????????????????????????{interval}?????????
         * @param {Function} fn ????????????
         * @param {Number} interval ????????????????????????
         * 
         * * throttle(fn,1000)???????????????????????????????????????fn?????????????????????1000??????
         */
        function throttle(fn, interval) {
            var timer, lastTimestamp = 0

            return function () {
                if (timer) return

                var _self = this,
                    args = arguments,
                    timestamp = + new Date,
                    pastTime = timestamp - lastTimestamp

                if (pastTime >= interval) {
                    lastTimestamp = timestamp
                    fn.apply(_self, args)
                }
                else {
                    timer = setTimeout(function () {
                        timer = null
                        lastTimestamp = + new Date
                        fn.apply(_self, args)
                    }, interval - pastTime)
                }
            }
        }

        /**
         * ???????????????-????????????
         * @param {Function} fn 
         */
        function curry(fn) {
            var currArgs = slice(arguments, 1)

            return function () {
                var args = slice(arguments),
                    allArgs = currArgs.concat(args)

                return allArgs.length >= fn.length
                    ? fn.apply(this, allArgs)
                    : curry.apply(this, [fn].concat(allArgs))
            }
        }

        /**
         * base64???blob
         * @param {String} base64 
         */
        function base64ToBlob(base64) {
            var arr = base64.split(','),
                mime = arr[0].match(/:(.*?);/)[1],
                bstr = atob(arr[1]), n = bstr.length, u8arr = new Uint8Array(n)

            while (n--) {
                u8arr[n] = bstr.charCodeAt(n)
            }

            return new Blob([u8arr], { type: mime })
        }

        /**
         * ### ??????????????????
         * @param {array} list ??????
         * @param {Function} [fn] ???????????????????????????
         * 
         * * sort(list)
         * * sort(list, function(a,b){return a-b})
         * 
         * ### ?????????????????? (????????????key??????)
         * @param {array} list ????????????
         * @param {string} key... ?????????????????????????????????????????????????????????????????????
         * * ??????????????? + ??????????????????# ??????????????????  
         *   ????????????????????????????????????????????????  
         *   ??????????????? > ???????????????????????????< ???????????????????????????
         * @param {string} [globalOrder] ???????????????????????????????????????????????????????????????????????????????????????????????????????????????????????????????????????????????????
         * 
         * * sort(list,"key1","key2") => key1?????? key2??????
         * * sort(list,"key1","key2",">") => key1?????? key2??????
         * * sort(list,"key1","key2<","key3",">") => key1?????? key2?????? key3??????
         * * sort(list,"+key1>","#key2>","+key3") => key1??????,???????????? key2??????,???????????? key3??????,????????????
         */
        function sort(list) {
            if (!isArray(list) || !list.length) return list

            var isObjectList = true,
                sortArgs = null,
                _list = list.filter(function (item) {
                    return isDef(item) && (!isObject(item) && (isObjectList = false), true)
                })

            if (!_list.length) return list

            if (isObjectList) {
                sortArgs = slice(arguments, 1)
                isObjectList = sortArgs.length && sortArgs.every(function (sortArg) {
                    return isString(sortArg)
                })
            }

            if (!isObjectList) {
                return list.sort(isFunction(arguments[1]) ? arguments[1] : Undefined)
            }

            var lastArg = sortArgs.at(-1),
                globalOrder = (lastArg === "<" || lastArg === ">") ? (sortArgs.pop() === "<" ? -1 : 1) : -1,
                keyOrderMap = {},
                keyCharOrInt = {},
                keys = sortArgs.map(function (arg) {
                    return arg.replace(/^([#+]?)([^<>]+)([<>]?)$/, function (match, charOrInt, key, keyOrder) {
                        charOrInt && (keyCharOrInt[key] = charOrInt)
                        keyOrder && (keyOrderMap[key] = keyOrder === "<" ? -1 : 1)
                        return key
                    })
                }),
                keyMaxIndex = keys.length - 1

            if (!~keyMaxIndex) return logError("?????????key,??????????????????"), list

            return _list.sort(function (a, b) {
                return sortCompare(a, b)
            })

            function sortCompare(a, b, index) {
                var key = keys[index || 0],
                    charOrInt = keyCharOrInt[key],
                    aVal = a[key],
                    bVal = b[key],
                    order = keyOrderMap[key] || globalOrder

                charOrInt === "+" && !isNaN(aVal) && !isNaN(bVal)
                    ? (aVal = +aVal, bVal = +bVal)
                    : charOrInt === "#" && (aVal = String(aVal), bVal = String(bVal))

                return aVal < bVal
                    ? order
                    : aVal > bVal
                        ? -order
                        : keyMaxIndex > index
                            ? sortCompare(a, b, ++index)
                            : -1
            }
        }

        /**
         * ???????????????????????????
         * @param {string} text ???????????????
         * @param {number} width ???????????????
         * @param {number} height ???????????????
         * @param {number} lineHeight ?????????line-height
         * @param {number} fontSize ?????????????????????
         */
        function autoFontSize(text, width, height, lineHeight, fontSize) {
            var widthFont = text && text.match(/[\u2e80-\ufe4f%]/g),
                chineseLen = ((widthFont ? widthFont.length : 0) + text.length) / 2,
                maxChineseLenInLine = ((width / fontSize) / 0.5 | 0) * 0.5

            return chineseLen > maxChineseLenInLine
                ? calSize(width, height, lineHeight, chineseLen)
                : fontSize

            function calSize(width, height, lineHeight, len) {
                var fontSize = Math.floor(Math.sqrt(width * height / len)),
                    lines = Math.ceil(len / Math.floor(width / fontSize) * 1.06)

                while (fontSize * lineHeight * lines > height) {
                    fontSize--
                    lines = Math.ceil(len / Math.floor(width / fontSize) * 1.06)
                }

                return fontSize
            }
        }

        /**
         * ??????????????????
         * @param {string} text ???????????????
         * @param {number} width ???????????????
         * @param {number} fontSize ?????????????????????
         * @param {number} maxLine ??????????????????
         * @param {string} tagName ?????????????????????
         */
        function autoEllipsis(text, width, fontSize, maxLine, tagName) {
            tagName = tagName || "span"

            var maxChineseLenInLine = ((width / fontSize) / 0.5 | 0) * 0.5,
                lines = [],
                lineText = "",
                lastChineseLen = 0,
                countChineseLen = 0

            for (var i = 0, len = text.length; i < len; i++) {
                var letter = text[i],
                    chineseLen = /[\u2e80-\ufe4f%]/.test(letter) ? 1 : /[A-Z]/.test(letter) ? 0.75 : 0.5

                countChineseLen += chineseLen

                if (countChineseLen <= maxChineseLenInLine) {
                    lastChineseLen = chineseLen
                    lineText += letter;
                }
                else {
                    lines.push(lineText)

                    if (lines.length == maxLine) {
                        lines[lines.length - 1] = lineText.replace(lastChineseLen > 0.5 ? /.$/ : /.{2}$/, "...")
                        break
                    }
                    else {
                        lineText = letter
                        countChineseLen = chineseLen
                    }
                }

                if (i === len - 1) {
                    lines.push(lineText)
                }
            }

            return lines.map(function (line, i) {
                return "<" + tagName + " style='white-space: nowrap;'>" + line + "</" + tagName + ">"
            }).join("<br>")
        }

        /**
         * ?????????????????????
         * @param {number} number ??????
         * 
         * * toChineseNumber(10010.01) => ???????????????????????????
         */
        function toChineseNumber(number) {
            if (isNaN(number)) throw Error('????????????????????????')

            var numberArea = (number + "").split('.'),
                integer = numberArea[0],
                decimal = numberArea[1],
                numberCharts = ['???', '???', '???', '???', '???', '???', '???', '???', '???', '???'],
                intUnitForPart = ['??????', '???', '???', ''],
                intUnitForChar = ['???', '???', '???', ''],
                RMB_Unit = decimal > 0 ? '???' : '??????',
                decimalUnitForChar = ['???', '???'],
                intChartsCount = integer.length,
                result = ""

            while (intChartsCount -= 4, intChartsCount > -4) {
                var startIndex = Math.max(0, intChartsCount), endIndex = intChartsCount + 4,
                    partOfInteger = integer.substring(startIndex, endIndex),
                    unit = intUnitForPart.pop()

                if (partOfInteger > 0) {
                    partOfChinese = toChinese(partOfInteger, intUnitForChar)
                    result = partOfChinese + unit + result
                }
            }

            result += RMB_Unit
            decimal = (decimal + '00').substr(0, decimalUnitForChar.length)
            result += toChinese(decimal, decimalUnitForChar)

            return result

            function toChinese(number, unitForChar) {
                var minNumber = 1, chinese = ""

                for (var i = number.length - 1, j = unitForChar.length - 1; i >= 0; i--, j--) {
                    var n = number.charAt(i),
                        char = numberCharts[n],
                        unit = unitForChar[j]

                    if (n >= minNumber) {
                        minNumber = 0// ?????????0??????,101=>????????????

                        if (n == '0') {
                            minNumber = 1// ????????????0,?????????????????????,1001=>????????????
                            chinese = char + chinese
                        }
                        else {
                            chinese = char + unit + chinese
                        }
                    }
                }

                return chinese
            }
        }
    }

    function nodeOps(require, module, exports) {
        var cssNumber = { "columnCount": true, "fillOpacity": true, "fontWeight": true, "lineHeight": true, "opacity": true, "orphans": true, "widows": true, "zIndex": true, "zoom": true }

        module.exports = {
            // cssValue: function (key, val) {
            //     if (!cssNumber[key] && typeof val === "number") {
            //         isNaN(val) ? val = 0 : val += "px"
            //     }
            //     return val
            // },
            _offset: function (elem) {// elem(border???)???html(content)????????? [css???zoom????????????????????? ????????????????????????]
                var html = document.documentElement

                if (elem === html) return { left: 0, top: 0 }

                var rect = elem.getBoundingClientRect(),
                    scrollTop = window.pageYOffset || html.scrollTop,
                    scrollLeft = window.pageXOffset || html.scrollLeft

                return {
                    left: rect.left + scrollLeft - (html.clientLeft),
                    top: rect.top + scrollTop - (html.clientTop)
                }
            },
            offset: function (elem) {// elem????????????html???????????????
                var left = 0, top = 0;

                while (elem) {
                    left += elem.offsetLeft
                    top += elem.offsetTop
                    elem = elem.offsetParent
                }

                return { left: left, top: top };
            },
            offsetParent: function (elem) {// ???????????????????????????
                var html = document.documentElement,
                    parent = elem.offsetParent

                while (parent && parent !== html && (!parent.style.position || parent.style.position === "static")) {
                    parent = parent.offsetParent
                }

                return parent || html
            },
            position: function (elem) {// elem(margin???)?????????????????????(content)?????????
                var offsetParent = this.offsetParent(elem),
                    distance = this.distance(elem, offsetParent),
                    elemMarginLeft = elem.style.marginLeft,
                    elemMarginTop = elem.style.marginTop,
                    parentBorderLeft = offsetParent.style.borderLeftWidth,
                    parentBorderTop = offsetParent.style.borderTopWidth

                return {
                    left: distance.left - parentBorderLeft - elemMarginLeft,
                    top: distance.top - parentBorderTop - elemMarginTop
                }
            },
            distance: function (elemA, elemB) {// elemA(border???)???elemB(border)?????????
                var offsetA = this.offset(elemA),
                    offsetB = this.offset(elemB)

                return {
                    left: offsetA.left - offsetB.left,
                    top: offsetA.top - offsetB.top
                }
            },
            addClass: function (elem, klass) {
                if (elem.nodeType !== 1 || !isRealString(klass)) return

                if (elem.classList) {
                    elem.classList.add.apply(elem.classList, klass.match(/\S+/g))
                } else {
                    var elClass = elem.className

                    if (elClass) {
                        elClass = " " + elClass + " "

                        var classes = klass.match(/\S+/g) || [],
                            change = false

                        for (var i = 0, len = classes.length; i < len; i++) {
                            if (!~elClass.indexOf(" " + classes[i] + " ")) {
                                elClass += classes[i] + " "
                                change = true
                            }
                        }

                        if (change) {
                            elem.className = elClass.trim()
                        }
                    }
                    else {
                        elem.className = klass
                    }
                }
            },
            removeClass: function (elem, klass) {
                if (elem.nodeType !== 1 || !isRealString(klass)) return

                if (elem.classList) {
                    elem.classList.remove.apply(elem.classList, klass.match(/\S+/g))
                    if (elem.classList.length === 0) {
                        elem.removeAttribute("class")
                    }
                } else {
                    var elClass = elem.className

                    if (elClass) {
                        elClass = " " + elClass + " "

                        var classes = klass.match(/\S+/g) || [],
                            change = false

                        for (var i = 0, len = classes.length; i < len; i++) {
                            if (~elClass.indexOf(" " + classes[i] + " ")) {
                                elClass = elClass.replace(" " + classes[i] + " ", " ")
                                change = true
                            }
                        }

                        if (change) {
                            elClass = elClass.trim()
                            elClass
                                ? elem.className = elClass
                                : elem.removeAttribute("class")
                        }
                    }
                }
            }
        }

        function camelCase(e) {
            return e.replace(/^-ms-/, "ms-").replace(/-([\da-z])/gi, function (e, t) {
                return t.toUpperCase()
            })
        }
    }

    function env(require, module, exports) {
        var ua = navigator.userAgent.toLowerCase(),
            testUA = function (reg) { return reg.test(ua) },
            getVersion = function (reg) {
                var matcher = ua.match(reg)
                return matcher ? matcher[1].replace(/_/g, ".") : ""
            },
            env$system = function () {
                /* ?????? */
                var env = {
                    platform: "",
                    system: "unknow",
                    systemVersion: "",
                    isWindows: false,
                    isMacOS: false,
                    isAndroid: false,
                    isIOS: false,
                    isElectron: testUA(/electron/)
                }

                if (testUA(/windows|win32|win64|wow32|wow64/)) {
                    env.platform = "desktop"
                    env.system = "windows"
                    env.isWindows = true
                    env.systemVersion = ""
                        || testUA(/windows (?:nt 5.0|2000)/) && "2000"
                        || testUA(/windows (?:nt 5.1|xp)/) && "xp"
                        || testUA(/windows (?:nt 5.2|2003)/) && "2003"
                        || testUA(/windows (?:nt 6.0|vista)/) && "vista"
                        || testUA(/windows (?:nt 6.1|7)/) && "7"
                        || testUA(/windows (?:nt 6.2|8)/) && "8"
                        || testUA(/windows (?:nt 6.3|8,1)/) && "8.1"
                        || testUA(/windows (?:nt 10.0|10)/) && "10"
                        || "unknow"
                }
                else if (testUA(/macintosh|macintel/)) {
                    env.platform = "desktop"
                    env.system = "macos"
                    env.isMacOS = true
                    env.systemVersion = getVersion(/os x ([\d._]+)/)
                }
                else if (testUA(/android|adr/)) {
                    env.platform = "mobile"
                    env.system = "android"
                    env.isAndroid = true
                    env.systemVersion = getVersion(/android ([\d._]+)/)
                }
                else if (testUA(/ios|iphone|ipad|ipod|iwatch/)) {
                    env.platform = "mobile"
                    env.system = "ios"
                    env.isIOS = true
                    env.systemVersion = getVersion(/os ([\d._]+)/)
                }

                return env
            }(),
            env$browser = function () {
                /* ????????? */
                var env = {
                    engine: "unknow",
                    engineVersion: "",
                    browser: "",
                    browserVersion: "",
                    isIE: false,
                    isEdge: false,
                    isChrome: false,
                    isFirefox: false,
                    isOpera: false,
                    isSafari: false
                }

                if (testUA(/applewebkit/)) {
                    env.engine = "webkit"
                    env.engineVersion = getVersion(/applewebkit\/([\d._]+)/)
                    env.browser = ""
                        || testUA(/edge/) && "edge"
                        || testUA(/opr/) && "opera"
                        || testUA(/chrome/) && "chrome"
                        || testUA(/safari/) && "safari"
                        || "unknow"
                }
                else if (testUA(/gecko/) && testUA(/firefox/)) {
                    env.engine = "gecko"
                    env.engineVersion = getVersion(/gecko\/([\d._]+)/)
                    env.browser = "firefox"
                }
                else if (testUA(/presto/)) {
                    env.engine = "presto"
                    env.engineVersion = getVersion(/presto\/([\d._]+)/)
                    env.browser = "opera"
                }
                else if (testUA(/trident/)) {
                    env.engine = "trident"
                    env.engineVersion = getVersion(/trident\/([\d._]+)/)
                    env.browser = "ie"
                }

                env.browserVersion = ""
                    || env.browser === "chrome" && (env.isChrome = true, getVersion(/chrome\/([\d._]+)/))
                    || env.browser === "safari" && (env.isSafari = true, getVersion(/version\/([\d._]+)/))
                    || env.browser === "firefox" && (env.isFirefox = true, getVersion(/firefox\/([\d._]+)/))
                    || env.browser === "opera" && (env.isOpera = true, getVersion(/opr\/([\d._]+)/))
                    || env.browser === "ie" && (env.isIE = true, getVersion(/(?:msie\s*|rv:)([\d._]+)/))
                    || env.browser === "edge" && (env.isEdge = true, getVersion(/edge\/([\d._]+)/))

                return env
            }(),
            env$shell = function () {
                /* ??????????????? */
                var env = {
                    shell: "",
                    shellVersion: ""
                }

                if (testUA(/micromessenger/)) {
                    env.shell = "wechat"
                    env.shellVersion = getVersion(/micromessenger\/([\d._]+)/)
                }
                else if (testUA(/qqbrowser/)) {
                    env.shell = "qq" // qq?????????
                    env.shellVersion = getVersion(/qqbrowser\/([\d._]+)/)
                }
                else if (testUA(/ucbrowser/)) {
                    env.shell = "uc" // uc?????????
                    env.shellVersion = getVersion(/ucbrowser\/([\d._]+)/)
                }
                else if (testUA(/qihu 360se/)) {
                    env.shell = "360" // 360?????????
                }
                else if (testUA(/2345explorer/)) {
                    env.shell = "2345" // 2345?????????
                    env.shellVersion = getVersion(/2345explorer\/([\d._]+)/)
                }
                else if (testUA(/metasr/)) {
                    env.shell = "sougou" // ???????????????
                }
                else if (testUA(/lbbrowser/)) {
                    env.shell = "liebao" // ???????????????
                }
                else if (testUA(/maxthon/)) {
                    env.shell = "maxthon" // ???????????????
                    env.shellVersion = getVersion(/maxthon\/([\d._]+)/)
                }

                return env
            }(),
            env = Object.assign(
                {
                    dev: false // ??????????????????
                },
                env$system,
                env$browser,
                env$shell
            )

        if (env.dev) {
            /** ????????????????????????????????????????????????????????????????????????????????????????????? dev ??? false???????????????????????????????????? js ??????????????? dev ??? false ????????????????????? */
            document.write("<script src='/cn/v3/js/toolkit_env_production.js'></script>")
        }

        module.exports = env
    }

    function polyfill() {
        extend(String.prototype, {
            startsWith: function (search, fromIndex) {
                if (fromIndex == Infinity) return false

                fromIndex = Math.max(fromIndex | 0, 0)

                return this.substring(fromIndex, fromIndex + search.length) === search
            },
            endsWith: function (search, endIndex) {
                if (endIndex == -Infinity) return false

                if (endIndex === undefined) {
                    endIndex = this.length
                }
                else {
                    endIndex = +endIndex

                    if (endIndex !== endIndex) {
                        endIndex = 0
                    }

                    endIndex = Math.min(endIndex, this.length)
                }

                return this.substring(endIndex - search.length, endIndex) === search
            },
            includes: function (search, start) {
                start |= 0

                if (start + search.length > this.length) {
                    return false
                } else {
                    return this.indexOf(search, start) !== -1
                }
            },
            padEnd: function (targetLength, padString) {
                targetLength |= 0
                padString = String(nvl(padString, ""))

                if (this.length >= targetLength) {
                    return String(this)
                }
                else {
                    targetLength = targetLength - this.length

                    if (targetLength > padString.length) {
                        padString += padString.repeat(targetLength / padString.length)
                    }

                    return String(this) + padString.slice(0, targetLength)
                }
            },
            padStart: function (targetLength, padString) {
                targetLength |= 0
                padString = String(nvl(padString, ""))

                if (this.length >= targetLength) {
                    return String(this)
                }
                else {
                    targetLength = targetLength - this.length

                    if (targetLength > padString.length) {
                        padString += padString.repeat(targetLength / padString.length)
                    }

                    return padString.slice(0, targetLength) + String(this)
                }
            },
            repeat: function (count) {
                if (this == null) {
                    throw new TypeError('String.prototype.repeat called on null or undefined')
                }

                var str = String(this)

                if (count == Infinity || count < 0) {
                    throw new RangeError('Invalid count value')
                }

                count |= 0

                if (str.length === 0 || count === 0) {
                    return ''
                }

                /**
                 * ???????????????????????? 1 << 28 ???????????????
                 */
                if (str.length * count >= 1 << 28) {
                    throw new RangeError('repeat count must not overflow maximum string size')
                }

                var result = ''

                /**
                 * ??????????????????????????????????????????????????????????????????????????? str ??????????????? str ????????????????????????????????????????????????????????? 1 ????????? str ????????? result???
                 * ??? 12 ?????????????????? 1100???????????? 8 + 4?????? 8 ??? str ??? 4 ??? str???
                 */
                do {
                    count & 1 && (result += str)
                    count >>>= 1
                    str += str
                } while (count > 0)

                return result
            },
            trim: function () {
                return this.replace(/^[\s\uFEFF\xA0]+|[\s\uFEFF\xA0]+$/g, '')
            },
            codePointAt: function (position) {
                if (this == null) {
                    throw new TypeError('String.prototype.codePointAt called on null or undefined')
                }

                var str = String(this),
                    len = str.length

                if (position < 0 || position >= len) {
                    return undefined
                }

                position |= 0

                var first = str.charCodeAt(position),
                    second

                if (
                    first >= 0xD800 && first <= 0xDBFF &&
                    len > position + 1
                ) {
                    second = str.charCodeAt(position + 1)

                    if (second >= 0xDC00 && second <= 0xDFFF) {
                        return (first - 0xD800) * 0x400 + second - 0xDC00 + 0x10000
                    }
                }

                return first
            },
            /**
             * ?????????????????? date
             * @param {string} format ????????????
             * 
             * '2017-05-26'.toDate('yyyy-MM-dd') => date
             */
            toDate: function (format) {
                if (!format) return null

                var str = this,
                    reg = /([yMdhmsS])\1*/g,
                    key = {},
                    tempKeys = format.match(reg), i = 0

                while (tempKeys.length) {
                    key[tempKeys.shift()[0]] = ++i
                }

                var r = str.match(format.replace(reg, function (m, v, i) {
                    return "(\\d{" + m.length + "})"
                }));

                var now = new Date,
                    y = now.getFullYear(),
                    M = now.getMonth() + 1,
                    d = now.getDate();

                return r && new Date(r[key.y] || y, (r[key.M] || M) - 1, r[key.d] || d, r[key.h] || 0, r[key.m] || 0, r[key.s] || 0, r[key.S] || 0);
            },
            /**
             * ???????????????????????????????????????????????????
             * @param {*} format ???????????????
             * @param {*} toFormat ??????????????????
             * 
             * * '2017-05-26'.dateFormat('yyyy-MM-dd','dd/MM/yyyy') => '26/05/2017'
             */
            dateFormat: function (format, toFormat) {
                var date = this.toDate(format)

                return date ? date.parse(toFormat) : ""
            }
        })

        extend(Function.prototype, {
            // ie8????????????bind??????
            bind: function (oThis) {
                if (typeof this !== 'function') {
                    throw new Error("bind???????????????")
                }

                var aArgs = Array.prototype.slice.call(arguments, 1), fToBind = this, fNOP = function () { },
                    fBound = function () {
                        return fToBind.apply(this instanceof fNOP ? this : oThis,
                            aArgs.concat(Array.prototype.slice.call(arguments)));
                    }

                fNOP.prototype = this.prototype;
                fBound.prototype = new fNOP();// fBound??????fNOP,?????????this instanceof fNOP??????fBound????????????new??????

                return fBound;
            }
        })

        extend(Date, {
            now: function () {
                return new Date().getTime()
            }
        })

        extend(Date.prototype, {
            /**
             * date ??????????????????
             * @param {string} format ????????????
             * 
             * * new Date().parse('yyyy-MM-dd hh:mm:ss') => '2017-05-26 16:21:16'
             */
            parse: function (format) {
                if (!format) return ""

                var date = this,
                    key = {
                        y: date.getFullYear(),
                        M: date.getMonth() + 1,
                        d: date.getDate(),
                        h: date.getHours(),
                        m: date.getMinutes(),
                        s: date.getSeconds()
                    },
                    reg = /([yMdhmsS])\1*/g,
                    str = format.replace(reg, function (m, v, i) {
                        var value = (key[v] || '') + "",
                            datestr = '0'.repeat(m.length) + value

                        return datestr.substr(datestr.length - Math.max(m.length, value.length));
                    })

                return str
            }
        })

        extend(Array.prototype, {
            filter: function (callback, thisArg) {
                if (this == null) {
                    throw new TypeError('Array.prototype.filter called on null or undefined')
                }

                if (typeof callback !== 'function') {
                    var callback$ = (typeof callback === 'object' && callback) ? Object.prototype.toString.call(callback) : String(callback)
                    throw new TypeError(callback$ + ' is not a function')
                }

                var o = Object(this),
                    len = o.length | 0,
                    i = 0,
                    res = []

                for (; i < len; i++) {
                    if (i in o) {
                        if (callback.call(thisArg, o[i], i, o)) {
                            res.push(o[i])
                        }
                    }
                }

                return res
            },
            find: function (callback, thisArg) {
                if (this == null) {
                    throw new TypeError('Array.prototype.find called on null or undefined')
                }

                if (typeof callback !== 'function') {
                    var callback$ = (typeof callback === 'object' && callback) ? Object.prototype.toString.call(callback) : String(callback)
                    throw new TypeError(callback$ + ' is not a function')
                }

                var o = Object(this),
                    len = o.length | 0,
                    i = 0

                for (; i < len; i++) {
                    if (callback.call(thisArg, o[i], i, o)) {
                        return o[i]
                    }
                }

                return Undefined
            },
            findIndex: function (callback, thisArg) {
                if (this == null) {
                    throw new TypeError('Array.prototype.findIndex called on null or undefined')
                }

                if (typeof callback !== 'function') {
                    var callback$ = (typeof callback === 'object' && callback) ? Object.prototype.toString.call(callback) : String(callback)
                    throw new TypeError(callback$ + ' is not a function')
                }

                var o = Object(this),
                    len = o.length | 0,
                    i = 0

                for (; i < len; i++) {
                    if (callback.call(thisArg, o[i], i, o)) {
                        return i
                    }
                }

                return -1
            },
            forEach: function (callback, thisArg) {
                if (this == null) {
                    throw new TypeError('Array.prototype.forEach called on null or undefined')
                }

                if (typeof callback !== 'function') {
                    var callback$ = (typeof callback === 'object' && callback) ? Object.prototype.toString.call(callback) : String(callback)
                    throw new TypeError(callback$ + ' is not a function')
                }

                var o = Object(this),
                    len = o.length | 0,
                    i = 0

                for (; i < len; i++) {
                    if (i in o) {
                        callback.call(thisArg, o[i], i, o)
                    }
                }
            },
            includes: function (value, fromIndex) {
                if (this == null) {
                    throw new TypeError('Cannot convert undefined or null to object')
                }

                var o = Object(this),
                    len = o.length | 0,
                    i = 0

                if (len <= 0) return false

                if (arguments.length > 1) {
                    fromIndex |= 0
                    i = fromIndex >= 0 ? fromIndex : Math.max(len + fromIndex, 0)
                }

                for (; i < len; i++) {
                    var x = o[i]

                    if (x === value || (x !== x && value !== value)) {
                        return true
                    }
                }

                return false
            },
            indexOf: function (value, fromIndex) {
                if (this == null) {
                    throw new TypeError('Cannot convert undefined or null to object')
                }

                var o = Object(this),
                    len = o.length | 0,
                    i = 0

                if (len <= 0) return -1

                if (arguments.length > 1) {
                    fromIndex |= 0
                    i = fromIndex >= 0 ? fromIndex : Math.max(len + fromIndex, 0)
                }

                for (; i < len; i++) {
                    if (i in o) {
                        if (o[i] === value) {
                            return i
                        }
                    }
                }

                return -1
            },
            lastIndexOf: function (value, fromIndex) {
                if (this == null) {
                    throw new TypeError('Cannot convert undefined or null to object')
                }

                var o = Object(this),
                    len = o.length | 0,
                    i = len - 1

                if (len <= 0) return -1

                if (arguments.length > 1) {
                    fromIndex |= 0
                    i = fromIndex >= 0 ? Math.min(i, fromIndex) : len + fromIndex
                }

                for (; i >= 0; i--) {
                    if (i in o) {
                        if (o[i] === value) {
                            return i
                        }
                    }
                }

                return -1
            },
            map: function (callback, thisArg) {
                if (this == null) {
                    throw new TypeError('Array.prototype.map called on null or undefined')
                }

                if (typeof callback !== 'function') {
                    var callback$ = (typeof callback === 'object' && callback) ? Object.prototype.toString.call(callback) : String(callback)
                    throw new TypeError(callback$ + ' is not a function')
                }

                var o = Object(this),
                    len = o.length | 0,
                    i = 0,
                    res = []

                for (; i < len; i++) {
                    if (i in o) {
                        res.push(callback.call(thisArg, o[i], i, o))
                    }
                }

                return res
            },
            reduce: function (callback, initialValue) {
                if (this == null) {
                    throw new TypeError('Array.prototype.reduce called on null or undefined')
                }

                if (typeof callback !== 'function') {
                    var callback$ = (typeof callback === 'object' && callback) ? Object.prototype.toString.call(callback) : String(callback)
                    throw new TypeError(callback$ + ' is not a function')
                }

                var o = Object(this),
                    len = o.length | 0,
                    i = 0,
                    value

                if (arguments.length > 1) {
                    value = initialValue
                }
                else {
                    while (i < len && !(i in o)) {
                        i++
                    }

                    if (i >= len) {
                        throw new TypeError('Reduce of empty array with no initial value')
                    }

                    value = o[i++]
                }

                for (; i < len; i++) {
                    if (i in o) {
                        value = callback(value, o[i], i, o)
                    }
                }

                return value
            },
            reduceRight: function (callback, initialValue) {
                if (this == null) {
                    throw new TypeError('Array.prototype.reduce called on null or undefined')
                }

                if (typeof callback !== 'function') {
                    var callback$ = (typeof callback === 'object' && callback) ? Object.prototype.toString.call(callback) : String(callback)
                    throw new TypeError(callback$ + ' is not a function')
                }

                var o = Object(this),
                    len = o.length | 0,
                    i = len - 1,
                    value

                if (arguments.length > 1) {
                    value = initialValue
                }
                else {
                    while (i >= 0 && !(i in o)) {
                        i--
                    }

                    if (i < 0) {
                        throw new TypeError('Reduce of empty array with no initial value')
                    }

                    value = o[i--]
                }

                for (; i >= 0; i--) {
                    if (i in o) {
                        value = callback(value, o[i], i, o)
                    }
                }

                return value
            },
            some: function (callback, thisArg) {
                if (this == null) {
                    throw new TypeError('Array.prototype.some called on null or undefined')
                }

                if (typeof callback !== 'function') {
                    var callback$ = (typeof callback === 'object' && callback) ? Object.prototype.toString.call(callback) : String(callback)
                    throw new TypeError(callback$ + ' is not a function')
                }

                var o = Object(this),
                    len = o.length | 0,
                    i = 0

                for (; i < len; i++) {
                    if (i in o) {
                        if (callback.call(thisArg, o[i], i, o)) {
                            return true
                        }
                    }
                }

                return false
            },
            every: function (callback, thisArg) {
                if (this == null) {
                    throw new TypeError('Array.prototype.every called on null or undefined')
                }

                if (typeof callback !== 'function') {
                    var callback$ = (typeof callback === 'object' && callback) ? Object.prototype.toString.call(callback) : String(callback)
                    throw new TypeError(callback$ + ' is not a function')
                }

                var o = Object(this),
                    len = o.length | 0,
                    i = 0

                for (; i < len; i++) {
                    if (i in o) {
                        if (!callback.call(thisArg, o[i], i, o)) {
                            return false
                        }
                    }
                }

                return true
            },
            at: function (index) {
                if (this == null) {
                    throw new TypeError('Array.prototype.at called on null or undefined')
                }

                if (index == Infinity) return Undefined

                var len = this.length

                index |= 0

                if (index < 0) index += len

                if (index < 0 || index >= len) return Undefined

                return this[index]
            },
            flat: function (deep) {
                if (this == null) {
                    throw new TypeError('Array.prototype.flat called on null or undefined')
                }

                deep = +nvl(deep, 1)

                if (deep !== deep) {
                    deep = 0
                }

                var o = Object(this)

                return flat(o)

                function flat(arr) {
                    if (deep <= 0) return arr

                    var result = []

                    for (var i = 0, len = arr.length; i < len; i++) {
                        var item = arr[i]

                        push(result, item instanceof Array ? flat(item, --deep) : item)
                    }

                    return result
                }
            }
        })

        var hasOwnProperty = Object.prototype.hasOwnProperty,
            hasDontEnumBug = !({ toString: null }).propertyIsEnumerable('toString'),
            dontEnums = [/*Bug: ?????????????????????????????? for...in ??????????????????*/
                'toString',
                'toLocaleString',
                'valueOf',
                'hasOwnProperty',
                'isPrototypeOf',
                'propertyIsEnumerable',
                'constructor'
            ],
            dontEnumsLength = dontEnums.length

        extend(Object, {
            assign: function (target/* , ...sources */) {
                if (target == null) {
                    throw new TypeError('Cannot convert undefined or null to object');
                }

                var o = Object(target),
                    len = arguments.length,
                    i = 1

                for (; i < len; i++) {
                    var source = arguments[i];

                    if (source != null) {
                        for (var key in source) {
                            if (Object.prototype.hasOwnProperty.call(source, key)) {
                                o[key] = source[key]
                            }
                        }
                    }
                }

                return o
            },
            create: function (proto) {
                if (typeof proto !== 'object' && typeof proto !== 'function') {
                    throw new TypeError('Object prototype may only be an Object or null: ' + proto);
                }

                function F() { }
                F.prototype = proto;

                return new F();
            },
            is: function (x, y) {
                /**
                 * +0 ??? -0 ?????????
                 * NaN ??? NaN ??????
                 */
                if (x === y) {
                    return x !== 0 || 1 / x === 1 / y
                } else {
                    return x !== x && y !== y
                }
            },
            keys: function (obj) {
                if (typeof obj !== 'object' && typeof obj !== 'function' || obj === null) throw new TypeError('Object.keys called on non-object');

                var result = [];

                for (var prop in obj) {
                    if (hasOwnProperty.call(obj, prop)) result.push(prop);
                }

                if (hasDontEnumBug) {
                    for (var i = 0; i < dontEnumsLength; i++) {
                        if (hasOwnProperty.call(obj, dontEnums[i])) result.push(dontEnums[i]);
                    }
                }
                return result;
            },
            values: function (obj) {
                if (typeof obj !== 'object' && typeof obj !== 'function' || obj === null) throw new TypeError('Object.keys called on non-object');

                var result = [];

                for (var prop in obj) {
                    if (hasOwnProperty.call(obj, prop)) result.push(obj[prop]);
                }

                if (hasDontEnumBug) {
                    for (var i = 0; i < dontEnumsLength; i++) {
                        if (hasOwnProperty.call(obj, dontEnums[i])) result.push(obj[dontEnums[i]]);
                    }
                }
                return result;
            }
        })

        extend(window, {
            console: function () {
                if (window.console) return

                var methods = ['assert', 'clear', 'count', 'debug', 'dir', 'dirxml', 'error', 'exception', 'group', 'groupCollapsed', 'groupEnd', 'info', 'log', 'markTimeline', 'profile', 'profileEnd', 'table', 'time', 'timeEnd', 'timeline', 'timelineEnd', 'timeStamp', 'trace', 'warn'],
                    noop = Function.prototype,
                    console = methods.reduce(function (console, method) {
                        console[method] = noop
                        return console
                    }, {})

                return console
            }(),
            requestAnimationFrame: function () {
                var lastTime = 0

                return function (cb) {
                    var curTime = +new Date,
                        timeToCall = Math.max(0, 16 - (curTime - lastTime)),
                        tid = window.setTimeout(cb, timeToCall)

                    lastTime = curTime + timeToCall

                    return tid
                }
            }(),
            cancelAnimationFrame: function (tid) {
                clearTimeout(tid)
            },
            atob: function (s) {
                s = s.replace(/\s|=/g, '')

                var base64hash = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/',
                    cur, prev, mod, i = 0, result = []

                while (i < s.length) {
                    cur = base64hash.indexOf(s.charAt(i));
                    mod = i % 4

                    switch (mod) {
                        case 0:
                            break;
                        case 1:
                            result.push(String.fromCharCode(prev << 2 | cur >> 4))
                            break;
                        case 2:
                            result.push(String.fromCharCode((prev & 0x0f) << 4 | cur >> 2))
                            break;
                        case 3:
                            result.push(String.fromCharCode((prev & 3) << 6 | cur))
                            break;
                    }

                    prev = cur
                    i++
                }

                return result.join('')
            },
            btoa: function (s) {
                if (/[^\u0000-\u00ff]/.test(s)) {
                    throw new Error('INVALID_CHARACTER_ERR')
                }

                var base64hash = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/',
                    i = 0, prev, ascii, mod, result = []

                while (i < s.length) {
                    ascii = s.charCodeAt(i)
                    mod = i % 3

                    switch (mod) {
                        case 0:
                            result.push(base64hash.charAt(ascii >> 2))
                            break;
                        case 1:
                            result.push(base64hash.charAt((prev & 3) << 4 | (ascii >> 4)))
                            break;
                        case 2:
                            result.push(base64hash.charAt(prev & 0x0f) << 2 | (ascii >> 6))
                            result.push(base64hash.charAt(ascii & 0x3f))
                    }

                    prev = ascii
                    i++
                }

                if (mod === 0) {
                    result.push(base64hash.charAt((prev & 3) << 4))
                    result.push('==')
                }
                else if (mod === 1) {
                    result.push(base64hash.charAt((prev & 0x0f) << 2))
                    result.push('=')
                }

                return result.join("")
            },
            Promise: function () {
                function Promise(resolver) {
                    if (typeof resolver !== 'function')
                        throw new TypeError('??????????????????????????????Promise??????1?????????');

                    if (!(this instanceof Promise))
                        return new Promise(resolver);

                    this._value;
                    this._reason;
                    this._status = 'PENDING';
                    this._resolves = null;
                    this._rejects = null;

                    var resolve = statusHandler.bind(this, 'RESOLVED'),
                        reject = statusHandler.bind(this, 'REJECTED')

                    try { resolver(resolve, reject) } catch (e) { reject(e) }
                }

                Promise.prototype = {
                    constructor: Promise,
                    then: function (onResolved, onRejected) {
                        var promise = this

                        return new Promise(function (resolve, reject) {
                            if (promise._status === 'PENDING') {
                                (promise._resolves || (promise._resolves = [])).push(resolveHandler);
                                (promise._rejects || (promise._rejects = [])).push(rejectHandler);
                            }
                            else if (promise._status === 'RESOLVED') {
                                addJob(resolveHandler.bind(null, promise._value))
                            }
                            else if (promise._status === 'REJECTED') {
                                addJob(rejectHandler.bind(null, promise._reason))
                            }

                            function resolveHandler(value) {
                                if (isPromise(value)) {
                                    value.then(resolveHandler, rejectHandler)
                                }
                                else if (typeof onResolved === 'function') {
                                    try { value = onResolved(value), resolve(value) } catch (e) { reject(e) }
                                }
                                else {
                                    resolve(value);
                                }
                            }

                            function rejectHandler(reason) {
                                if (typeof onRejected === 'function') {
                                    try { reason = onRejected(reason), resolve(reason) } catch (e) { reject(e) }
                                }
                                else {
                                    reject(reason);
                                }
                            }
                        });
                    },
                    "catch": function (onRejected) {
                        return this.then(Undefined, onRejected)
                    }
                }

                Promise.resolve = function (value) {
                    if (value instanceof Promise) return value

                    return new Promise(function (resolve, reject) {
                        if (typeof value === 'object' && typeof value['then'] === 'function') {
                            var thenable = value

                            thenable.then(function (value) {
                                resolve(value)
                            }, function (reason) {
                                reject(reason)
                            })
                        }
                        else {
                            resolve(value)
                        }
                    })
                }

                Promise.reject = function (reason) {
                    return new Promise(function (resolve, reject) {
                        reject(reason)
                    })
                }

                Promise.all = function (promises) {
                    if (!(promises instanceof Array)) {
                        throw new TypeError('???????????????Promise??????');
                    }

                    return new Promise(function (resolve, reject) {
                        var result = []

                        function resolver(index) {
                            return function (value) {
                                resolveAll(index, value);
                            };
                        }

                        function resolveAll(index, value) {
                            result[index] = value

                            if (--count === 0) {
                                resolve(result)
                            }
                        }

                        if (promises.length === 0) resolve([])

                        for (var i = 0, count = len = promises.length; i < len; i++) {
                            promises[i] && promises[i].then && promises[i].then(resolver(i), reject);
                        }
                    })
                }

                Promise.race = function (promises) {
                    if (!(promises instanceof Array)) {
                        throw new TypeError('???????????????Promise??????')
                    }

                    return new Promise(function (resolve, reject) {
                        for (var i = 0, len = promises.length; i < len; i++) {
                            promises[i].then(resolve, reject)
                        }
                    })
                }

                function statusHandler(status, value) {
                    var promise = this;

                    if (promise._status !== 'PENDING') return
                    if (promise === value) throw Error("????????????????????????Promise??????")

                    promise._status = status;

                    var isResolved = promise._status === 'RESOLVED',
                        callbacks = promise[isResolved ? '_resolves' : '_rejects']

                    addJob(function () {
                        if (!callbacks) {
                            if (!isResolved) {
                                var uncaughtError = "???????????????:" + (value instanceof Error ? value.message : String(value))

                                console.error(uncaughtError)
                            }

                            return
                        }

                        for (var i = 0; i < callbacks.length; i++) {
                            callbacks[i](value)
                        }

                        callbacks = null
                    })

                    promise[isResolved ? '_value' : '_reason'] = value;
                    promise['_resolves'] = promise['_rejects'] = null;
                }

                function isPromise(p) {
                    return p && typeof p === 'object' && typeof p['then'] === 'function'
                }

                var taskId = null,
                    jobQueue = null

                function addJob(job) {
                    if (!taskId) {
                        jobQueue = []
                        taskId = setTimeout(function () {
                            for (var i = 0; i < jobQueue.length; i++) {
                                jobQueue[i]()
                            }

                            jobQueue = null
                            taskId = null
                        })
                    }

                    jobQueue.push(job)
                }

                return Promise
            }(),
            Map: function () {
                function MapIterator(array) {
                    if (!(array instanceof Array)) return

                    var iterable = array.slice(0),
                        len = iterable.length,
                        curIndex = 0

                    this.next = function () {
                        if (curIndex >= len) return { value: Undefined, done: true }

                        var value = iterable[curIndex]

                        return { value: value, done: ++curIndex >= len }
                    }
                }

                function Map(mapIterable) {
                    if (!(this instanceof Map)) throw "???????????? Map ???????????? new ????????????"

                    this._collection = []
                    this.size = 0

                    if (mapIterable) {
                        if (!(mapIterable instanceof Array)) {
                            throw "???????????????????????????"
                        }

                        if (
                            !mapIterable.every(function (item) {
                                return item instanceof Array
                            })
                        ) {
                            throw "???????????????????????????"
                        }

                        var map = this
                        mapIterable.forEach(function (entry) {
                            map.set(entry[0], entry[1]);
                        })
                    }
                }

                Map.prototype = {
                    constructor: Map,
                    get: function (key) {
                        if (typeof key === "string" || typeof key === "number") {
                            return this.common && this.common[key]
                        }

                        var keyInfo = this._getKeyInfo(key)

                        return keyInfo && keyInfo.value
                    },
                    set: function (key, value) {
                        if (typeof key === "string" || typeof key === "number") {
                            this.common || (this.common = {})
                            this.common[key] = value
                            value = null
                        }

                        var _collection = this._collection,
                            keyInfo = this._getKeyInfo(key)

                        keyInfo ? (_collection[keyInfo.index + 1] = value) : _collection.push(key, value)

                        this.size = _collection.length / 2

                        return this
                    },
                    has: function (key) {
                        return Boolean(this._getKeyInfo(key))
                    },
                    clear: function () {
                        this.size = this._collection.length = 0
                    },
                    "delete": function (key) {
                        var _collection = this._collection,
                            keyInfo = this._getKeyInfo(key)

                        if (keyInfo) {
                            _collection.splice(keyInfo.index, 2)
                            this.size = _collection.length / 2
                        }

                        return Boolean(keyInfo)
                    },
                    forEach: function (fn) {
                        if (typeof fn !== "function") throw String(fn) + " ??????????????????"

                        var _collection = this._collection

                        for (var i = 0, len = _collection.length; i < len; i += 2) {
                            var key = _collection[i],
                                value = _collection[i + 1]

                            fn(value, key, this)
                        }
                    },
                    entries: function () {
                        var entries = []

                        this.forEach(function (value, key) {
                            entries.push([key, value])
                        })

                        return new MapIterator(entries)
                    },
                    keys: function () {
                        var keys = []

                        this.forEach(function (value, key) {
                            keys.push(key)
                        })

                        return new MapIterator(keys)
                    },
                    values: function () {
                        var values = []

                        this.forEach(function (value) {
                            values.push(value)
                        })

                        return new MapIterator(values)
                    },
                    toJSON: function () {
                        var json = []

                        this.forEach(function (value, key) {
                            json.push([key, value])
                        })

                        return json
                    },
                    _getKeyInfo: function (key) {
                        var _collection = this._collection

                        for (var i = 0, len = _collection.length; i < len; i += 2) {
                            var _key = _collection[i]

                            if (_key === key) return { value: _collection[i + 1], index: i }
                        }
                    }
                }

                return Map
            }()
        })

        extend(window.Promise, {
            delay: function (time) {
                return new Promise(function (resolve) {
                    setTimeout(resolve, time)
                })
            }
        })
    }

    function exportModules(userModules) {
        var modules = {}, allExports = {}

        for (var name in userModules) {
            require(name)
        }

        function require(name) {
            if (userModules.hasOwnProperty(name) && !modules.hasOwnProperty(name)) {
                var exports = {},
                    module = modules[name] = { exports: exports }

                if (!isFunction(userModules[name])) {
                    return logError("?????????????????????????????????" + name + "?????????????????????", userModules[name])
                }

                userModules[name](require, module, exports)

                if (module.exports === exports) { // ???exports.x1 = xxx1, exports.x2 = xxx2??? x1, x2 ????????????????????????
                    for (var name$ in exports) {
                        if (!exports.hasOwnProperty(name$)) continue
                        if (!allExports.hasOwnProperty(name$)) {
                            allExports[name$] = exports[name$]
                        }
                        else {
                            logError("????????????????????????" + name$ + "??????????????????")
                        }
                    }
                }
                else if (!allExports.hasOwnProperty(name)) { //???module.exports = xxx??? xxx ??????????????????
                    allExports[name] = module.exports
                }
                else {
                    logError("????????????????????????" + name + "??????????????????")
                }
            }

            return modules[name].exports
        }

        return allExports
    }

    function logWarning(msg) {
        if (window.console && isFunction(console.warn)) {
            print(console.warn, slice(arguments))
        }

        return msg
    }

    function logError(msg) {
        if (window.console && isFunction(console.error)) {
            print(console.error, slice(arguments))
        }

        return msg
    }

    function logTypeError(msg, expected, butGot) {
        return logError(msg + "???????????????\"" + expected + "\"???????????????\"" + butGot + "\"")
    }

    function print(stdout, args) {
        if (stdout.apply) {
            stdout.apply(null, args)
        }
        else {
            /**
             * IE8 ??? console ????????? apply ??????
             */
            var evalArgs = []

            for (var i = 0, len = args.length; i < len; i++) {
                evalArgs.push("args[" + i + "]")
            }

            eval("stdout(" + evalArgs.join(",' ',") + ")")
        }
    }

    function genConsole() {
        if (genConsole.myConsole) return genConsole.myConsole

        var myConsole = null

        return myConsole = genConsole.myConsole = {
            head: function (head$) {
                var console$ = this

                if (console$ === myConsole) {
                    console$ = Object.assign({}, myConsole)
                }

                console$.head$ = head$

                return console$
            },
            stdout: function (stdout$) {
                if (!isFunction(stdout$)) return this

                var console$ = this

                if (console$ === myConsole) {
                    console$ = Object.assign({}, myConsole)
                }

                console$.stdout$ = stdout$

                return console$
            },
            print: function (message) {
                if (!isArray(message)) {
                    message = slice(arguments)
                }

                var title = this.padLeft || this.head$ || "",
                    stdout = this.stdout$ || window.console && console.log,
                    output = title ? [title].concat(message) : message

                if (!stdout) return this

                if (stdout.apply) {
                    stdout.apply(null, output)
                }
                else {
                    /**
                     * IE8 ??? console ????????? apply ??????
                     */
                    var output_list = []

                    for (var i = 0, len = output.length; i < len; i++) {
                        output_list.push("output[" + i + "]")
                    }

                    eval("stdout(" + output_list.join(",' ',") + ")")
                }

                return this.head$ && !this.padLeft
                    ? Object.assign({ padLeft: "-".repeat(charLength(this.head$)) }, this)
                    : this
            },
            printLines: function (messages) {
                if (!isArray(messages)) {
                    messages = slice(arguments)
                }

                var console$ = this

                for (var i = 0; i < messages.length; i++) {
                    var message = messages[i]

                    if (!message) continue

                    console$ = console$.print(message)
                }
            }
        }
    }

    function deepProxy(obj, handler) {
        if (!window.Proxy) return obj

        return genProxy(obj)

        function genProxy(obj) {
            if (isArray(obj)) {
                for (var i = 0, len = obj.length; i < len; i++) {
                    var item = obj[i]

                    if (isArray(item) || isPlainObject(item)) {
                        obj[i] = genProxy(item)
                    }
                }
            }
            else if (isPlainObject(obj)) {
                for (var key in obj) {
                    if (obj.hasOwnProperty(key)) {
                        var item = obj[key]

                        if (isArray(item) || isPlainObject(item)) {
                            obj[key] = genProxy(item)
                        }
                    }
                }
            }

            return new Proxy(obj, handler)
        }
    }

    function nextTick(fn, context) {
        if (isUndef(nextTick.fns)) {
            nextTick.fns = []

            Promise.resolve().then(function () {
                var fns = nextTick.fns
                nextTick.fns = null

                for (var i = 0, len = fns.length; i < len; i++) {
                    fns[i]()
                }
            })
        }

        if (isFunction(fn)) {
            context && (fn = fn.bind(context))
            nextTick.fns.push(fn)
        }
    }

    function cache(fn, genCacheKey) {
        var cacheMap = {}

        return isFunction(genCacheKey)
            ? function () {
                var key = genCacheKey.apply(null, arguments)
                if (key in cacheMap) return cacheMap[key]

                return cacheMap[key] = fn.apply(null, arguments)
            }
            : function () {
                var key = arguments.length ? String(arguments[0]) : "__key__"
                if (key in cacheMap) return cacheMap[key]

                return cacheMap[key] = fn.apply(null, arguments)
            }
    }

    function push(arrA, arrB) {
        return isArray(arrB) ? arrA.push.apply(arrA, arrB) : arrA.push(arrB)
    }

    function slice(likeArray, sIdx, eIdx) {
        if (isUndef(sIdx)) sIdx = 0
        if (isUndef(eIdx)) eIdx = likeArray.length
        return Array.prototype.slice.call(likeArray, sIdx, eIdx)
    }

    function JSONStringify(json) {
        return JSON.stringify(json, function (key, val) {
            return isFunction(val) ? "FUNCTION" : val
        })
    }

    function nvl(valueA, valueB) {
        return isDef(valueA) ? valueA : valueB
    }

    function isPlainObject(a) {
        return isObject(a) && a.constructor === Object
    }

    function isEmptyObject(o) {
        if (isPlainObject(o)) {
            for (var key in o) {
                if (o.hasOwnProperty(key)) {
                    return false
                }
            }

            return true
        }

        return false
    }

    function isNotEmptyObject(o) {
        if (isPlainObject(o)) {
            for (var key in o) {
                if (o.hasOwnProperty(key)) {
                    return true
                }
            }
        }

        return false
    }

    function isObject(a) {
        return a !== null && typeof a === 'object'
    }

    function isArray(a) {
        return a instanceof Array
    }

    function isBoolean(a) {
        return typeof a === "boolean"
    }

    function isFunction(a) {
        return typeof a === "function"
    }

    function isString(a) {
        return typeof a === "string"
    }

    function isRealString(a) {
        return isString(a) && a !== ""
    }

    function isInteger(a) {
        return !isNaN(a) && a === (a | 0)
    }

    function isUndef(a) {
        return a == Undefined
    }

    function isDef(a) {
        return a != Undefined
    }

    function isEqual(a, b) {
        return a === b || (a !== a && b !== b)
    }

    function noop() { }

    function matchWith(str) {
        var list = str.split(","), map = {}

        for (var i = 0; i < list.length; i++) {
            map[list[i]] = !0
        }

        return function (t) {
            return map[t]
        }
    }

    function each(iterable, fn, thisArg) {
        if (isArray(iterable)) {
            for (var i = 0, len = iterable.length; i < len; i++) {
                fn.call(thisArg, iterable[i], i)
            }
        }
        else if (isObject(iterable) && isFunction(iterable.next)) {
            for (var i = 0, result = null; (result = iterable.next()) && !result.done; i++) {
                fn.call(thisArg, result.value, i)
            }
        }
        else {
            fn.call(thisArg, iterable, 0)
        }
    }

    function charLength(str) {
        if (!isString(str)) return 0

        var chineseCount = str.match(/[\u4e00-\u9fa5]/g)

        return str.length + (chineseCount ? Math.ceil(chineseCount.length * 0.8) : 0)
    }

    function testLocalStorage() { // ??????localStorage???????????????,?????????????????????????????????,??????????????????
        if (window.localStorage) {
            try { localStorage.setItem('testLocalStorage', '') }
            catch (e) { return false }

            localStorage.removeItem('testLocalStorage')

            return true;
        }

        return false;
    }

    function extend(target, obj) {
        for (var k in obj) {
            if (!(k in target)) {
                target[k] = obj[k]
            }
        }
    }
}())