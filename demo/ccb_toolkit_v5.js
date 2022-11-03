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
            hasKeyPath = utils.hasKeyPath,
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

        var userHookEvent = function (hook) { return "hook:" + hook },
            userHooks = [
                "receiveProps", "beforePatch",
                "beforeMount", "mounted", "allMounted",
                "beforeUpdate", "updated", "allUpdated",
                "beforeUnmount", "unmounted"
            ],
            componentModelEvent = function (propName) { return "update:" + propName },
            isUserHookEvent = matchWith(userHooks.map(userHookEvent)),
            isReservedAttr = matchWith("style", "class", "key"),
            Reg$SplitComma = /\s*,\s*/,
            $$id = 0,
            currentInstance = null,
            DepTarget = null,
            patchCallbacks = []

        function Parser(config, componentData) {
            if (!config) throw this._logError("组件实例化失败，缺少选项对象参数")

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

                this.baseContext.$el = this.el
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
                this.el = null // 在 IOS 中部分浏览器的点击事件不能绑定在 body 元素上,所以 el 最好不要使用 body，或者使用 touchstart 事件代替点击事件。
                this.runtimeHooks = null
                this.refNode = null
                this.vdom = null
                this.onceCache = null
                this.observer = new Observer()
                this.shortCache = new ShortCache()

                this._normalizeConfig(config)

                this.template = config.template
                this.render = config.__render__ // 渲染函数，由组件缓存提供，每个组件只会编译一次渲染函数，由所有组件实例共享。

                this._initState(config)

                this._initHooks(config)

                this._initPrivateStyle(config)

                this._initComponents(config)

                this._initBaseContext()

                this._initStore(config)

                this._initMethods(config)

                this._initPropsConfig(config)

                this._initEmitsConfig(config)

                this._handleComponentData(componentData)

                this._initDataContext(config)

                this._markObservables(config)

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

                    for (var i = 0; i < userHooks.length; i++) {
                        var hook = userHooks[i];
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
                    this._logError("props 选项只能是数组或对象")
                    config.props = Undefined
                }
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
                    this._logError("emits 选项只能是数组或对象")
                    config.emits = Undefined
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

                userHooks.forEach(function (hook) {
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
            _initComponents: function (config) {
                var userDefineComponents = config.components,
                    localComponents = isPlainObject(userDefineComponents) && Object.assign({}, userDefineComponents)

                this.getComponent = function (name) {
                    return localComponents && localComponents[name] || Component.public[name]
                }
            },
            _initBaseContext: function () {
                function BaseContext() { }// 存放提供给用户使用的内部方法及属性
                function DataContext() { }// 存放 methods, data, props, computed 等用户定义的数据
                function Context() { } // 存放由 for 指令派生的别名数据

                this.Context = inherit(Context, inherit(DataContext, BaseContext))
                this.dataContext = Context.prototype
                this.baseContext = DataContext.prototype

                var instance = this,
                    $nextTick = function (fn) {
                        return nextTick(fn, this)
                    },
                    $setData = function (keyPath, value) {
                        return instance._setData(keyPath, value)
                    }

                $setData.force = function (keyPath, value) {
                    return instance._setData(keyPath, value, true)
                }

                Object.assign(
                    this.baseContext,
                    {
                        $nextTick: $nextTick,
                        $setData: $setData,
                        $emit: this._emit.bind(this),
                        $mount: this.mount.bind(this),
                        $destroy: this.destroy.bind(this),
                        $refs: {},
                        $attrs: {},
                        $elements: [],
                        $watch: null,
                        $parent: null,
                        $store: null,
                        $el: null,
                        __instance__: this
                    }
                )
            },
            _initStore: function (config) {
                var store = config.store

                if (isUndef(store)) return

                if (store !== store.getRaw()) {
                    var instance = this,
                        release = store.onupdate(function (changeState, causes) {
                            if (!causes.length) return

                            instance._setDirty("store")
                            instance.observer.update(causes.map(function (causeKeyPath) {
                                return "$store." + causeKeyPath
                            }))
                        })

                    this._on("beforeUnmount", release)
                } else {
                    store = store.provide()
                }

                this.baseContext.$store = store
            },
            _initMethods: function (config) {
                var userDefineMethods = config.methods,
                    methods = this.methods = {}

                if (isUndef(userDefineMethods)) return

                var instance = this,
                    initMethod = normailzeSurrogate(function (method, name) {
                        var methodDeps = Undefined

                        return function () {
                            var context = instance.context || instance.dataContext

                            if (isUndef(context)) return instance._logWarning("组件已销毁，" + name + " 方法调用失败")

                            if (DepTarget) {
                                if (methodDeps === Undefined) {
                                    methodDeps = collectFunctionDeps(method, instance.observables)
                                }

                                if (methodDeps) {
                                    DepTarget.collect(instance.observer, methodDeps)
                                }
                            }

                            return method.apply(context, arguments)
                        }
                    })

                for (var name in userDefineMethods) {
                    methods[name] = initMethod(userDefineMethods[name], name)
                }
            },
            _initPropsConfig: function (config) {
                var userDefineProps = config.props

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
                        throw this._logError(genErrorMsg("保留关键字，不能作为组件 prop"))
                    }

                    var propDefine = userDefineProps[propName]

                    if (isPlainObject(propDefine)) {
                        var type = propDefine.type,
                            required = Boolean(propDefine.required),
                            validator = propDefine.validator,
                            defaultVal = propDefine["default"]

                        if (validator && !isFunction(validator)) {
                            this._logError(genErrorMsg('validator 需要函数'))
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
                            this._logError(genErrorMsg("type 需要构造函数"))
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
                    return "props 选项配置错误：【" + propName + "】，" + message
                }

                this.propsConfig = propsConfig
            },
            _initEmitsConfig: function (config) {
                var userDefineEmits = config.emits

                if (!isPlainObject(userDefineEmits)) return

                var emitsConfig = this.emitsConfig = {}

                for (var name in userDefineEmits) {
                    var emitsValidator = userDefineEmits[name]

                    emitsConfig[name] = isFunction(emitsValidator) ? emitsValidator : null
                }
            },
            _handleComponentData: function (componentData) {
                if (isUndef(componentData)) return

                this.state.isRoot = false

                this.componentData = componentData
                this.name = componentData.name
                this.domEventManager = componentData.domEventManager
                this.componentCallback = componentData.complete
                this.baseContext.$parent = componentData.parentContext

                this._installComponentChildren(componentData.children)
                this._installComponentEvents(componentData.events)
                this._installComponentProps(componentData.props)
                this._installComponentAttributes(componentData.props, componentData.events)
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

                var props = this.props = {}

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
                            this._logError("【" + propName + "】缺少必要的 prop")
                            continue
                        }
                    }

                    if (isFunction(validator)) {
                        isValid = validator(propVal)

                        if (!isValid) {
                            this._logWarning(["【" + propName + "】prop 自定义验证失败", ["接收到的值：", propVal]])
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

                            this._logWarning(["【" + propName + "】prop 的值不是【" + notMatchType + "】类型", ["接收到的值：", propVal]])
                            continue
                        }
                    }

                    props[propName] = isValid ? propVal : Undefined
                }
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
                            isUserHookEvent(type)/* hook:mounted ... */ ||
                            emitsConfig && emitsConfig.hasOwnProperty(type)
                        ) continue

                        componentAttrs["@event"] || (componentAttrs["@event"] = [])
                        componentAttrs["@event"].push(eventInfo)
                    }
                }

                this.baseContext.$attrs = componentAttrs
                this.componentAttrs = isNotEmptyObject(componentAttrs) ? componentAttrs : null
            },
            _initDataContext: function (config) {
                var dataContext = this.dataContext,
                    methods = this.methods,
                    props = this.props

                for (var methodName in methods) {
                    this._checkUserDefineName(methodName, "methods")
                    dataContext[methodName] = methods[methodName]
                }

                for (var propName in props) {
                    this._checkUserDefineName(propName, "props")
                    dataContext[propName] = props[propName]
                }

                var initData = config.data

                if (isUndef(initData)) return

                if (!isFunction(initData)) throw this._logError("data 选项需使用函数方式定义")

                var data = initData.call(dataContext)

                if (!isPlainObject(data)) throw this._logError("data 选项必需返回对象")

                for (var key in data) {
                    if (!data.hasOwnProperty(key)) continue

                    this._checkUserDefineName(key, "data")
                    dataContext[key] = data[key]
                }
            },
            _updateDataContext: function (keyPath, value, force) {
                if (this.state.destroy) return false

                var contextPatch

                if (isString(keyPath)) {
                    contextPatch = {}
                    contextPatch[keyPath] = value
                } else if (isPlainObject(keyPath)) {
                    contextPatch = keyPath
                    force = value
                }

                if (!contextPatch) return false

                var dataContext = this.dataContext,
                    context = this.context || dataContext,
                    isChange = false,
                    changePaths = []

                for (var path in contextPatch) {
                    var value = contextPatch[path],
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
                    this._setDirty("context")
                    this.observer.update(changePaths)
                }

                return isChange
            },
            _markObservables: function (config) {
                var observables = this.observables = {},
                    dataContext = this.dataContext,
                    userDefineComputed = config.computed,
                    userDefineMethods = config.methods

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

                if (this.baseContext.$store) {
                    observables["$store"] = Undefined
                }

                if (userDefineMethods) {
                    Object.assign(observables, userDefineMethods)
                }
            },
            _initComputed: function (userDefineComputed) {
                if (isUndef(userDefineComputed)) return

                var dataContext = this.dataContext,
                    observer = this.observer,
                    observables = this.observables,
                    computeds = {}

                for (var name in userDefineComputed) {
                    this._checkUserDefineName(name, "computed")

                    if (isFunction(userDefineComputed[name])) {
                        computeds[name] = userDefineComputed[name]
                    }
                    else {
                        throw this._logError("computed 的【" + name + "】必须使用函数定义")
                    }
                }

                for (var name in computeds) {
                    var inited = dataContext.hasOwnProperty(name)

                    if (inited) continue

                    init(name, computeds[name])
                }

                /**清除闭包内没用的数据 */
                computeds = observables = init = null

                function init(name, computed) {
                    var computedDeps = collectFunctionDeps(computed, observables)

                    var computed$ = createDepTarget(computed.bind(dataContext), function onDepUpdate() {
                        var oldValue = dataContext[name],
                            value = dataContext[name] = computed$()

                        !isEqual(oldValue, value) && observer.update(name)
                    })

                    if (computedDeps) {
                        computedDeps.forEach(function (keyPath) {
                            var pathKeys = pathResolve(keyPath),
                                name$ = pathKeys[0],
                                isUninitComputed = computeds.hasOwnProperty(name$) && !dataContext.hasOwnProperty(name$)

                            if (!isUninitComputed) return

                            init(name$, computeds[name$])
                        })

                        computed$.collect(observer, computedDeps)
                    }

                    dataContext[name] = computed$()
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

                        if (!isString(keyPath)) return instance._logError("watch 的第一个参数 keyPath 必须是字符串，接收到【" + keyPath + "】")
                        if (!isFunction(handler)) return instance._logError("watch 的第二个参数 handler 必须是函数")

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

                                try {
                                    handler.call(context, oldValue, newValue)
                                } catch (err) {
                                    instance._logError(err)
                                }
                            })

                            instance._startUpdate()
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
                            })
                        })

                        immediateHandlers = Undefined

                        this.run()
                    }
                }

                this.baseContext.$watch = function (keyPath, handler, config) {
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

                    if (isString(handler) && isFunction(instance.methods[handler])) {
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
                        _logError(keyPath, "在 methods 中未找到【" + handler + "】方法")
                    }
                    else {
                        _logError(keyPath, "未正确配置 handler")
                    }
                }

                function _logError(keyPath, message) {
                    instance._logError("watch 配置错误：【" + keyPath + "】，" + message)
                }

                return watchConfigs
            },
            _compile: function (template) {
                var instance = this,
                    render = this.render,
                    renderHelperMap = this._createRenderHelper(),
                    renderHelperNames = Object.keys(renderHelperMap),
                    renderHelpers = renderHelperNames.map(function (name) {
                        return renderHelperMap[name]
                    })

                /**清除闭包内没用的数据 */
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
                                throw Error("不存在的 token 类型")
                            }
                        }
                    })

                    var renderCode = rootToken.code

                    try {
                        render = Function.apply(Function, renderHelperNames.concat(renderCode))
                    } catch (e) {
                        throw this._logError([
                            "构建渲染函数失败",
                            ["错误信息：", e],
                            ["构建代码：", renderCode]
                        ])
                    }

                    render.deps = convertor.depCollector.getDeps()
                    this.render = render

                    /**清除闭包内没用的数据 */
                    convertor = null
                }

                var state = this.state,
                    isRoot = state.isRoot,
                    name = this.name,
                    render$ = createDepTarget(render, function onDepUpdate() {
                        state.shouldTemplateReRender = true
                        instance._startUpdate()
                    })

                if (render.deps) {
                    render$.collect(instance.observer, render.deps)
                }

                this.renderVdom = function (context) {
                    try {
                        var vdom = render$.apply(context, renderHelpers)

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
                            "执行渲染函数失败",
                            ["错误信息：", e],
                            ["渲染函数：", render]
                        ])
                    }
                }
            },
            _createConvertor: function () {
                var instance = this,
                    depCollector = createDepCollector(),
                    tokenStack = [],
                    uniq = {},
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
                            if (instance.state.isRoot) return instance._logWarning("根组件不能使用 slot 插槽")

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
                                hasMustache = Reg$MustacheContent.test(value)

                            markLocation(attrData.loc)

                            if (exist[attrName]) {
                                instance._logWarning('存在重复属性【' + name + '】')
                            }

                            exist[attrName] = true

                            switch (type) {
                                case "event":
                                    if (hasMustache)
                                        throwError('事件绑定不能使用 Mustache 标签')

                                    depCollector.collect(value)
                                    addEventInfo(name, value, attrData.modifers, attrs, token)

                                    continue
                                case "slotInfo":
                                    if (hasMustache)
                                        throwError('组件子元素的作用域插槽参数列表,不能使用 Mustache 标签，正确写法：#default="paramA, paramB"')

                                    token.slotInfo = { name: name, slotScope: value || null }

                                    continue
                                case "directive":
                                    var isPureDirective = 0
                                        || name === "allow-html"
                                        || name === "else"
                                        || name === "once"

                                    if (!isPureDirective && !value)
                                        throwError(name + ' 指令的参数不能为空')

                                    if (isPureDirective && value) {
                                        instance._logWarning(name + ' 指令不需要参数')
                                        value = Undefined
                                    }

                                    if (hasMustache)
                                        throwError('指令参数不能使用 Mustache 标签')

                                    /**
                                     * for 指令的参数是特殊语法，不能直接收集依赖。
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
                                            param: propName,
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
                                            throwError('slot 标签的 name 属性必须是静态字符串，不能使用动态属性或 Mustache 标签')

                                        token.slotName = name
                                        continue
                                    }

                                    if (isDynamic && hasMustache)
                                        throwError('动态属性不能使用 Mustache 标签')

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
                            token.parent.type === "root" && // 根节点
                            !instance.state.isRoot && // 不是根实例
                            instance.state.inheritAttrs // 允许继承非 prop 属性
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

                    var name = attr.name

                    var attrTypes = { "@": "event", "#": "slotInfo", ":": "dynamicProp", "$": "directive" },
                        type = attrTypes[name[0]]

                    if (type) {
                        attr.name = name = name.substring(1)
                        attr.type = type

                        if (type === "directive" && ~name.indexOf(":")) {
                            var tuple = name.split(":")
                            attr.name = name = tuple[0]
                            attr.directiveProp = tuple[1]
                        }
                    }

                    var Reg$Modifiers = /(\.[\w-]+)+/,
                        matcher = name.match(Reg$Modifiers)

                    if (matcher) {
                        attr.name = name = name.replace(matcher[0], "")
                        attr.modifiers = genModifiers(matcher[0])
                    }

                    return attr
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
                 * 搜集模板依赖的数据，当这些数据变更时，才会重新渲染模板。
                 */
                function createDepCollector() {
                    var collects = {},
                        observables = {}

                    for (var name in instance.dataContext) {
                        if (instance.dataContext.hasOwnProperty(name) && !instance.methods.hasOwnProperty(name)) {
                            observables[name] = Undefined
                        }
                    }

                    if (instance.baseContext.$store) {
                        observables["$store"] = Undefined
                    }

                    /**
                     * 'head.keyA[1].keyB["keyC"].indexOf(...)' -> head.keyA[1].keyB["keyC"] 不匹配对象的方法调用
                     */
                    // var keyPathReg = "(([\\w$]+)(?:(?=(\\.[\\w$]+|\\[\\s*(?:\\d+|([\"']).+?\\4)\\s*\\]))\\3(?!\\s*\\())*)",
                    //     Reg$KeyPathInTemplate = new RegExp("(?:^|[^\\s.\\[\"']\\b)\\s*" + keyPathReg, "g")
                    var Reg$KeyPathInTemplate = /(?=([\w$]+))\1(?:\.(?=([\w$]+))\2|\[[^\]]*\])*(?!\s*[\'"\]()])/g

                    return {
                        collect: function (expression) {
                            var matcher = null

                            while (matcher = Reg$KeyPathInTemplate.exec(expression)) {
                                var keyPath = matcher[0],
                                    head = matcher[1]

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
                    var directive = token.directives["model"]

                    if (!directive) return

                    var attrs = token.lastAttrs,
                        eventName = "",
                        eventHandler = "",
                        modelPath = "",
                        modifiers = null

                    if (token.isComponent) {
                        var modelDirectives = directive

                        for (var i = 0, len = modelDirectives.length; i < len; i++) {
                            var directive$ = modelDirectives[i],
                                propName = directive$.param

                            markLocation(directive$.loc)

                            eventName = componentModelEvent(propName)
                            eventHandler = "$model.component"
                            modelPath = verifyModelBinding(directive$.value)

                            addEventInfo(eventName, callMethod(eventHandler, addDoubleQuot(modelPath), "$args[0]"), modifiers, attrs, token)
                            attrs[propName] = modelPath
                        }

                        return
                    }

                    markLocation(directive.loc)

                    if (token.genTransitionCode) return instance._logWarning("transition 不能使用 model 指令")
                    if (token.genSlotCode) return instance._logWarning("slot 不能使用 model 指令")

                    var tagName = token.tagName,
                        inputType = token.staticAttrs.type || 'text',
                        isInput = tagName === 'input' && ~'text,number,password,search,email,tel,url'.indexOf(inputType),
                        isCheckBox = tagName === 'input' && inputType === 'checkbox',
                        isRadio = tagName === 'input' && inputType === 'radio',
                        isTextarea = tagName === 'textarea',
                        isSelect = tagName === 'select',
                        bindingHandler = ""

                    modelPath = verifyModelBinding(directive.value)

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
                        throwError("model 指令只能用于组件及表单元素")
                    }

                    addEventInfo(eventName, callMethod(eventHandler, "$event", addDoubleQuot(modelPath)), modifiers, attrs, token)

                    token.code = genCode(function (code) {
                        return callMethod(bindingHandler, code(), modelPath)
                    }, token.code)
                }

                //todo 要支持绑定派生数据，不能在这里检查
                function verifyModelBinding(name) {
                    if (instance._existInContext(name, "data")) {
                        return name
                    }

                    // if (instance._existInContext(name, "props")) {//props不能$setData 不符合双向绑定的定义？？
                    //     if (instance.emitsConfig && instance.emitsConfig.hasOwnProperty(componentModelEvent(name))) {
                    //         return name
                    //     }
                    //     throwError('使用 model 指令双向绑定 props 的属性时，必须在 emits 选项中明确声明"' + componentModelEvent(name) + '"事件')
                    // }

                    if (hasKeyPath(instance.baseContext, name)) {
                        return name
                    }

                    throwError("model 指令只能使用 data 或 $store 的状态，接收到【" + name + "】")
                }

                function processShow(token) {
                    var directive = token.directives["show"]

                    if (!directive) return

                    markLocation(directive.loc)

                    if (token.genTransitionCode) return instance._logWarning("transition 不能使用 show 指令")

                    token.code = genCode(function (code) {
                        return callMethod("__show__", code(), directive.value)
                    }, token.code)
                }

                function processRef(token) {
                    var directive = token.directives["ref"]

                    if (!directive) return

                    markLocation(directive.loc)

                    if (token.genTransitionCode) return instance._logWarning("transition 不能使用 ref 指令")
                    // if (token.genSlotCode) return instance._logWarning("slot 不能使用 ref 指令")
                    if (token.genBlockCode) return instance._logWarning("block 不能使用 ref 指令")
                    if (uniq[directive.value]) return instance._logWarning("ref 指令使用的名称重复：" + directive.value)

                    token.code = genCode(function (code) {
                        var isArrayRef = tokenStack.length

                        return callMethod("__saveRef__", addDoubleQuot(directive.value), isArrayRef ? "true" : "false", code())
                    }, token.code)
                }

                function processFor(token) {
                    var directive = token.directives["for"]

                    if (!directive) return

                    markLocation(directive.loc)

                    if (token.genSlotCode) return instance._logWarning("slot 不能使用 for 指令")

                    var matcher = directive.value.match(Reg$LoopDirective),
                        alias = (matcher[1] || matcher[2]).trim().split(Reg$SplitComma),
                        valueAlias = alias[0],// 数据项
                        indexAlias = alias[1],// 数组索引 or 对象键名
                        objectIndexAlias = alias[2],// 对象键索引
                        source = matcher[3],// 数据源
                        rangeMatcher = source.match(Reg$RangeGrammar)

                    if (
                        valueAlias === indexAlias ||
                        valueAlias === objectIndexAlias ||
                        (indexAlias && indexAlias === objectIndexAlias)
                    ) {
                        throwError("for 指令中存在重复的别名")
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
                    var directive = token.directives["once"]

                    if (!directive) return

                    markLocation(directive.loc)

                    if (token.genTransitionCode) return instance._logWarning("transition 不能使用 once 指令")
                    if (token.genSlotCode) return instance._logWarning("slot 不能使用 once 指令")

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
                    var directive = token.directives["if"]

                    if (!directive) return

                    markLocation(directive.loc)

                    checkBranchDirective(token)

                    token.branchKey = genStaticId()

                    token.code = genCode(function (code) {
                        return directive.value + "?" + code() + ": null"
                    }, token.code)
                }

                function processElseIf(token) {
                    var directive = token.directives["else-if"]

                    if (!directive) return

                    markLocation(directive.loc)

                    checkBranchDirective(token)

                    var tokenWithIf = findIf(token)

                    token.branchKey = genStaticId()

                    token.code = genCode(function (code) {
                        return directive.value + "?" + code() + ": null"
                    }, token.code)

                    tokenWithIf.code = genCode(function (codeWithIf, code) {
                        var codeIf = codeWithIf(),
                            index = codeIf.lastIndexOf("null")

                        return codeIf.substring(0, index) + code() + codeIf.substring(index + 4)
                    }, tokenWithIf.code, token.code)

                    token.code = Undefined
                }

                function processElse(token) {
                    var directive = token.directives["else"]

                    if (!directive) return

                    markLocation(directive.loc)

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
                        instance._logWarning("transition 的内容必须有 key"/*,childsWithoutKey.map(function (child) { return child.open_loc || child.loc }) */)

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
                            throwError('事件指令必须配置参数和修饰符至少一项')

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
                            throwError('事件指令必须配置参数和修饰符至少一项')

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
                         * 非 IE 浏览器下检查箭头函数语法
                         */
                        if (!isIE && !isFunction(eval(handler))) {
                            throwError("不是有效的箭头函数：" + handler)
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
                        throwError("if/else-if/else 指令，不能存在于同一个标签")
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
                            throwError("使用 else-if/else 指令时，前一兄弟元素必须有 if/else-if 指令")
                        }

                        if (directives.hasOwnProperty("else")) {
                            throwError("使用 else-if/else 指令前，不能使用 else 指令")
                        }

                        if (directives.hasOwnProperty("if")) {
                            return prevToken
                        }

                        prevToken = prevToken.prev
                    }

                    throwError("使用 else-if/else 指令前，必须先使用 if 指令")
                }

                function throwError() {
                    throw instance._logError.apply(instance, arguments)
                }
            },
            _createRenderHelper: function () {
                var instance = this

                bindContext = normailzeSurrogate(bindContext)

                return {// 执行代码字符串时使用到的方法
                    "$model": {
                        input: function (e, path) {
                            if (!path) return

                            var value = e.target.value

                            setModelData(path, value)
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

                            setModelData(path, value)
                        },
                        radio: function (e, path) {
                            if (!path) return

                            var value = e.target._value

                            value = (value === "on" || isUndef(value)) ? null : value

                            setModelData(path, value)
                        },
                        select: function (e, path) {
                            if (!path) return

                            var select = e.target,
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

                            setModelData(path, value)

                            function findOptionValue(option) {
                                return "_value" in option ? option._value : option.innerText
                            }
                        },
                        component: function (path, value) {
                            if (!path) return

                            setModelData(path, value)
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
                            var isMultiple = isDef(vdom.getAttribute("multiple"))

                            if (isMultiple && !isArray(value)) {
                                vdom.setElementProperty("value", Undefined)
                                instance._logWarning("select 多选时应使用数组绑定")

                                return vdom
                            }

                            var found = isMultiple,
                                options = []

                            VirtualDOM.eachRealChild(vdom.children, function (child) {
                                options.push(child)
                            })

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

                        if (!component) return instance._logError("未找到组件【" + tagName + "】")

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

                            try {
                                if (updateId !== _currentInstance.updateId) return

                                if (_currentInstance.state.patching) return

                                _currentInstance._doneAsyncComponent(vdom)
                            } finally {
                                /**清除闭包内没用的数据 */
                                _currentInstance = updateId = componentData = vdom = null
                            }
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
                         * 当组件创建/更新时,插槽需要创建/更新的情况:
                         * !slotCache 没插槽缓存,可能未创建插槽或缓存被清除
                         * !hasComponentChildren 代表插槽将使用 children 渲染,children 属于组件,需随组件更新
                         * useSlotProps 代表componentChildren依赖了组件数据,需随组件更新
                         */
                        if (
                            !slotCache ||
                            !hasComponentChildren ||
                            useSlotProps
                        ) {
                            if (hasComponentChildren) {
                                slotVdoms = []

                                try {
                                    var child = null

                                    for (var i = 0, len = componentSlotChildren.length; i < len; i++) {
                                        child = componentSlotChildren[i]

                                        var slotScope = child.slotScope,
                                            childVdoms = null,
                                            childVdoms = slotScope
                                                ? child.render.apply(null, slotScope.map(function (key) { return slotProps[key] }))
                                                : child.render()

                                        if (childVdoms) slotVdoms.push(childVdoms)
                                    }
                                } catch (e) {
                                    instance._logError([
                                        "渲染插槽时出错",
                                        ["错误信息：", e],
                                        ["错误位置 - 第" + (i + 1) + "个组件子元素", getRawFn(child.render)]
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
                                instance._logWarning("transition 的内容必须有 key")
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
                         * 对 html 文本中的特殊字符转义为实体
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
                            throw instance._logError(["for 指令仅支持数组、对象、字符串、整数", ["接收到：", source]])
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
                * 为函数绑定当前作用域数据。
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

                function setModelData(path, value) {
                    var context = instance.context || instance.dataContext

                    if (instance._existInContext(path, "data")) {
                        instance._updateDataContext(path, value)
                    }
                    // else if (instance._existInContext(path, "props")) {
                    //     context.$emit(componentModelEvent(path), value)
                    // }
                    else if (hasKeyPath(instance.baseContext, path)) {
                        path = path.replace(/^\$store\./, "")
                        context.$store.commit(path, value)
                    }
                    else {
                        instance._logError("model 指令只能使用 data 或 $store 的状态，接收到【" + path + "】")
                    }
                }
            },
            _existInContext: function (keyPath, type) {
                if (!isPlainObject(this._contextKeyMap)) return false

                var keyMap = this._contextKeyMap,
                    name = keyPath,
                    existType

                if (type === "data" || type === "props") {
                    existType = 0
                        || keyMap[name]
                        || keyMap[name = pathResolve(name)[0]]
                        || keyMap[name = pathResolve(this._toAbsolutePath(name))[0]]
                }
                else {
                    existType = keyMap[name]
                }

                return existType === type
            },
            _checkUserDefineName: function (name, type) {
                var keyMap = this._contextKeyMap || (this._contextKeyMap = {}),
                    existType = keyMap[name],
                    validate = true

                if (name[0] === "$") {
                    validate = false
                    this._logError(wrap(type) + '选项的属性，不能使用"$"作为前缀：' + wrap(name))
                }

                if (!/^[\w$]+$/.test(name)) {
                    validate = false
                    throw this._logError(wrap(type) + '选项的属性，包含不合法的字符：' + wrap(name))
                }

                if (existType) {
                    validate = false
                    this._logError('已在' + wrap(existType) + '选项中存在相同的命名：' + wrap(name))
                }

                if (validate) {
                    keyMap[name] = type
                }

                function wrap(str) {
                    return '[' + str + ']'
                }

                return validate
            },
            _setData: function (keyPath, value, force) {
                var wrongPaths = []

                if (isString(keyPath)) {
                    if (this._existInContext(keyPath, "data")) {
                        this._updateDataContext(keyPath, value, force)
                    }
                    else {
                        wrongPaths.push(keyPath)
                    }
                }
                else if (isPlainObject(keyPath)) {
                    var dataPatch = keyPath,
                        data = {},
                        shouldUpdate = false

                    for (var keyPath$ in dataPatch) {
                        if (this._existInContext(keyPath$, "data")) {
                            data[keyPath$] = dataPatch[keyPath$]
                            shouldUpdate = true
                        }
                        else {
                            wrongPaths.push(keyPath$)
                        }
                    }

                    if (shouldUpdate) {
                        this._updateDataContext(data, force)
                    }
                }

                if (wrongPaths.length) {
                    this._logError("$setData 只能修改 data 或由 data 派生的数据：" + wrongPaths)
                }
            },
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

                var hookEventNm = userHookEvent(hook)

                if (isUserHookEvent(hookEventNm)) {
                    this._emit.apply(this, [hookEventNm].concat(args || slice(arguments, 1)))
                }
            },
            _emit: function (eventType) {
                var args = slice(arguments, 1),
                    invoker = this.componentEvents && this.componentEvents[eventType],
                    emitsValidator = this.emitsConfig && this.emitsConfig[eventType]

                if (!invoker) return

                if (isFunction(emitsValidator) && !emitsValidator.apply(null, args)) {
                    this._logWarning(["事件【" + eventType + "】，参数校验失败", ["参数：", args]])
                    return
                }

                invoker.apply(null, args)
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
                    if (!this.el) throw this._logError("未添加挂载节点，退出更新")

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

                this._setDirty(false)

                if (!state.shouldTemplateReRender) return

                state.shouldTemplateReRender = false

                delete this.vdomRefList

                var restoreCurrentInstance = setCurentInstance(this),
                    context = this.context = this._createContext(),
                    oldVdom = this.vdom,
                    newVdom = this.renderVdom(context)

                this._syncComponentMeta(newVdom)

                if (state.shouldTemplateReRender) {
                    this._logWarning("在渲染模板期间，再次触发了模板更新！")
                }

                this.context = null
                this.vdom = newVdom

                this._emitHook("beforePatch", oldVdom, newVdom)

                this._patch(oldVdom, newVdom)

                restoreCurrentInstance()

                this._doneUpdate()
            },
            _patch: function (oldVdom, newVdom) {
                if (oldVdom) this.refNode = null // 挂载后参考节点以 oldVdom 为准

                this.state.patching = true
                VirtualDOM.patch(this.el, oldVdom, newVdom, this.refNode)
                this.state.patching = false
            },
            _rootElements: function () {
                var $elements = this.baseContext.$elements,
                    elements = []

                VirtualDOM.eachElement(this.vdom, function (element) {
                    elements.push(element)
                })

                $elements.length = 0
                push($elements, elements)

                return elements
            },
            _doneUpdate: function () {
                clearKeys(this.baseContext.$refs)
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
                var $refs = this.baseContext.$refs,
                    vdomRefList = this.vdomRefList

                if (!vdomRefList || !vdomRefList.length) return delete this.vdomRefList

                var notFoundList = null

                for (var i = 0, len = vdomRefList.length; i < len; i++) {
                    var vdom = vdomRefList[i],
                        ref = getRef(vdom)

                    if (isUndef(ref)) {
                        ref === Undefined && (notFoundList || (notFoundList = [])).push(vdom)
                        continue
                    }

                    var isArrayRef = vdom.isArrayRef,
                        refName = vdom.refName,
                        collectedRef = $refs[refName]

                    if (collectedRef) {
                        isArrayRef && isArray(collectedRef) ? collectedRef.push(ref) : this._logWarning("重复的 ref【" + refName + "】")
                    }
                    else {
                        $refs[refName] = isArrayRef ? [ref] : ref
                    }
                }

                this.vdomRefList = notFoundList

                function getRef(vdom) {
                    if (vdom.isComponent) {
                        var i
                        return isDef(i = vdom.component) && isDef(i = i.instance) && i.dataContext || Undefined
                    }
                    else if (vdom.isFragment) {
                        return null
                    }
                    else {
                        return vdom.element || Undefined
                    }
                }
            },
            _logError: function (messages, loc) {
                var head = this._genConsoleHead(),
                    loc$ = loc || LOC

                if (loc$) {
                    messages = [].concat(messages, "错误位置：\n" + markTemplate(this.template, loc$))
                }

                genConsole().head(head).stdout(console.error).printLines(messages)
            },
            _logWarning: function (messages, loc) {
                var head = this._genConsoleHead(),
                    loc$ = loc || LOC

                if (loc$) {
                    messages = [].concat(messages, "错误位置：\n" + markTemplate(this.template, loc$))
                }

                genConsole().head(head).stdout(console.warn).printLines(messages)
            },
            _genConsoleHead: function () {
                var id = this.state.isRoot ? "" : "(" + this.id + ")",
                    names = [this.name],
                    parentContext = this.baseContext.$parent

                while (parentContext) {
                    names.push(parentContext.__instance__.name)
                    parentContext = parentContext.$parent
                }

                var head = names.reverse().join("->") + id + ":"

                return head
            }
        }

        /**
         * 用于实现跨组件实例的响应式更新
         */
        var createDepTarget = normailzeSurrogate(function (fn, onDepUpdate) {
            var uniq = {},
                onupdate$ = isFunction(onDepUpdate) ? onDepUpdate : depTarget,
                callback = null

            function depTarget() {
                var oDepTarget = DepTarget

                DepTarget = depTarget
                var value = fn.apply(this, arguments)
                DepTarget = oDepTarget

                if (isFunction(callback)) {
                    callback(value)
                }

                return value
            }

            depTarget.collect = function (observer, deps) {
                var id = "" + observer.id + deps

                if (uniq[id]) return

                uniq[id] = true

                var onupdate = observer.observe(deps),
                    release = onupdate.deep(onupdate$)

                depTarget.release.add(release)
            }

            depTarget.release = createInvoker()

            depTarget.callback = function (fn) {
                if (isFunction(fn)) {
                    callback = fn
                }
            }

            return depTarget
        })

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
                 * 当没有 移除/插入 元素时，out-in/in-out 会在 patch 后立即执行 in/out
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

            var lastModeHandler = lastTransition.modeHandler // 上一次过渡仍有 modeHandler 代表 listener 未执行。

            if (lastModeHandler && mode === "out-in") return lastModeHandler // 复用 modeHandler，新的 out-in 过渡的待进入元素，由其控制。

            if (lastModeHandler && mode === "in-out") lastModeHandler.end() // 立即移除上一次 in-out 过渡的待移除元素，以免待移除元素堆积。

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
                patchCallbacks.push(function transitionEnterNow() { // 在元素插入后执行
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
                    savePosition("_oldPos_", element)
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
             * 先移除不保留的元素，使后面的 patch 不会把保留的元素插入到不保留的元素后面，影响动画执行
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
                moveElements.forEach(endLastTransition) // 先结束正在执行的过渡/动画，保证后面获取的位置正确
                allChildren.forEach(fixModePlace)

                moveElements.forEach(saveNewPos) // getBoundingClientRect 会触发浏览器回流，所以与设置 transform 样式的 stayAtOldPos 分开处理
                moveElements.forEach(stayAtOldPos)

                document.body.offsetHeight // 强制浏览器触发回流，使前面的样式变更生效

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
                savePosition("_newPos_", element)
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

        function savePosition(key, element) {
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
         * 处理样式属性，兼容性，样式前缀等...todo
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
         * 使构建的代理函数记录下原始函数，避免重复代理
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

                count += lineLen + 1// 算上被分割的换行符 \n

                var lineStart = count - lineLen - 1,
                    lineEnd = count

                /**
                 * 处理包含标记内容的行
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
                elemAttrValue = // 在mustache、圆括号内可直接使用与属性值引号相同的引号
                    '([`"\'])' + // 起始属性值引号
                    // 属性值内容包含这些情况：一般字符 | 与属性值引号不同的引号 | 带转义符的属性值引号
                    '((?:[^`"\'\\\\]|(?!\\3)[`"\']|\\\\\\3?)*)' +
                    '\\3', // 结束属性值引号
                Reg$ElemAttr = new RegExp("^([\\w-@#:.$|]+)(\\s*=\\s*" + elemAttrValue + ")?\\s*"),// $1:属性名、$2:属性值（含等号）?、$3:引号、$4:引号内容
                Reg$TextContent = new RegExp("^[^<]+"),
                Reg$SingleElem = /^(?:img|input|br|hr|param|meta|link)$/,
                start = 0, end = 0,
                intactTemplate

            function doParse(template, context) {
                if (!template) {
                    if (context.type !== "root") {
                        throw parse_warn('标签未闭合', context.open_loc)
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
                            attrValue = attrNameOnly ? "" : matcher[4].trim()

                        attrs.push({
                            name: attrName,
                            value: attrValue,
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
                        throw parse_warn('标签未结束', open_loc.start, end)
                    }
                }
                else if (matcher = template.match(Reg$ElemClose)) {
                    template = cutMatch(template, matcher)

                    var tagName = matcher[1]

                    if (tagName != context.tagName) throw parse_warn('结束标签错误', LOC)

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
                    throw parse_warn('未识别内容', start, start + 1)
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
                throw logError("Store 实例化失败，缺少参数 options 对象")
            }

            var state = options.state,
                getters = options.getters,
                actions = options.actions

            if (!isPlainObject(state)) {
                throw logError("Store 实例化失败，参数 options 中未定义 state 状态对象", options)
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
                        : logError("修改状态【" + key + "】失败，state 中定义的状态只能通过调用 commit 方法修改")
                    return true
                },
                deleteProperty: function (target, key) {
                    logError("修改状态【" + key + "】失败，state 中定义的状态不能删除")
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
                        logWarning("Store 中的【" + keyPath + "】是 getter，不能 commit")
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
                            conflicts.push("【" + name + "】")
                        }
                    }
                }

                if (conflicts.length) {
                    throw logError("Store 实例化失败，在 getters 和 state 中存在重复命名的状态：" + conflicts.join(" "))
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
                return hasKeyPath(this.state, keyPath) || (logWarning("Store 中不存在状态【" + keyPath + "】"), false)
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
            if (isUndef(type)) throw logError("VirtualDOM：实例化失败，缺少参数 type")
            if (isUndef(options)) throw logError("VirtualDOM：实例化失败，缺少参数 options")

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
                    this.element = null // fragment 的 element 引用父 vdom 的 element，可以看作是父 vdom 的替身
                    break
                default:
                    throw logError("VirtualDOM：实例化失败，未能识别的类型【" + type + "】")
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
                logError("VirtualDOM：提供的组件实现类，未实现【" + name + "】方法", Component)
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
                if (!isFunction(_Component)) return logWarning("组件实现类必须是函数")

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
                    logError("VirtualDOM：为元素设置属性【" + key + "】失败", val, element)
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

        var entityMap = { 'amp': '&', 'gt': '>', 'lt': '<', 'quot': '"', 'apos': "'", 'ldquo': '“', 'rdquo': '”' }

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
                    logError("VirtualDOM：创建 DOM 元素失败", vdom)
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
                /** 使移除元素的行为可由 remove hook 控制，最后一次调用 rm 才会真正移除元素 */
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
                        logWarning("VirtualDOM：检测到存在重复的 key【" + vdom.key + "】")
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

                if (newStartIdx <= newEndIdx) {// 旧节点全部比较完毕，添加未比较的新节点
                    var _ref = isDef(newChildren[newEndIdx + 1])
                        ? newChildren[newEndIdx + 1]
                        : ref

                    addChildren(parentNode, newChildren, newStartIdx, newEndIdx, _ref)
                }
                else if (oldStartIdx <= oldEndIdx) {// 删除剩余的旧节点
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

            if (newVdom.isText) {// 文本节点
                if (oldVdom.text !== newVdom.text) {
                    setTextContent(element, newVdom.text)
                }
                return true
            }

            if (newVdom.isComment) {// 注释节点
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
            _createInstance: function (config, componentData) {
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

                if (isFunction(error)) { /* error 组件 */
                    errorComp = VirtualDOM.createComponent("error", error, {
                        name: "error",
                        parentContext: this.componentData.parentContext,
                        vdom: this.componentData.vdom,
                        domEventManager: this.componentData.domEventManager,
                        complete: this.componentData.complete
                    })
                }
                else { /* DOM 元素 */
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

                function createLoading$() {
                    if (!_self.asyncLoading) return

                    var loadingComp = null

                    if (isFunction(loading)) { /* loading 组件 */
                        loadingComp = VirtualDOM.createComponent("loading", loading, {
                            name: "loading",
                            parentContext: _self.componentData.parentContext,
                            vdom: _self.componentData.vdom,
                            domEventManager: _self.componentData.domEventManager
                        })
                    }
                    else { /* DOM 元素 */
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

                delay ? setTimeout(createLoading$, delay) : createLoading$()
            },
            _callError: function (errMessage) {
                this.instance = null

                errMessage = "Component:【" + this.name + "】" + errMessage

                isFunction(this._errCallback) && this._errCallback(errMessage)

                logError.apply(null, [errMessage].concat(slice(arguments, 1)))
            },
            create: function (componentData) {
                if (this.state !== "init") return

                if (isUndef(componentData)) {
                    return this._callError("缺少组件上下文")
                }

                if (!isObject(componentData)) {
                    return this._callError("无效的组件上下文", componentData)
                }

                this.componentData = componentData
                this._errCallback = function () { this.componentData.complete() }

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
                                _self._callError("加载异步组件超时")
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
                            _self._callError("加载异步组件失败", err)
                            resolve()
                        })
                    })
                }
                else {
                    if (!initComponent) {
                        return this._callError("组件不存在")
                    }

                    if (!isFunction(initComponent)) {
                        return this._callError("组件必须使用函数定义")
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
                        instance = this.instance = this._createInstance(config, componentData)

                        if (!render) {
                            RenderCache[id] = instance.render
                        }
                    } catch (err) {
                        this._callError("创建组件失败", err)
                    }
                }
            },
            mount: function (parentNode, refNode) {
                if (this.state !== "init") return

                if (this.asyncLoading) { // 异步组件加载中
                    if (this.placeholder) return

                    var _self = this,
                        placeholder = this._createPlaceholder(parentNode, refNode)

                    this._createLoading(parentNode, placeholder)

                    this.asyncLoading
                        .then(this.mount.bind(this, parentNode, placeholder)) // 异步组件加载完毕后继续处理
                        .then(function () {
                            if (_self.loadingComp) {
                                _self.loadingComp.remove()
                                _self.loadingComp = null
                            }
                        })
                }
                else if (this.instance) { // 组件实例构建成功
                    this.state = "success"
                    this.instance.mount(parentNode, refNode)

                    if (this.placeholder) {
                        this.placeholder.remove()
                        this.placeholder = null
                    }
                }
                else { // 组件实例构建失败
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
                    this._callError("componentData 必须是对象")
                }

                if (this.asyncLoading) {
                    this.asyncLoading.then(this.update.bind(this, componentData))
                }
                else if (this.instance) {
                    this.componentData = componentData
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
                     * 没有 doScroll 或 iframe 内不能使用 doScroll 时
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
            if (!isString(name)) throw logError("importComponent：缺少参数 name")
            if (!isString(url)) throw logError("importComponent：缺少参数 url")

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
                     * 异步组件加载回来后，往导入结果对象注入组件，使得父组件可以使用该组件。
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
                         * 当 IE 浏览器同时请求多个 script 时，前面的 script 的 onreadystatechange/onload 事件可能会在后面的 script 执行后才被触发。
                         * 解决办法是将在一个 marcotask 中同时发起的多个 script 请求，变成在多个 marcotask 中分别发起。
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

                        if (!success) logError("importComponent：导入组件库【" + url + "】失败")

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
                return logError("registerComponent：注册全局组件失败，组件【" + name + "】需使用函数定义")
            }

            var componentSpace = componentSpaces["global"] || (componentSpaces["global"] = Component.public)

            handleComponent(name, component, options, componentSpace)
        }

        var exportCallbacks = null

        function exportComponent(name, component, options) {
            if (!isFunction(component)) {
                return logError("exportComponent：导出组件失败，组件【" + name + "】需使用函数定义")
            }

            if (!isDocReady) {
                /**
                 * 兼容 js 同步加载。使得用 exportComponent 导出的组件，既可异步加载，也可在 html 中使用 script 标签同步加载。
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

        var $ob_id = 0,
            CIRCULAR_THRESHOLD = isIE ? Infinity : 100,
            Reg$TestNested = /[.\[]/

        function Observer() {
            this.id = ++$ob_id
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
                        dep_id = dependent.dep_id,
                        obs = observer.obs || (observer.obs = {})

                    keys.forEach(function (key) {
                        var dependents = obs[key] || (obs[key] = [])

                        if (dependents[dep_id]) return

                        dependents[dep_id] = true
                        dependents.push(dependent)
                    })

                    return function release() {
                        releaseDependent(obs, keys, dependent)
                    }
                }

                function onupdate_deep(fn) {
                    if (!isFunction(fn)) return

                    var dependent = createDependent(fn),
                        dep_id = dependent.dep_id,
                        deepObs = observer.deepObs || (observer.deepObs = {}),
                        release = onupdate(dependent)

                    deepKeys.forEach(function (key) {
                        var dependents = deepObs[key] || (deepObs[key] = [])

                        if (dependents[dep_id]) return

                        dependents[dep_id] = true
                        dependents.push(dependent)
                    })

                    /**
                     * 当深度监听时，使用键路径第一个 key 作为标志，当 update 时，若没有标志，不用查找深度监听的依赖
                     * 例如：
                     * 深度监听 “a.b” 时，“a” 作为标志被记录；
                     * 当 update “a.b.c.d” 时，发现 “a” 标志存在，继续查找深度监听的依赖；
                     * 当 update “x.y.z” 时，发现 “x” 标志不存在，不再查找深度监听的依赖。
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

                    var pathKeys = pathResolve(keyPath)

                    if (!deepMarks || !deepMarks[pathKeys[0]]) {
                        continue
                    }

                    var maxIndex = pathKeys.length - 1,
                        pathKeys$ = []

                    for (var j = 0; j < maxIndex; j++) {
                        pathKeys$.push(pathKeys[j])

                        var deepKey = genObserveKey(pathKeys$)

                        addTaskForKeyPath(keyPath, deepObs[deepKey])
                    }
                }

                /**
                 * 收集同步执行期间的更新记录，用于检查是否存在循环更新。
                 */
                var updateRecord = this.updateRecord || (this.updateRecord = [])
                updateRecord.push(keyPaths.join())

                if (!this.queue) {
                    var circular = null

                    this.queue = queue

                    for (var m = 0; m < queue.length; m++) {
                        var task = queue[m]

                        if (updateRecord.length > CIRCULAR_THRESHOLD && (circular = checkCircular(updateRecord))) {
                            logError("Observer：检测到更新陷入死循环，循环路径【" + circular.path.join("->") + "】,循环次数【" + circular.times + "】")

                            break
                        }

                        isFunction(task) && task()
                    }

                    this.queue = this.once = null

                    /**
                     * 在同步执行结束后清空更新记录。
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

            if (isDef(fn.dependent)) {
                fn.dependent.__released = false
                return fn.dependent
            }

            dependent.__released = false
            dependent.dep_id = "dep-" + ++$ob_id

            function dependent(causes) {
                if (dependent.__released) return

                try {
                    fn(causes)
                } catch (err) {
                    console.error(err)
                }
            }

            return fn.dependent = dependent
        }

        function releaseDependent(obs, keys, dependent) {
            dependent.__released = true

            keys.forEach(function (key) {
                var dependents = obs[key]

                delete dependents[dependents.dep_id]
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

            if (len - startIndex < 30) return // 限制检查频率，新增更新记录超过 30 个才检查

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
                     * IE8 输入框监听 onpropertychange 事件，在第一次输入时不会触发
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
                 * 模拟捕获阶段：
                 * 由于模拟时处于冒泡或目标阶段，冒泡过程中可能会触发多个监听器，在第一个监听器被调用时执行捕获阶段，
                 * 后面的监听器被调用时会被 runCapturePhase 拦截，不会重复执行捕获阶段。
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
            if (!isString(keyPath)) throw logTypeError("解析键路径失败：无效的参数 keyPath", "String", toType(keyPath))

            keyPath = keyPath.trim()

            if (!keyPath) throw logError("解析键路径失败：参数 keyPath 不能为空")

            if (isArray(pathResolvedCache[keyPath])) return pathResolvedCache[keyPath]

            var matcher,
                pathKeys = [],
                remainPath = keyPath

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
                    throw logError("解析键路径失败：【" + keyPath + "】不是有效的键路径")
                }
            }

            return pathResolvedCache[keyPath] = pathKeys

            function cutMatch() {
                var startIndex = matcher.index,
                    endIndex = startIndex + matcher[0].length

                remainPath = remainPath.substring(endIndex)
            }
        }

        function readData(data, keyPath) {
            if (!isObject(data)) throw logTypeError("读取数据失败：无效的参数 data", "Object", toType(data))

            if (isUndef(keyPath) || !isString(keyPath)) throw logTypeError("读取数据失败：无效的参数 keyPath", "String", toType(keyPath))

            if (!keyPath) throw logError("读取数据失败：参数 keyPath 不能为空")

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
            if (!isObject(data)) throw logTypeError("检查 keyPath 失败：无效的参数 data", "Object", toType(data))

            if (isUndef(keyPath) || !isString(keyPath)) throw logTypeError("检查 keyPath 失败：无效的参数 keyPath", "String", toType(keyPath))

            if (!keyPath) throw logError("检查 keyPath 失败：参数 keyPath 不能为空")

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
            if (!isObject(data)) throw logTypeError("写入数据失败：无效的参数 data", "Object", toType(data))

            if (isUndef(keyPath) || !isString(keyPath)) throw logTypeError("写入数据失败：无效的参数 keyPath", "String", toType(keyPath))

            if (!keyPath) throw logError("写入数据失败：参数 keyPath 不能为空")

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
            if (!isObject(data)) throw logTypeError("替换数据失败：无效的参数 data", "Object", toType(data))

            if (isUndef(keyPath) || !isString(keyPath)) throw logTypeError("替换数据失败：无效的参数 keyPath", "String", toType(keyPath))

            if (!keyPath) throw logError("替换数据失败：参数 keyPath 不能为空")

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
             * 把函数中非赋值并以 head 开头的键路径视作依赖并收集
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
             * 查找函数中被赋值了 this 的键路径（变量或对象属性）
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

                if (!url) throw new Error('ajax请求缺少url参数');

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
                //         .print("请求失败")
                //         .print("请求url", options.url)
                //         .print("状态码", xhr.status)
                //         .print("响应", xhr.responseText)
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
                            _content = $.trim(content).replace(/(")((?:[^"]|"(?!\s*[}\]]|\s*[:,]\s*(?:["\[{]|\d+\b)))*)(")/g, function (match, $1, quotString, $3) {

                                return $1 + quotString.replace(/[\r\n\t]/g, function (match) {/*修复双引号内的换行符制表符*/
                                    return replaceMap[match] || match
                                }).replace(/[\\]?"/g, '\\"')/*修复双引号内的无转义的双引号*/ + $3

                            }).replace(/[\r\n\t]/g, "")/*去除多余的换行符制表符*/.replace(/,\s*([}\]])/g, "$1")/*去除末尾逗号*/

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
            sendJsonpWithScript: function () {// 当连续发送多个jsonp且响应的回调函数名称相同时，或回调函数传入的参数多于1个时，不能用jquery的jsonp请求方式
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
         * 获取指定URL参数
         * @param {string} name
         * @param {Object} options
         */
        function getURLParam(name, options) {
            if (isUndef(paramObjDecoded)) {
                paramObjDecoded = {}

                var paramString = location.search.substring(1);

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
                throw logTypeError("getURLParam：无效的参数 options", "Object", toType(options))
            }

            options = Object.assign({
                required: false,
                optional: Undefined,
                onerror: Undefined
            }, options)

            var optional = options.optional

            if (isDef(optional) && !isArray(optional)) {
                throw logTypeError("getURLParam：无效的选项 optional", "Array", toType(optional))
            }
            else if (
                isArray(optional) &&
                optional.some(function (a) { return !isString(a) || !a })
            ) {
                throw logError("getURLParam：选项 optional 数组只能包含非空字符串")
            }

            if (options.required && !value) {
                handleError("required", "getURLParam：缺少必要的 URL 参数【" + name + "】")
            }

            if (value && isArray(optional) && !~optional.indexOf(value)) {
                handleError("optional", "getURLParam：URL 参数【" + name + "】的值【" + value + "】不在指定的 optional 选项范围内")
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

        // 设置COOKIE
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

        // 获取指定COOKIE
        function getCookie(name) {
            var reg = new RegExp(name + "=([^;]*)"),
                cookie = document.cookie.match(reg)

            return cookie && decodeURIComponent(cookie[1]);
        }

        // 获取多个COOKIE
        function getCookies(names) {
            return names.reduce(function (obj, key) {
                return obj[key] = getCookie(key), obj;
            }, {})
        }

        // 删除指定COOKIE
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

        // 深度复制对象
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

        // 深度比较
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
         * 组合
         * combine(["a","b"],[1,2,3]) => [ ["a",1],["a",2],["a",3],["b",1],["b",2],["b",3] ]
         */
        function combine() {
            if (arguments.length < 2) throw logError("combine：至少需要两个数组作为参数")

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

        // 继承
        function inherit(ChildClass, ParentClass) {
            function ChildProtoClass() { this.$_proto_ = ChildProtoClass.prototype }
            ChildProtoClass.prototype = ParentClass.prototype

            var childProto = new ChildProtoClass()

            function ChildClass$() {
                ChildClass.apply(this, arguments)

                this.$_proto_ = ChildClass$.prototype

                noop.prototype = this// 用于在chrome调试中显示对象类型时使用正确的名称，而不是显示为 “ChildClass$”
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

        // 分页器
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
                            throw Error("分页更新函数只接收一个参数时，需返回 Promise，且该 Promise 需返回一个 hasNext，若不使用 Promise，分页更新函数须接收至少两个参数，分别为 {Number}nextPage, {Function}done, {Function}fail")
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
         * 滚动分页器
         * @param {Element} scrollRef 滚动容器
         * @param {Element} contentRef 内容容器[可选,若内容容器占满滚动容器(即没有其它内容)则不用输入]
         * @param {Number} page 起始页
         * @param {Function} pageUpdater 数据更新函数
         * 
         * <div 滚动容器>  
         *    <div 其它内容></div>  
         *    <ul 内容容器>  
         *      <li 滚动加载的内容></li>  
         *    </ul>  
         *    <div 其它内容></div>  
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

            return {// 控制器,当多个分页器共用同一个滚动容器时,用于控制哪个分页器激活
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
         * 函数去抖，限制事件触发间隔不少于{wait}毫秒
         * @param {Function} fn 回调函数
         * @param {Number} wait 间隔时间（毫秒）
         * @param {Boolean|Function} immediate 是否立即执行
         * 
         * * debounce(fn,1000) 触发事件后,在1秒内不再触发事件则执行回调函数 fn 并复位计时器。
         * * debounce(fn,1000,true) 触发事件后立即执行回调函数 fn，在1秒内不再触发事件则复位计时器。
         * * debounce(fn,1000,()=>alert("请不要频繁点击")) 触发事件后立即执行回调函数 fn，在1秒内不再触发事件则复位计时器,若在1秒内再次触发会调用{immediate}函数
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
         * 函数节流。控制回调函数调用间隔不少于{interval}毫秒。
         * @param {Function} fn 回调函数
         * @param {Number} interval 间隔时间（毫秒）
         * 
         * * throttle(fn,1000)持续触发事件期间，回调函数fn调用间隔不少于1000毫秒
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
         * 函数柯里化-多次传参
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
         * base64转blob
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
         * ### 普通数组排序
         * @param {array} list 数组
         * @param {Function} [fn] 可选，排序比较函数
         * 
         * * sort(list)
         * * sort(list, function(a,b){return a-b})
         * 
         * ### 对象数组排序 (按若干个key排序)
         * @param {array} list 对象数组
         * @param {string} key... 对象的排序参数，由比较方式、键和排序方向组成。
         * * 比较方式： + 按数字比较，# 按字符比较。  
         *   键：指定对象中用于排序的键名称。  
         *   排序方向： > 从大到小降序排列，< 从小到大升序排列。
         * @param {string} [globalOrder] 可选，全局排序方向。当排序参数没指定排序方向时，使用全局排序方向，没有全局排序方向时，按升序排列。
         * 
         * * sort(list,"key1","key2") => key1升序 key2升序
         * * sort(list,"key1","key2",">") => key1降序 key2降序
         * * sort(list,"key1","key2<","key3",">") => key1降序 key2升序 key3降序
         * * sort(list,"+key1>","#key2>","+key3") => key1降序,数字比较 key2降序,字符比较 key3升序,数字比较
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

            if (!~keyMaxIndex) return logError("未传入key,无法比较对象"), list

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
         * 计算合适的字体大小
         * @param {string} text 显示的文本
         * @param {number} width 盒子的宽度
         * @param {number} height 盒子的高度
         * @param {number} lineHeight 盒子的line-height
         * @param {number} fontSize 当前的字体大小
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
         * 超长文本省略
         * @param {string} text 显示的文本
         * @param {number} width 盒子的宽度
         * @param {number} fontSize 当前的字体大小
         * @param {number} maxLine 最大显示行数
         * @param {string} tagName 换行元素标签名
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
         * 数字转中文大写
         * @param {number} number 数字
         * 
         * * toChineseNumber(10010.01) => 壹万零壹拾圆零壹分
         */
        function toChineseNumber(number) {
            if (isNaN(number)) throw Error('请输入正确的数字')

            var numberArea = (number + "").split('.'),
                integer = numberArea[0],
                decimal = numberArea[1],
                numberCharts = ['零', '壹', '贰', '叁', '肆', '伍', '陆', '柒', '捌', '玖'],
                intUnitForPart = ['万亿', '亿', '万', ''],
                intUnitForChar = ['仟', '佰', '拾', ''],
                RMB_Unit = decimal > 0 ? '圆' : '圆整',
                decimalUnitForChar = ['角', '分'],
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
                        minNumber = 0// 非末尾0有效,101=>壹佰零壹

                        if (n == '0') {
                            minNumber = 1// 连续多个0,只需输出一个零,1001=>壹仟零壹
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
            _offset: function (elem) {// elem(border外)到html(content)的距离 [css的zoom会影响计算结果 结果会随滚动变化]
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
            offset: function (elem) {// elem边框外到html边缘的距离
                var left = 0, top = 0;

                while (elem) {
                    left += elem.offsetLeft
                    top += elem.offsetTop
                    elem = elem.offsetParent
                }

                return { left: left, top: top };
            },
            offsetParent: function (elem) {// 找到最近的定位元素
                var html = document.documentElement,
                    parent = elem.offsetParent

                while (parent && parent !== html && (!parent.style.position || parent.style.position === "static")) {
                    parent = parent.offsetParent
                }

                return parent || html
            },
            position: function (elem) {// elem(margin外)到最近定位元素(content)的距离
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
            distance: function (elemA, elemB) {// elemA(border外)到elemB(border)的距离
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
                /* 系统 */
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
                /* 浏览器 */
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
                /* 浏览器外壳 */
                var env = {
                    shell: "",
                    shellVersion: ""
                }

                if (testUA(/micromessenger/)) {
                    env.shell = "wechat"
                    env.shellVersion = getVersion(/micromessenger\/([\d._]+)/)
                }
                else if (testUA(/qqbrowser/)) {
                    env.shell = "qq" // qq浏览器
                    env.shellVersion = getVersion(/qqbrowser\/([\d._]+)/)
                }
                else if (testUA(/ucbrowser/)) {
                    env.shell = "uc" // uc浏览器
                    env.shellVersion = getVersion(/ucbrowser\/([\d._]+)/)
                }
                else if (testUA(/qihu 360se/)) {
                    env.shell = "360" // 360浏览器
                }
                else if (testUA(/2345explorer/)) {
                    env.shell = "2345" // 2345浏览器
                    env.shellVersion = getVersion(/2345explorer\/([\d._]+)/)
                }
                else if (testUA(/metasr/)) {
                    env.shell = "sougou" // 搜狗浏览器
                }
                else if (testUA(/lbbrowser/)) {
                    env.shell = "liebao" // 猎豹浏览器
                }
                else if (testUA(/maxthon/)) {
                    env.shell = "maxthon" // 遨游浏览器
                    env.shellVersion = getVersion(/maxthon\/([\d._]+)/)
                }

                return env
            }(),
            env = Object.assign(
                {
                    dev: false // 是否测试环境
                },
                env$system,
                env$browser,
                env$shell
            )

        if (env.dev) {
            /** 检查生产环境标识文件，该标识文件只存在于生产环境，并会同步修正 dev 为 false。该机制用于防止在更新本 js 时，因漏改 dev 为 false 而出现的问题。 */
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
                 * 浏览器可能不支持 1 << 28 长的字符串
                 */
                if (str.length * count >= 1 << 28) {
                    throw new RangeError('repeat count must not overflow maximum string size')
                }

                var result = ''

                /**
                 * 位运算，二进制中每位为右边的两倍，因此每向右移一位 str 翻倍，使得 str 的倍数与位所代表的数值一致，当位的值为 1 时，把 str 追加进 result。
                 * 如 12 的二进制值为 1100，可看作 8 + 4，即 8 个 str 加 4 个 str。
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
             * 日期字符串转 date
             * @param {string} format 日期格式
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
             * 日期字符串转另一种格式的日期字符串
             * @param {*} format 现日期格式
             * @param {*} toFormat 目标日期格式
             * 
             * * '2017-05-26'.dateFormat('yyyy-MM-dd','dd/MM/yyyy') => '26/05/2017'
             */
            dateFormat: function (format, toFormat) {
                var date = this.toDate(format)

                return date ? date.parse(toFormat) : ""
            }
        })

        extend(Function.prototype, {
            // ie8以下添加bind函数
            bind: function (oThis) {
                if (typeof this !== 'function') {
                    throw new Error("bind需用于函数")
                }

                var aArgs = Array.prototype.slice.call(arguments, 1), fToBind = this, fNOP = function () { },
                    fBound = function () {
                        return fToBind.apply(this instanceof fNOP ? this : oThis,
                            aArgs.concat(Array.prototype.slice.call(arguments)));
                    }

                fNOP.prototype = this.prototype;
                fBound.prototype = new fNOP();// fBound继承fNOP,再通过this instanceof fNOP判断fBound是否通过new调用

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
             * date 转日期字符串
             * @param {string} format 日期格式
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
            dontEnums = [/*Bug: 对象自身的属性，但用 for...in 不能枚举出来*/
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
                 * +0 和 -0 不相等
                 * NaN 和 NaN 相等
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
                        throw new TypeError('必须传递一个函数作为Promise的第1个参数');

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
                        throw new TypeError('参数必须是Promise数组');
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
                        throw new TypeError('参数必须是Promise数组')
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
                    if (promise === value) throw Error("参数不能是自身的Promise实例")

                    promise._status = status;

                    var isResolved = promise._status === 'RESOLVED',
                        callbacks = promise[isResolved ? '_resolves' : '_rejects']

                    addJob(function () {
                        if (!callbacks) {
                            if (!isResolved) {
                                var uncaughtError = "未捕获异常:" + (value instanceof Error ? value.message : String(value))

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
                    if (!(this instanceof Map)) throw "构造函数 Map 必须使用 new 创建实例"

                    this._collection = []
                    this.size = 0

                    if (mapIterable) {
                        if (!(mapIterable instanceof Array)) {
                            throw "参数必须是二维数组"
                        }

                        if (
                            !mapIterable.every(function (item) {
                                return item instanceof Array
                            })
                        ) {
                            throw "参数必须是二维数组"
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
                        if (typeof fn !== "function") throw String(fn) + " 不是一个函数"

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
                    return logError("模块必须使用函数，但【" + name + "】模块接收到：", userModules[name])
                }

                userModules[name](require, module, exports)

                if (module.exports === exports) { // 【exports.x1 = xxx1, exports.x2 = xxx2】 x1, x2 分别作为模块导出
                    for (var name$ in exports) {
                        if (!exports.hasOwnProperty(name$)) continue
                        if (!allExports.hasOwnProperty(name$)) {
                            allExports[name$] = exports[name$]
                        }
                        else {
                            logError("模块命名冲突，【" + name$ + "】模块已存在")
                        }
                    }
                }
                else if (!allExports.hasOwnProperty(name)) { //【module.exports = xxx】 xxx 作为模块导出
                    allExports[name] = module.exports
                }
                else {
                    logError("模块命名冲突，【" + name + "】模块已存在")
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
        return logError(msg + "，类型应是\"" + expected + "\"，但接收到\"" + butGot + "\"")
    }

    function print(stdout, args) {
        if (stdout.apply) {
            stdout.apply(null, args)
        }
        else {
            /**
             * IE8 的 console 不支持 apply 方法
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
                     * IE8 的 console 不支持 apply 方法
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

    function matchWith(strOrArr) {
        var list = isArray(strOrArr) ? strOrArr : strOrArr.split(","),
            map = {}

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

    function testLocalStorage() { // 测试localStorage是否能使用,浏览器开启无痕浏览模式,会导致不可用
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