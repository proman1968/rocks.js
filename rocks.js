/* * oda.js v1.0
 * (c) 2019-2021 Roman Perepelkin, Vadim Biryuk
 * Under the MIT License.
 *
 *   rocks.js
 *
 *   Reactive
 *   Optimizing
 *   Constructing
 *   Kernel with
 *   Smart cache

*/

if (!globalThis.KERNEL) {
    const regExpCheck = /^__.*__$/g;
    function makeReactive(target, saveName) {
        if (!isObject(target) || !Object.isExtensible(target)) return target;
        const op = target.__op__;
        if (op){
            let val = op.hosts.get(this);
            if (val === undefined){
                val = isNativeObject(target)?op.proxy:target;
                op.hosts.set(this, val);
            }
            return val;
        }
        else if (target !== this) {
            if (Array.isArray(target)) {
                target.forEach((val, i)=>{
                    target[i] = makeReactive.call(this, val, saveName);
                })
            }
            else if (!isNativeObject(target) && !(target instanceof Promise))
                return target;
        }
        else if (target.$proxy)
            return target;
        const options = op || Object.create(null);
        const handlers = {
            get: (target, key, resolver) => {
                if (!key) return;
                let val = options.target[key];
                if (val){
                    if (options === val || options.target === val || typeof key === 'symbol' || regExpCheck.test(key))
                        return val;
                    if (typeof val === 'function')
                        return (...args) => val.apply(options.target, args);
                    if (options.target.$proxy && KERNEL.reservedWords.includes(key))
                        return val;

                }
                else if (options.target instanceof Promise){
                    options.target.then(res=>{
                        res = makeReactive.call(this, res, options.$saveName);
                        options.target[key] = res?.[key];
                    })
                    return undefined;
                }
                const block = getBlock.call(this, options, key);
                if (KERNEL.dpTarget !== block && !block.obs && KERNEL.dpTarget && !block.deps.includes(KERNEL.dpTarget)) {
                    block.deps.push(KERNEL.dpTarget);
                    KERNEL.dpTarget.count++;
                }
                const saveName = (block.prop?.save && block.prop.name) || block.$$saveName
                if (val === undefined) {
                    if (block.getter) {
                        block.count = block.count || 0;
                        targetStack.push(KERNEL.dpTarget);
                        KERNEL.dpTarget = block;
                        val = block.getter.call(target);
                        if (val instanceof Promise) {
                            val = makeReactive.call(this, val, saveName);
                        }
                        else if (block.prop)
                            val = toType(block.prop.type, val)
                        KERNEL.dpTarget = targetStack.pop();
                        if (target === val) {
                            block.count = -1;
                            return makeReactive.call(this, val, saveName);
                        }
                        return (block.old = getProxyValue.call(this, block, val, block.count?undefined:block.old));
                    }
                }
                if (val && !block.prop?.freeze)
                    val = makeReactive.call(this, val, saveName);
                return val;
            },
            set: (target, key, value) => {
                const old = (Array.isArray(options.target) && key === 'length')?undefined:options.target[key];
                if (Object.equal(old, value)) return true;
                const block = getBlock.call(this, options, key);
                getProxyValue.call(this, block, value, old, true);
                return true;
            }
        };
        const proxy = new Proxy(options?.target || target, handlers);
        if (!target.__op__) {
            options.target = target;
            options.hosts = new Map();
            options.proxy = proxy;
            options.blocks = Object.create(null);
            if (saveName)
                options.$$saveName = saveName;
            Object.defineProperty(target, '__op__', {
                enumerable: false,
                configurable: true,
                writable: true,
                value: options
            });
        }
        options.hosts.set(this, proxy);
        return proxy;
    }
    let _blockId = 0;
    function getBlockId(){
        return ++_blockId;
    }
    let _currentBlock = 0;
    function getBlock(options, key) {
        let block = options.blocks[key];
        if (!block){
            block = (options.blocks[key] = Object.assign({ id: getBlockId(),options, key, deps: [], obs: key.startsWith?.(`#$obs$`), $$saveName: options.$$saveName }, this.constructor.__model__.$system.blocks[key] || {}));
            if (block.prop?.save){
                block.$$saveName = block.prop.name;
            }
        }
        return  block;
    }
    function getProxyValue(block, val, old, setter) {
        if (Object.equal(val, old)) return val;
        const target = block.options.target;
        const key = block.key;
        if (!block.prop?.freeze)
            val = makeReactive.call(this, val, block.$$saveName);
        target[key] = (block.prop?.type)?toType(block.prop?.type, val):val;
        if (block.obs) return val;
        if (setter && block.setter) {
            const v = block.setter.call(target, val, old);
            if (v !== undefined && !block.prop?.freeze)
                val = makeReactive.call(this, v, block.$$saveName);
        }
        const reset = resetDeps(block, [], setter);
        if (block.$$saveName)
            this.saveSettings?.(block.$$saveName, this[block.$$saveName]);
        for (let host of block.options.hosts.keys()){
            host.notify?.(block, val);
            host.updated?.([])
        }

        return val;
    }
    function resetDeps(block, stack = [], recurse) {
        if (_currentBlock === block.id)
            return false;
        _currentBlock = block.id;
        if (!block.deps?.length)
            return false;
        block.deps?.forEach(i => {
            if (i === block) return;
            if (i.prop?.freeze) return;
            i.options.target[i.key] = undefined;
            if (!recurse || stack.includes(i)) return;
            stack.add(i)
            resetDeps(i, stack, recurse);
        })
        return true;
    }
    
    function KERNEL(model = {}, statics = {}) {
        model.$system = {blocks: Object.create(null), observers: []};
        model.listeners = model.listeners || Object.create(null);
        model.props = model.props || Object.create(null);
        model.observers = model.observers || [];

        const name = model?.is || '$' + this?.name;
        if (globalThis[name])
            throw new Error(`class named "${name}" already exist!!!`)

        const cls = class extends (this || Object) {
            constructor() {
                super(...arguments);
                if (!this.$proxy){
                    for (let def in this.constructor.defaults) {
                        this['#' + def] = this.constructor.defaults[def];
                    }
                    this.$proxy = makeReactive.call(this, this);
                    cls.ctor?.call(this, ...arguments);
                }
                if (this.constructor.__model__ !== model) return;
                this.__id__ = nextId();
                this.__customCache__ = {};
                this.created?.();
            }
        };

        const fn = function () {
            if (!new.target)
                return KERNEL.call(fn.cls, ...arguments);
            return new fn.cls(...arguments);
        }
        fn.cls = cls;
        Object.defineProperty(fn, Symbol.hasInstance, { value: (obj) => obj instanceof fn.cls });
        Object.defineProperty(fn, '__model__', {
            value: model
        })
        Object.defineProperty(cls, '__model__', {
            value: model
        })
        Object.defineProperty(fn, '__statics__', {
            value: statics
        })
        Object.defineProperty(cls, '__statics__', {
            value: statics
        })
        if (name) {
            Object.defineProperty(fn, 'name', {value: name})
            Object.defineProperty(cls, 'name', { value: name });
            Object.defineProperty(cls.prototype, Symbol.toStringTag, { value: name });
        }
        model?.is && (globalThis[model?.is] = fn);

        const parents = (typeof model.extends === 'string'
            ? model.extends.replace(/ /g, '').split(',').map((e) => {
                if (globalThis[e])
                    return globalThis[e];
                throw Error(`Parent class '${e}' for inherit to '${model.is}' not found!`)
            }) : [model.extends]).filter(Boolean);

        while (model.observers.length > 0) {
            let func = model.observers.shift();
            let expr;
            let fName;
            if (typeof func === 'function') {
                fName = func.name;
                expr = func.toString();
                expr = expr.substring(0, expr.indexOf('{')).replace('async', '').replace('function', '').replace(fName, '');
            }
            else {
                fName = func.slice(0, func.indexOf('(')).trim();
                expr = func.substring(func.indexOf('(')).trim();
            }
            expr = expr.replace('(', '').replace(')', '').trim();
            const vars = expr.split(',').map((prop, idx) => {
                prop = prop.trim();
                return { prop, func: createFunc('', prop, model), arg: 'v' + idx };
            });
            if (typeof func === 'string') {
                const args = vars.map(i => {
                    const idx = func.indexOf('(');
                    func = func.slice(0, idx) + func.slice(idx).replace(i.prop, i.arg);
                    return i.arg;
                }).join(',');
                func = createFunc(args, func, model);
            }
            if (!func) throw new Error(`function "${fName}" for string observer not found!!`)
            const obsName = `$obs$${fName}`;
            function funcObserver() {
                const params = vars.map(v => {
                    return v.func.call(this);
                });
                if (!params.includes(undefined)) {
                    this.async(() => {
                        let target = KERNEL.dpTarget;
                        KERNEL.dpTarget = undefined;
                        func.call(this, ...params)
                        KERNEL.dpTarget = target;
                    });
                }
                return true;
            }
            if (!fName) throw new Error('ERROR: no function name!');
            model.props[obsName] = {
                get: funcObserver
            };
            model.$system.observers.push(obsName);
        }
        let descriptors = Object.getOwnPropertyDescriptors(model.props);
        for (let key in descriptors) {
            let prop = descriptors[key].value;
            if (typeof prop === 'function')
                prop = (prop.name === key) ? { get: prop } : { type: prop };
            if (Array.isArray(prop))
                prop = { default: prop, type: Array };
            else if (prop === null || typeof prop !== "object")
                prop = { default: prop, type: prop ? prop.__proto__.constructor : Object };
            else if (Object.keys(prop).length === 0 || (!prop.get && !prop.set && prop.default === undefined && !prop.type))
                prop = { default: prop, type: Object };
            if (typeof prop.get === 'string')
                prop.get = model[prop.get];
            if (typeof prop.set === 'string')
                prop.set = model[prop.set];
            if (!prop.type && prop.default !== undefined)
                prop.type = prop.default === null ? Object : prop.default.__proto__.constructor;
            model.props[key] = prop;
        }
        if (this) {
            parents.unshift(this);
            for (const key in this.__model__.listeners) {
                 model.listeners[key] = model.listeners[key] || this.__model__.listeners[key];
            }
        }
        for (let parent of parents) {
            descriptors = Object.getOwnPropertyDescriptors(model.props);
            const parentdDescrs = Object.getOwnPropertyDescriptors(parent.__model__.props);
            for (let key in parentdDescrs) {
                const parentProp = parentdDescrs[key].value;
                const targetProp = descriptors[key]?.value;
                if (targetProp) {
                    for (let k in parentProp) {
                        if (['get', 'default'].includes(k) && ('get' in targetProp || 'default' in targetProp)) continue;
                        targetProp[k] = targetProp[k] || parentProp[k];
                    }
                }
                model.props[key] = targetProp || parentProp;
            }
            for (const key in parent.__model__.listeners) {
                model.listeners[key] = model.listeners[key] || parent.__model__.listeners[key];
            }
            for (let key in parent.__model__) {
                if (key in model) continue;
                Object.defineProperty(model, key, Object.getOwnPropertyDescriptor(parent.__model__, key));
            }
            for (let s in parent.__statics__){
                statics[s] = statics[s] || parent.__statics__[s];
            }
        }

        Object.defineProperties(cls.prototype, {
            $super: {
                enumerable: true,
                value: function (func, ...args) {
                    // return this.constructor.prototype?.[func]?.call(this, ...args); // does not worked
                    return Object.getPrototypeOf(Object.getPrototypeOf(this)).constructor.prototype?.[func]?.call(this, ...args);
                }
            },
            listen: {
                enumerable: false,
                value: function (event, handler) {
                    if (typeof event === "function"){
                        handler = event;
                        event = '__any__';
                    }
                    const ev = this.__handlers__ || (this.__handlers__ = {});
                    (ev[event] || (ev[event] = [])).add(handler);
                }
            },
            unlisten: {
                enumerable: false,
                value: function (event, handler) {
                    if (typeof event === "function"){
                        handler = event;
                        event = '__any__';
                    }
                    const list = this.__handlers__?.[event];
                    if (!list) return;
                    handler ? list.remove(handler) : list.clear();
                }
            }, //todo возможно надо убрать addEventListener removeEventListener
            addEventListener: {
                enumerable: false,
                value: cls.prototype.listen
            },
            removeEventListener: {
                enumerable: false,
                value: cls.prototype.unlisten
            },
            fire: {
                enumerable: false,
                value: async function (event, value) {
                    const ev = new CustomEvent(event, { detail: { value, target: this }, composed: true });
                    (this.__handlers__?.[event] || []).forEach(i => i(ev));
                    (this.__handlers__?.['__any__'] || []).forEach(i => i(ev))
                }
            },
        })
        Object.defineProperty(cls.prototype, 'props', {
            get() { return model.props }
        })
        if (model.is && !globalThis[model.is]) {
            globalThis[model.is] = cls;
        }
        cls.defaults = {};
        descriptors = Object.getOwnPropertyDescriptors(model.props);
        for (let name in descriptors) {
            const prop = descriptors[name].value;
            prop.name = name;
            const key = `#${name}`;
            const desc = { enumerable: !name.startsWith('_'), configurable: true };
            model.$system.blocks[key] = Object.create(null);
            model.$system.blocks[key].getter = prop.get;
            model.$system.blocks[key].setter = prop.set;
            model.$system.blocks[key].prop = prop;
            model.$system.blocks[key].key = key;
            desc.get = function () {
                let val = this[key];
                if (val === undefined) {
                    val = this.$proxy[key];
                }
                else if (KERNEL.dpTarget) {
                    const block = this.__op__.blocks[key];
                    if (!block?.deps.includes(KERNEL.dpTarget)) {
                        val = this.$proxy[key];
                    }
                }
                return val;
            }
            desc.set = function (val) {
                this.$proxy[key] = toType(prop.type, val);
            }
            desc.set.set = prop.set;
            Object.defineProperty(cls.prototype, name, desc);
            if (prop.default === undefined) continue;
            Object.defineProperty(cls.defaults, name, {
                configurable: true,
                enumerable: true,
                get() {
                    if (typeof prop.default === "function")
                        return prop.default.call(this);
                    else if (Array.isArray(prop.default))
                        return Array.from(prop.default);
                    else if (isObject(prop.default))
                        return Object.assign({}, prop.default);
                    return prop.default;
                }
            });
        }
        descriptors = Object.getOwnPropertyDescriptors(model)
        for (let name in descriptors) {
            const desc = descriptors[name];
            if (typeof desc.value === 'function' && name !== 'ctor') {
                Object.defineProperty(cls.prototype, name, {
                    enumerable: true,
                    writable: true,
                    value: function (...args) {
                        return desc.value.call(this, ...args);
                    }
                });
            }
            else if (!KERNEL.reservedWords.includes(name)) {
                if ('value' in desc){
                    const def = desc.value;
                    Object.defineProperty(cls.defaults, name, {
                        enumerable: true,
                        get() {
                            if (Array.isArray(def))
                                return Array.from(def);
                            else if (isObject(def))
                                return Object.assign({}, def);
                            return def;
                        }
                    });
                    desc.value = undefined;
                    delete desc.value;
                    delete desc.writable;
                    delete desc.enumerable;
                }
                const key = '#' + name;
                model.$system.blocks[key] = {key, getter:desc.get, setter: desc.set};
                desc.enumerable = true;
                desc.get = function () {
                    let val = this[key];
                    if (val === undefined) {
                        val = this.$proxy[key];
                    }
                    else if (KERNEL.dpTarget) {
                        const block = this.__op__.blocks[key];
                        if (!block?.deps.includes(KERNEL.dpTarget)) {
                            val = this.$proxy[key];
                        }
                    }
                    return val;
                }
                desc.set = function (v) {
                    this.$proxy[key] = v;
                }
                Object.defineProperty(cls.prototype, name, desc);
            }
        }
        const prefix = model.props?.prefix?.default;
        if (prefix) {
            KERNEL.__factory__[prefix] = KERNEL.__factory__[prefix] || cls;
        }
        const ctor = model.ctor;
        cls.ctor = function (...args) {
            ctor?.call(this, ...args);
        }
        cls.__id__ = nextClsId();
        if (statics){
            for (let i in statics)
                fn[i] = statics[i];
        }
        return fn;
    }
    KERNEL.makeReactive = makeReactive;
    const targetStack = [];
    // KERNEL.targets = [];
    globalThis.KERNEL = KERNEL;
    let obj_counter = 0;
    let cls_counter = 0;
    KERNEL.reservedWords = [
        '__proto__', 'is', 'template', 'props', 'extends', 'keys', 'observers', 'listeners', 'hostAttributes', 'keyBindings', 'imports', '$system', '$core', '$proxy'
    ]
    function nextId() {
        return ++obj_counter;
    }
    function nextClsId() {
        return ++cls_counter;
    }
    function isObject(obj) {
        return obj && typeof obj === 'object';
    }
    String:{
        const kebabGlossary = Object.create(null);
        function toKebab(str) {
            return (kebabGlossary[str] = str.replace(/\B([A-Z])/g, '-$1').toLowerCase());
        }
        if (!String.toKebabCase) {
            Object.defineProperty(String.prototype, 'toKebabCase', {
                enumerable: false, value: function () {
                    const s = this.toString();
                    const str = kebabGlossary[s];
                    return str ? str : toKebab(s);
                }
            });
        }
        const camelGlossary = Object.create(null);
        function toCamel(str) {
            return (camelGlossary[str] = str.replace(/-(\w)/g, function (_, c) { return c ? c.toUpperCase() : '' }))
        }

        if (!String.toCamelCase) {
            Object.defineProperty(String.prototype, 'toCamelCase', {
                enumerable: false, value: function () {
                    const s = this.toString();
                    const str = camelGlossary[s];
                    return str ? str : toCamel(s);
                }
            });
        }
    }
    Object:{
        Object.equal = Object.equal || function (a, b, recurse) {
            if (a === b) return true;
            if (!isObject(a) || !isObject(b)) return false;
            if ((a?.__op__ || a) === (b?.__op__ || b)) return true;
            if (recurse) {
                for (let key in Object.assign({}, a, b))
                    if (!Object.equal(b[key], a[key], recurse)) return false;
                return true;
            }
            return false;
        };
    }

    Array:{
        const fnIncl = Array.prototype.includes;
        Object.defineProperty(Array.prototype, 'includes', {
            enumerable: false, configurable: true, value: function (item) {
                return fnIncl.call(this, item) || this.indexOf(item) > -1;
            }
        });
        if (!Array.prototype.nativeIndexOf) {
            Object.defineProperty(Array.prototype, 'nativeIndexOf', { enumerable: false, configurable: true, value: Array.prototype.indexOf });
            Object.defineProperty(Array.prototype, 'indexOf', {
                enumerable: false, configurable: true, value: function (item) {
                    let idx = Array.prototype.nativeIndexOf.call(this, item);
                    if (!~idx)
                        idx = this.findIndex(i => {
                            return Object.equal(i, item);
                        })
                    return idx;
                }
            });
            Object.defineProperty(Array.prototype, 'has', {
                enumerable: false, configurable: true, value: Array.prototype.includes
            });
            Object.defineProperty(Array.prototype, 'clear', {
                enumerable: false, configurable: true, value: function () {
                    this.splice(0);
                }
            });
            Object.defineProperty(Array.prototype, 'last', {
                enumerable: false, configurable: true, get() {
                    return this[this.length - 1];
                }
            });
            Object.defineProperty(Array.prototype, 'add', {
                enumerable: false, configurable: true, value: function (...item) {
                    let index = -1;
                    for (let i of item) {
                        index = this.indexOf(i);
                        if (index>-1) continue;
                        index = this.push(i);
                        if (this.__op__)
                            this.__op__.proxy['length'] = index;
                        index--;
                    }
                    return index;
                }
            });
            Object.defineProperty(Array.prototype, 'remove', {
                enumerable: false, configurable: true, value: function (...items) {
                    for (const item of items) {
                        let idx = this.indexOf(item);
                        if (~idx)
                            this.splice(idx, 1);
                    }
                }
            });
        }
    }

    function isNativeObject(obj) {
        return obj && (obj.constructor === Object);//toString.call(obj) === '[object Object]';
    }
    function toBool(v, def = false) {
        if (!v)
            return def;
        switch (typeof v) {
            case 'object': return true;
            case 'string': return v.toLowerCase() === 'true';
            case 'boolean': return v;
            case 'number': return v !== 0;
        }
        return false;
    }
    function toType(type, value) {
        switch (type) {
            case Boolean: return toBool(value);
            case Number: return parseFloat(value) || 0;
            case String: return value?.toString() || '';
            case Date: return Date.parse(value) || new Date(value)
            default: return value;
        }
    }
    globalThis.toType = toType;
    function createFunc(vars, expr, prototype = {}) {
        try {
            return new Function(vars, `with (this) {return (${expr})}`);
        }
        catch (e) {
            console.error('%c' + expr + '\r\n', 'color: black; font-weight: bold; padding: 4px;', prototype.is, prototype.url, e);
        }
    }
}
export default globalThis.KERNEL;