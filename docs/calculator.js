"use strict";
// This object will hold all exports.
var Haste = {};
if(typeof window === 'undefined') window = global;

/* Constructor functions for small ADTs. */
function T0(t){this._=t;}
function T1(t,a){this._=t;this.a=a;}
function T2(t,a,b){this._=t;this.a=a;this.b=b;}
function T3(t,a,b,c){this._=t;this.a=a;this.b=b;this.c=c;}
function T4(t,a,b,c,d){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;}
function T5(t,a,b,c,d,e){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;}
function T6(t,a,b,c,d,e,f){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;this.f=f;}

/* Thunk
   Creates a thunk representing the given closure.
   If the non-updatable flag is undefined, the thunk is updatable.
*/
function T(f, nu) {
    this.f = f;
    if(nu === undefined) {
        this.x = __updatable;
    }
}

/* Hint to optimizer that an imported symbol is strict. */
function __strict(x) {return x}

// A tailcall.
function F(f) {
    this.f = f;
}

// A partially applied function. Invariant: members are never thunks.
function PAP(f, args) {
    this.f = f;
    this.args = args;
    this.arity = f.length - args.length;
}

// "Zero" object; used to avoid creating a whole bunch of new objects
// in the extremely common case of a nil-like data constructor.
var __Z = new T0(0);

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

// Indicates that a closure-creating tail loop isn't done.
var __continue = {};

/* Generic apply.
   Applies a function *or* a partial application object to a list of arguments.
   See https://ghc.haskell.org/trac/ghc/wiki/Commentary/Rts/HaskellExecution/FunctionCalls
   for more information.
*/
function A(f, args) {
    while(true) {
        f = E(f);
        if(f instanceof Function) {
            if(args.length === f.length) {
                return f.apply(null, args);
            } else if(args.length < f.length) {
                return new PAP(f, args);
            } else {
                var f2 = f.apply(null, args.slice(0, f.length));
                args = args.slice(f.length);
                f = B(f2);
            }
        } else if(f instanceof PAP) {
            if(args.length === f.arity) {
                return f.f.apply(null, f.args.concat(args));
            } else if(args.length < f.arity) {
                return new PAP(f.f, f.args.concat(args));
            } else {
                var f2 = f.f.apply(null, f.args.concat(args.slice(0, f.arity)));
                args = args.slice(f.arity);
                f = B(f2);
            }
        } else {
            return f;
        }
    }
}

function A1(f, x) {
    f = E(f);
    if(f instanceof Function) {
        return f.length === 1 ? f(x) : new PAP(f, [x]);
    } else if(f instanceof PAP) {
        return f.arity === 1 ? f.f.apply(null, f.args.concat([x]))
                             : new PAP(f.f, f.args.concat([x]));
    } else {
        return f;
    }
}

function A2(f, x, y) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 2:  return f(x, y);
        case 1:  return A1(B(f(x)), y);
        default: return new PAP(f, [x,y]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 2:  return f.f.apply(null, f.args.concat([x,y]));
        case 1:  return A1(B(f.f.apply(null, f.args.concat([x]))), y);
        default: return new PAP(f.f, f.args.concat([x,y]));
        }
    } else {
        return f;
    }
}

function A3(f, x, y, z) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 3:  return f(x, y, z);
        case 2:  return A1(B(f(x, y)), z);
        case 1:  return A2(B(f(x)), y, z);
        default: return new PAP(f, [x,y,z]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 3:  return f.f.apply(null, f.args.concat([x,y,z]));
        case 2:  return A1(B(f.f.apply(null, f.args.concat([x,y]))), z);
        case 1:  return A2(B(f.f.apply(null, f.args.concat([x]))), y, z);
        default: return new PAP(f.f, f.args.concat([x,y,z]));
        }
    } else {
        return f;
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f !== __blackhole) {
            if(t.x === __updatable) {
                var f = t.f;
                t.f = __blackhole;
                t.x = f();
            } else {
                return t.f();
            }
        }
        if(t.x === __updatable) {
            throw 'Infinite loop!';
        } else {
            return t.x;
        }
    } else {
        return t;
    }
}

/* Tail call chain counter. */
var C = 0, Cs = [];

/* Bounce
   Bounce on a trampoline for as long as we get a function back.
*/
function B(f) {
    Cs.push(C);
    while(f instanceof F) {
        var fun = f.f;
        f.f = __blackhole;
        C = 0;
        f = fun();
    }
    C = Cs.pop();
    return f;
}

// Export Haste, A, B and E. Haste because we need to preserve exports, A, B
// and E because they're handy for Haste.Foreign.
if(!window) {
    var window = {};
}
window['Haste'] = Haste;
window['A'] = A;
window['E'] = E;
window['B'] = B;


/* Throw an error.
   We need to be able to use throw as an exception so we wrap it in a function.
*/
function die(err) {
    throw E(err);
}

function quot(a, b) {
    return (a-a%b)/b;
}

function quotRemI(a, b) {
    return {_:0, a:(a-a%b)/b, b:a%b};
}

// 32 bit integer multiplication, with correct overflow behavior
// note that |0 or >>>0 needs to be applied to the result, for int and word
// respectively.
if(Math.imul) {
    var imul = Math.imul;
} else {
    var imul = function(a, b) {
        // ignore high a * high a as the result will always be truncated
        var lows = (a & 0xffff) * (b & 0xffff); // low a * low b
        var aB = (a & 0xffff) * (b & 0xffff0000); // low a * high b
        var bA = (a & 0xffff0000) * (b & 0xffff); // low b * high a
        return lows + aB + bA; // sum will not exceed 52 bits, so it's safe
    }
}

function addC(a, b) {
    var x = a+b;
    return {_:0, a:x & 0xffffffff, b:x > 0x7fffffff};
}

function subC(a, b) {
    var x = a-b;
    return {_:0, a:x & 0xffffffff, b:x < -2147483648};
}

function sinh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / 2;
}

function tanh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / (Math.exp(arg) + Math.exp(-arg));
}

function cosh (arg) {
    return (Math.exp(arg) + Math.exp(-arg)) / 2;
}

function isFloatFinite(x) {
    return isFinite(x);
}

function isDoubleFinite(x) {
    return isFinite(x);
}

function err(str) {
    die(toJSStr(str));
}

/* unpackCString#
   NOTE: update constructor tags if the code generator starts munging them.
*/
function unCStr(str) {return unAppCStr(str, __Z);}

function unFoldrCStr(str, f, z) {
    var acc = z;
    for(var i = str.length-1; i >= 0; --i) {
        acc = B(A(f, [str.charCodeAt(i), acc]));
    }
    return acc;
}

function unAppCStr(str, chrs) {
    var i = arguments[2] ? arguments[2] : 0;
    if(i >= str.length) {
        return E(chrs);
    } else {
        return {_:1,a:str.charCodeAt(i),b:new T(function() {
            return unAppCStr(str,chrs,i+1);
        })};
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str._ == 1; str = E(str.b)) {
        s += String.fromCharCode(E(str.a));
    }
    return s;
}

// newMutVar
function nMV(val) {
    return ({x: val});
}

// readMutVar
function rMV(mv) {
    return mv.x;
}

// writeMutVar
function wMV(mv, val) {
    mv.x = val;
}

// atomicModifyMutVar
function mMV(mv, f) {
    var x = B(A(f, [mv.x]));
    mv.x = x.a;
    return x.b;
}

function localeEncoding() {
    var le = newByteArr(5);
    le['v']['i8'][0] = 'U'.charCodeAt(0);
    le['v']['i8'][1] = 'T'.charCodeAt(0);
    le['v']['i8'][2] = 'F'.charCodeAt(0);
    le['v']['i8'][3] = '-'.charCodeAt(0);
    le['v']['i8'][4] = '8'.charCodeAt(0);
    return le;
}

var isDoubleNaN = isNaN;
var isFloatNaN = isNaN;

function isDoubleInfinite(d) {
    return (d === Infinity);
}
var isFloatInfinite = isDoubleInfinite;

function isDoubleNegativeZero(x) {
    return (x===0 && (1/x)===-Infinity);
}
var isFloatNegativeZero = isDoubleNegativeZero;

function strEq(a, b) {
    return a == b;
}

function strOrd(a, b) {
    if(a < b) {
        return 0;
    } else if(a == b) {
        return 1;
    }
    return 2;
}

/* Convert a JS exception into a Haskell JSException */
function __hsException(e) {
  e = e.toString();
  var x = new Long(2904464383, 3929545892, true);
  var y = new Long(3027541338, 3270546716, true);
  var t = new T5(0, x, y
                  , new T5(0, x, y
                            , unCStr("haste-prim")
                            , unCStr("Haste.Prim.Foreign")
                            , unCStr("JSException")), __Z, __Z);
  var show = function(x) {return unCStr(E(x).a);}
  var dispEx = function(x) {return unCStr("JavaScript exception: " + E(x).a);}
  var showList = function(_, s) {return unAppCStr(e, s);}
  var showsPrec = function(_, _p, s) {return unAppCStr(e, s);}
  var showDict = new T3(0, showsPrec, show, showList);
  var self;
  var fromEx = function(_) {return new T1(1, self);}
  var dict = new T5(0, t, showDict, null /* toException */, fromEx, dispEx);
  self = new T2(0, dict, new T1(0, e));
  return self;
}

function jsCatch(act, handler) {
    try {
        return B(A(act,[0]));
    } catch(e) {
        if(typeof e._ === 'undefined') {
            e = __hsException(e);
        }
        return B(A(handler,[e, 0]));
    }
}

/* Haste represents constructors internally using 1 for the first constructor,
   2 for the second, etc.
   However, dataToTag should use 0, 1, 2, etc. Also, booleans might be unboxed.
 */
function dataToTag(x) {
    if(x instanceof Object) {
        return x._;
    } else {
        return x;
    }
}

function __word_encodeDouble(d, e) {
    return d * Math.pow(2,e);
}

var __word_encodeFloat = __word_encodeDouble;
var jsRound = Math.round, rintDouble = jsRound, rintFloat = jsRound;
var jsTrunc = Math.trunc ? Math.trunc : function(x) {
    return x < 0 ? Math.ceil(x) : Math.floor(x);
};
function jsRoundW(n) {
    return Math.abs(jsTrunc(n));
}
var realWorld = undefined;
if(typeof _ == 'undefined') {
    var _ = undefined;
}

function popCnt64(i) {
    return popCnt(i.low) + popCnt(i.high);
}

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

function __clz(bits, x) {
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    } else {
        return bits - (1 + Math.floor(Math.log(x)/Math.LN2));
    }
}

// TODO: can probably be done much faster with arithmetic tricks like __clz
function __ctz(bits, x) {
    var y = 1;
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    }
    for(var i = 0; i < bits; ++i) {
        if(y & x) {
            return i;
        } else {
            y <<= 1;
        }
    }
    return 0;
}

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
    if(x === 0) {
        return __decodedZeroF;
    }
    rts_scratchFloat[0] = x;
    var sign = x < 0 ? -1 : 1;
    var exp = ((rts_scratchW32[0] >> 23) & 0xff) - 150;
    var man = rts_scratchW32[0] & 0x7fffff;
    if(exp === 0) {
        ++exp;
    } else {
        man |= (1 << 23);
    }
    return {_:0, a:sign*man, b:exp};
}

var __decodedZero = {_:0,a:1,b:0,c:0,d:0};
var __decodedZeroF = {_:0,a:1,b:0};

function decodeDouble(x) {
    if(x === 0) {
        // GHC 7.10+ *really* doesn't like 0 to be represented as anything
        // but zeroes all the way.
        return __decodedZero;
    }
    rts_scratchDouble[0] = x;
    var sign = x < 0 ? -1 : 1;
    var manHigh = rts_scratchW32[1] & 0xfffff;
    var manLow = rts_scratchW32[0];
    var exp = ((rts_scratchW32[1] >> 20) & 0x7ff) - 1075;
    if(exp === 0) {
        ++exp;
    } else {
        manHigh |= (1 << 20);
    }
    return {_:0, a:sign, b:manHigh, c:manLow, d:exp};
}

function isNull(obj) {
    return obj === null;
}

function jsRead(str) {
    return Number(str);
}

function jsShowI(val) {return val.toString();}
function jsShow(val) {
    var ret = val.toString();
    return val == Math.round(val) ? ret + '.0' : ret;
}

window['jsGetMouseCoords'] = function jsGetMouseCoords(e) {
    var posx = 0;
    var posy = 0;
    if (!e) var e = window.event;
    if (e.pageX || e.pageY) 	{
	posx = e.pageX;
	posy = e.pageY;
    }
    else if (e.clientX || e.clientY) 	{
	posx = e.clientX + document.body.scrollLeft
	    + document.documentElement.scrollLeft;
	posy = e.clientY + document.body.scrollTop
	    + document.documentElement.scrollTop;
    }
    return [posx - (e.currentTarget.offsetLeft || 0),
	    posy - (e.currentTarget.offsetTop || 0)];
}

var jsRand = Math.random;

// Concatenate a Haskell list of JS strings
function jsCat(strs, sep) {
    var arr = [];
    strs = E(strs);
    while(strs._) {
        strs = E(strs);
        arr.push(E(strs.a));
        strs = E(strs.b);
    }
    return arr.join(sep);
}

// Parse a JSON message into a Haste.JSON.JSON value.
// As this pokes around inside Haskell values, it'll need to be updated if:
// * Haste.JSON.JSON changes;
// * E() starts to choke on non-thunks;
// * data constructor code generation changes; or
// * Just and Nothing change tags.
function jsParseJSON(str) {
    try {
        var js = JSON.parse(str);
        var hs = toHS(js);
    } catch(_) {
        return __Z;
    }
    return {_:1,a:hs};
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return {_:0, a:jsRead(obj)};
    case 'string':
        return {_:1, a:obj};
    case 'boolean':
        return {_:2, a:obj}; // Booleans are special wrt constructor tags!
    case 'object':
        if(obj instanceof Array) {
            return {_:3, a:arr2lst_json(obj, 0)};
        } else if (obj == null) {
            return {_:5};
        } else {
            // Object type but not array - it's a dictionary.
            // The RFC doesn't say anything about the ordering of keys, but
            // considering that lots of people rely on keys being "in order" as
            // defined by "the same way someone put them in at the other end,"
            // it's probably a good idea to put some cycles into meeting their
            // misguided expectations.
            var ks = [];
            for(var k in obj) {
                ks.unshift(k);
            }
            var xs = [0];
            for(var i = 0; i < ks.length; i++) {
                xs = {_:1, a:{_:0, a:ks[i], b:toHS(obj[ks[i]])}, b:xs};
            }
            return {_:4, a:xs};
        }
    }
}

function arr2lst_json(arr, elem) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1, a:toHS(arr[elem]), b:new T(function() {return arr2lst_json(arr,elem+1);}),c:true}
}

/* gettimeofday(2) */
function gettimeofday(tv, _tz) {
    var t = new Date().getTime();
    writeOffAddr("i32", 4, tv, 0, (t/1000)|0);
    writeOffAddr("i32", 4, tv, 1, ((t%1000)*1000)|0);
    return 0;
}

// Create a little endian ArrayBuffer representation of something.
function toABHost(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    return a;
}

function toABSwap(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    var bs = new Uint8Array(a);
    for(var i = 0, j = n-1; i < j; ++i, --j) {
        var tmp = bs[i];
        bs[i] = bs[j];
        bs[j] = tmp;
    }
    return a;
}

window['toABle'] = toABHost;
window['toABbe'] = toABSwap;

// Swap byte order if host is not little endian.
var buffer = new ArrayBuffer(2);
new DataView(buffer).setInt16(0, 256, true);
if(new Int16Array(buffer)[0] !== 256) {
    window['toABle'] = toABSwap;
    window['toABbe'] = toABHost;
}

/* bn.js by Fedor Indutny, see doc/LICENSE.bn for license */
var __bn = {};
(function (module, exports) {
'use strict';

function BN(number, base, endian) {
  // May be `new BN(bn)` ?
  if (number !== null &&
      typeof number === 'object' &&
      Array.isArray(number.words)) {
    return number;
  }

  this.negative = 0;
  this.words = null;
  this.length = 0;

  if (base === 'le' || base === 'be') {
    endian = base;
    base = 10;
  }

  if (number !== null)
    this._init(number || 0, base || 10, endian || 'be');
}
if (typeof module === 'object')
  module.exports = BN;
else
  exports.BN = BN;

BN.BN = BN;
BN.wordSize = 26;

BN.max = function max(left, right) {
  if (left.cmp(right) > 0)
    return left;
  else
    return right;
};

BN.min = function min(left, right) {
  if (left.cmp(right) < 0)
    return left;
  else
    return right;
};

BN.prototype._init = function init(number, base, endian) {
  if (typeof number === 'number') {
    return this._initNumber(number, base, endian);
  } else if (typeof number === 'object') {
    return this._initArray(number, base, endian);
  }
  if (base === 'hex')
    base = 16;

  number = number.toString().replace(/\s+/g, '');
  var start = 0;
  if (number[0] === '-')
    start++;

  if (base === 16)
    this._parseHex(number, start);
  else
    this._parseBase(number, base, start);

  if (number[0] === '-')
    this.negative = 1;

  this.strip();

  if (endian !== 'le')
    return;

  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initNumber = function _initNumber(number, base, endian) {
  if (number < 0) {
    this.negative = 1;
    number = -number;
  }
  if (number < 0x4000000) {
    this.words = [ number & 0x3ffffff ];
    this.length = 1;
  } else if (number < 0x10000000000000) {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff
    ];
    this.length = 2;
  } else {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff,
      1
    ];
    this.length = 3;
  }

  if (endian !== 'le')
    return;

  // Reverse the bytes
  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initArray = function _initArray(number, base, endian) {
  if (number.length <= 0) {
    this.words = [ 0 ];
    this.length = 1;
    return this;
  }

  this.length = Math.ceil(number.length / 3);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  var off = 0;
  if (endian === 'be') {
    for (var i = number.length - 1, j = 0; i >= 0; i -= 3) {
      var w = number[i] | (number[i - 1] << 8) | (number[i - 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  } else if (endian === 'le') {
    for (var i = 0, j = 0; i < number.length; i += 3) {
      var w = number[i] | (number[i + 1] << 8) | (number[i + 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  }
  return this.strip();
};

function parseHex(str, start, end) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r <<= 4;

    // 'a' - 'f'
    if (c >= 49 && c <= 54)
      r |= c - 49 + 0xa;

    // 'A' - 'F'
    else if (c >= 17 && c <= 22)
      r |= c - 17 + 0xa;

    // '0' - '9'
    else
      r |= c & 0xf;
  }
  return r;
}

BN.prototype._parseHex = function _parseHex(number, start) {
  // Create possibly bigger array to ensure that it fits the number
  this.length = Math.ceil((number.length - start) / 6);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  // Scan 24-bit chunks and add them to the number
  var off = 0;
  for (var i = number.length - 6, j = 0; i >= start; i -= 6) {
    var w = parseHex(number, i, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
    off += 24;
    if (off >= 26) {
      off -= 26;
      j++;
    }
  }
  if (i + 6 !== start) {
    var w = parseHex(number, start, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
  }
  this.strip();
};

function parseBase(str, start, end, mul) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r *= mul;

    // 'a'
    if (c >= 49)
      r += c - 49 + 0xa;

    // 'A'
    else if (c >= 17)
      r += c - 17 + 0xa;

    // '0' - '9'
    else
      r += c;
  }
  return r;
}

BN.prototype._parseBase = function _parseBase(number, base, start) {
  // Initialize as zero
  this.words = [ 0 ];
  this.length = 1;

  // Find length of limb in base
  for (var limbLen = 0, limbPow = 1; limbPow <= 0x3ffffff; limbPow *= base)
    limbLen++;
  limbLen--;
  limbPow = (limbPow / base) | 0;

  var total = number.length - start;
  var mod = total % limbLen;
  var end = Math.min(total, total - mod) + start;

  var word = 0;
  for (var i = start; i < end; i += limbLen) {
    word = parseBase(number, i, i + limbLen, base);

    this.imuln(limbPow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }

  if (mod !== 0) {
    var pow = 1;
    var word = parseBase(number, i, number.length, base);

    for (var i = 0; i < mod; i++)
      pow *= base;
    this.imuln(pow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }
};

BN.prototype.copy = function copy(dest) {
  dest.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    dest.words[i] = this.words[i];
  dest.length = this.length;
  dest.negative = this.negative;
};

BN.prototype.clone = function clone() {
  var r = new BN(null);
  this.copy(r);
  return r;
};

// Remove leading `0` from `this`
BN.prototype.strip = function strip() {
  while (this.length > 1 && this.words[this.length - 1] === 0)
    this.length--;
  return this._normSign();
};

BN.prototype._normSign = function _normSign() {
  // -0 = 0
  if (this.length === 1 && this.words[0] === 0)
    this.negative = 0;
  return this;
};

var zeros = [
  '',
  '0',
  '00',
  '000',
  '0000',
  '00000',
  '000000',
  '0000000',
  '00000000',
  '000000000',
  '0000000000',
  '00000000000',
  '000000000000',
  '0000000000000',
  '00000000000000',
  '000000000000000',
  '0000000000000000',
  '00000000000000000',
  '000000000000000000',
  '0000000000000000000',
  '00000000000000000000',
  '000000000000000000000',
  '0000000000000000000000',
  '00000000000000000000000',
  '000000000000000000000000',
  '0000000000000000000000000'
];

var groupSizes = [
  0, 0,
  25, 16, 12, 11, 10, 9, 8,
  8, 7, 7, 7, 7, 6, 6,
  6, 6, 6, 6, 6, 5, 5,
  5, 5, 5, 5, 5, 5, 5,
  5, 5, 5, 5, 5, 5, 5
];

var groupBases = [
  0, 0,
  33554432, 43046721, 16777216, 48828125, 60466176, 40353607, 16777216,
  43046721, 10000000, 19487171, 35831808, 62748517, 7529536, 11390625,
  16777216, 24137569, 34012224, 47045881, 64000000, 4084101, 5153632,
  6436343, 7962624, 9765625, 11881376, 14348907, 17210368, 20511149,
  24300000, 28629151, 33554432, 39135393, 45435424, 52521875, 60466176
];

BN.prototype.toString = function toString(base, padding) {
  base = base || 10;
  var padding = padding | 0 || 1;
  if (base === 16 || base === 'hex') {
    var out = '';
    var off = 0;
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var w = this.words[i];
      var word = (((w << off) | carry) & 0xffffff).toString(16);
      carry = (w >>> (24 - off)) & 0xffffff;
      if (carry !== 0 || i !== this.length - 1)
        out = zeros[6 - word.length] + word + out;
      else
        out = word + out;
      off += 2;
      if (off >= 26) {
        off -= 26;
        i--;
      }
    }
    if (carry !== 0)
      out = carry.toString(16) + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else if (base === (base | 0) && base >= 2 && base <= 36) {
    var groupSize = groupSizes[base];
    var groupBase = groupBases[base];
    var out = '';
    var c = this.clone();
    c.negative = 0;
    while (c.cmpn(0) !== 0) {
      var r = c.modn(groupBase).toString(base);
      c = c.idivn(groupBase);

      if (c.cmpn(0) !== 0)
        out = zeros[groupSize - r.length] + r + out;
      else
        out = r + out;
    }
    if (this.cmpn(0) === 0)
      out = '0' + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else {
    throw 'Base should be between 2 and 36';
  }
};

BN.prototype.toJSON = function toJSON() {
  return this.toString(16);
};

BN.prototype.toArray = function toArray(endian, length) {
  this.strip();
  var littleEndian = endian === 'le';
  var res = new Array(this.byteLength());
  res[0] = 0;

  var q = this.clone();
  if (!littleEndian) {
    // Assume big-endian
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[res.length - i - 1] = b;
    }
  } else {
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[i] = b;
    }
  }

  if (length) {
    while (res.length < length) {
      if (littleEndian)
        res.push(0);
      else
        res.unshift(0);
    }
  }

  return res;
};

if (Math.clz32) {
  BN.prototype._countBits = function _countBits(w) {
    return 32 - Math.clz32(w);
  };
} else {
  BN.prototype._countBits = function _countBits(w) {
    var t = w;
    var r = 0;
    if (t >= 0x1000) {
      r += 13;
      t >>>= 13;
    }
    if (t >= 0x40) {
      r += 7;
      t >>>= 7;
    }
    if (t >= 0x8) {
      r += 4;
      t >>>= 4;
    }
    if (t >= 0x02) {
      r += 2;
      t >>>= 2;
    }
    return r + t;
  };
}

// Return number of used bits in a BN
BN.prototype.bitLength = function bitLength() {
  var hi = 0;
  var w = this.words[this.length - 1];
  var hi = this._countBits(w);
  return (this.length - 1) * 26 + hi;
};

BN.prototype.byteLength = function byteLength() {
  return Math.ceil(this.bitLength() / 8);
};

// Return negative clone of `this`
BN.prototype.neg = function neg() {
  if (this.cmpn(0) === 0)
    return this.clone();

  var r = this.clone();
  r.negative = this.negative ^ 1;
  return r;
};

BN.prototype.ineg = function ineg() {
  this.negative ^= 1;
  return this;
};

// Or `num` with `this` in-place
BN.prototype.iuor = function iuor(num) {
  while (this.length < num.length)
    this.words[this.length++] = 0;

  for (var i = 0; i < num.length; i++)
    this.words[i] = this.words[i] | num.words[i];

  return this.strip();
};

BN.prototype.ior = function ior(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuor(num);
};


// Or `num` with `this`
BN.prototype.or = function or(num) {
  if (this.length > num.length)
    return this.clone().ior(num);
  else
    return num.clone().ior(this);
};

BN.prototype.uor = function uor(num) {
  if (this.length > num.length)
    return this.clone().iuor(num);
  else
    return num.clone().iuor(this);
};


// And `num` with `this` in-place
BN.prototype.iuand = function iuand(num) {
  // b = min-length(num, this)
  var b;
  if (this.length > num.length)
    b = num;
  else
    b = this;

  for (var i = 0; i < b.length; i++)
    this.words[i] = this.words[i] & num.words[i];

  this.length = b.length;

  return this.strip();
};

BN.prototype.iand = function iand(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuand(num);
};


// And `num` with `this`
BN.prototype.and = function and(num) {
  if (this.length > num.length)
    return this.clone().iand(num);
  else
    return num.clone().iand(this);
};

BN.prototype.uand = function uand(num) {
  if (this.length > num.length)
    return this.clone().iuand(num);
  else
    return num.clone().iuand(this);
};


// Xor `num` with `this` in-place
BN.prototype.iuxor = function iuxor(num) {
  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  for (var i = 0; i < b.length; i++)
    this.words[i] = a.words[i] ^ b.words[i];

  if (this !== a)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];

  this.length = a.length;

  return this.strip();
};

BN.prototype.ixor = function ixor(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuxor(num);
};


// Xor `num` with `this`
BN.prototype.xor = function xor(num) {
  if (this.length > num.length)
    return this.clone().ixor(num);
  else
    return num.clone().ixor(this);
};

BN.prototype.uxor = function uxor(num) {
  if (this.length > num.length)
    return this.clone().iuxor(num);
  else
    return num.clone().iuxor(this);
};


// Add `num` to `this` in-place
BN.prototype.iadd = function iadd(num) {
  // negative + positive
  if (this.negative !== 0 && num.negative === 0) {
    this.negative = 0;
    var r = this.isub(num);
    this.negative ^= 1;
    return this._normSign();

  // positive + negative
  } else if (this.negative === 0 && num.negative !== 0) {
    num.negative = 0;
    var r = this.isub(num);
    num.negative = 1;
    return r._normSign();
  }

  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) + (b.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }

  this.length = a.length;
  if (carry !== 0) {
    this.words[this.length] = carry;
    this.length++;
  // Copy the rest of the words
  } else if (a !== this) {
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  }

  return this;
};

// Add `num` to `this`
BN.prototype.add = function add(num) {
  if (num.negative !== 0 && this.negative === 0) {
    num.negative = 0;
    var res = this.sub(num);
    num.negative ^= 1;
    return res;
  } else if (num.negative === 0 && this.negative !== 0) {
    this.negative = 0;
    var res = num.sub(this);
    this.negative = 1;
    return res;
  }

  if (this.length > num.length)
    return this.clone().iadd(num);
  else
    return num.clone().iadd(this);
};

// Subtract `num` from `this` in-place
BN.prototype.isub = function isub(num) {
  // this - (-num) = this + num
  if (num.negative !== 0) {
    num.negative = 0;
    var r = this.iadd(num);
    num.negative = 1;
    return r._normSign();

  // -this - num = -(this + num)
  } else if (this.negative !== 0) {
    this.negative = 0;
    this.iadd(num);
    this.negative = 1;
    return this._normSign();
  }

  // At this point both numbers are positive
  var cmp = this.cmp(num);

  // Optimization - zeroify
  if (cmp === 0) {
    this.negative = 0;
    this.length = 1;
    this.words[0] = 0;
    return this;
  }

  // a > b
  var a;
  var b;
  if (cmp > 0) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) - (b.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }

  // Copy rest of the words
  if (carry === 0 && i < a.length && a !== this)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  this.length = Math.max(this.length, i);

  if (a !== this)
    this.negative = 1;

  return this.strip();
};

// Subtract `num` from `this`
BN.prototype.sub = function sub(num) {
  return this.clone().isub(num);
};

function smallMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  var len = (self.length + num.length) | 0;
  out.length = len;
  len = (len - 1) | 0;

  // Peel one iteration (compiler can't do it, because of code complexity)
  var a = self.words[0] | 0;
  var b = num.words[0] | 0;
  var r = a * b;

  var lo = r & 0x3ffffff;
  var carry = (r / 0x4000000) | 0;
  out.words[0] = lo;

  for (var k = 1; k < len; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = carry >>> 26;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = (k - j) | 0;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;
    }
    out.words[k] = rword | 0;
    carry = ncarry | 0;
  }
  if (carry !== 0) {
    out.words[k] = carry | 0;
  } else {
    out.length--;
  }

  return out.strip();
}

function bigMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  out.length = self.length + num.length;

  var carry = 0;
  var hncarry = 0;
  for (var k = 0; k < out.length - 1; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = hncarry;
    hncarry = 0;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;

      hncarry += ncarry >>> 26;
      ncarry &= 0x3ffffff;
    }
    out.words[k] = rword;
    carry = ncarry;
    ncarry = hncarry;
  }
  if (carry !== 0) {
    out.words[k] = carry;
  } else {
    out.length--;
  }

  return out.strip();
}

BN.prototype.mulTo = function mulTo(num, out) {
  var res;
  if (this.length + num.length < 63)
    res = smallMulTo(this, num, out);
  else
    res = bigMulTo(this, num, out);
  return res;
};

// Multiply `this` by `num`
BN.prototype.mul = function mul(num) {
  var out = new BN(null);
  out.words = new Array(this.length + num.length);
  return this.mulTo(num, out);
};

// In-place Multiplication
BN.prototype.imul = function imul(num) {
  if (this.cmpn(0) === 0 || num.cmpn(0) === 0) {
    this.words[0] = 0;
    this.length = 1;
    return this;
  }

  var tlen = this.length;
  var nlen = num.length;

  this.negative = num.negative ^ this.negative;
  this.length = this.length + num.length;
  this.words[this.length - 1] = 0;

  for (var k = this.length - 2; k >= 0; k--) {
    // Sum all words with the same `i + j = k` and accumulate `carry`,
    // note that carry could be >= 0x3ffffff
    var carry = 0;
    var rword = 0;
    var maxJ = Math.min(k, nlen - 1);
    for (var j = Math.max(0, k - tlen + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = this.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      carry += (r / 0x4000000) | 0;
      lo += rword;
      rword = lo & 0x3ffffff;
      carry += lo >>> 26;
    }
    this.words[k] = rword;
    this.words[k + 1] += carry;
    carry = 0;
  }

  // Propagate overflows
  var carry = 0;
  for (var i = 1; i < this.length; i++) {
    var w = (this.words[i] | 0) + carry;
    this.words[i] = w & 0x3ffffff;
    carry = w >>> 26;
  }

  return this.strip();
};

BN.prototype.imuln = function imuln(num) {
  // Carry
  var carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = (this.words[i] | 0) * num;
    var lo = (w & 0x3ffffff) + (carry & 0x3ffffff);
    carry >>= 26;
    carry += (w / 0x4000000) | 0;
    // NOTE: lo is 27bit maximum
    carry += lo >>> 26;
    this.words[i] = lo & 0x3ffffff;
  }

  if (carry !== 0) {
    this.words[i] = carry;
    this.length++;
  }

  return this;
};

BN.prototype.muln = function muln(num) {
  return this.clone().imuln(num);
};

// `this` * `this`
BN.prototype.sqr = function sqr() {
  return this.mul(this);
};

// `this` * `this` in-place
BN.prototype.isqr = function isqr() {
  return this.mul(this);
};

// Shift-left in-place
BN.prototype.iushln = function iushln(bits) {
  var r = bits % 26;
  var s = (bits - r) / 26;
  var carryMask = (0x3ffffff >>> (26 - r)) << (26 - r);

  if (r !== 0) {
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var newCarry = this.words[i] & carryMask;
      var c = ((this.words[i] | 0) - newCarry) << r;
      this.words[i] = c | carry;
      carry = newCarry >>> (26 - r);
    }
    if (carry) {
      this.words[i] = carry;
      this.length++;
    }
  }

  if (s !== 0) {
    for (var i = this.length - 1; i >= 0; i--)
      this.words[i + s] = this.words[i];
    for (var i = 0; i < s; i++)
      this.words[i] = 0;
    this.length += s;
  }

  return this.strip();
};

BN.prototype.ishln = function ishln(bits) {
  return this.iushln(bits);
};

// Shift-right in-place
BN.prototype.iushrn = function iushrn(bits, hint, extended) {
  var h;
  if (hint)
    h = (hint - (hint % 26)) / 26;
  else
    h = 0;

  var r = bits % 26;
  var s = Math.min((bits - r) / 26, this.length);
  var mask = 0x3ffffff ^ ((0x3ffffff >>> r) << r);
  var maskedWords = extended;

  h -= s;
  h = Math.max(0, h);

  // Extended mode, copy masked part
  if (maskedWords) {
    for (var i = 0; i < s; i++)
      maskedWords.words[i] = this.words[i];
    maskedWords.length = s;
  }

  if (s === 0) {
    // No-op, we should not move anything at all
  } else if (this.length > s) {
    this.length -= s;
    for (var i = 0; i < this.length; i++)
      this.words[i] = this.words[i + s];
  } else {
    this.words[0] = 0;
    this.length = 1;
  }

  var carry = 0;
  for (var i = this.length - 1; i >= 0 && (carry !== 0 || i >= h); i--) {
    var word = this.words[i] | 0;
    this.words[i] = (carry << (26 - r)) | (word >>> r);
    carry = word & mask;
  }

  // Push carried bits as a mask
  if (maskedWords && carry !== 0)
    maskedWords.words[maskedWords.length++] = carry;

  if (this.length === 0) {
    this.words[0] = 0;
    this.length = 1;
  }

  this.strip();

  return this;
};

BN.prototype.ishrn = function ishrn(bits, hint, extended) {
  return this.iushrn(bits, hint, extended);
};

// Shift-left
BN.prototype.shln = function shln(bits) {
  var x = this.clone();
  var neg = x.negative;
  x.negative = false;
  x.ishln(bits);
  x.negative = neg;
  return x;
};

BN.prototype.ushln = function ushln(bits) {
  return this.clone().iushln(bits);
};

// Shift-right
BN.prototype.shrn = function shrn(bits) {
  var x = this.clone();
  if(x.negative) {
      x.negative = false;
      x.ishrn(bits);
      x.negative = true;
      return x.isubn(1);
  } else {
      return x.ishrn(bits);
  }
};

BN.prototype.ushrn = function ushrn(bits) {
  return this.clone().iushrn(bits);
};

// Test if n bit is set
BN.prototype.testn = function testn(bit) {
  var r = bit % 26;
  var s = (bit - r) / 26;
  var q = 1 << r;

  // Fast case: bit is much higher than all existing words
  if (this.length <= s) {
    return false;
  }

  // Check bit and return
  var w = this.words[s];

  return !!(w & q);
};

// Add plain number `num` to `this`
BN.prototype.iaddn = function iaddn(num) {
  if (num < 0)
    return this.isubn(-num);

  // Possible sign change
  if (this.negative !== 0) {
    if (this.length === 1 && (this.words[0] | 0) < num) {
      this.words[0] = num - (this.words[0] | 0);
      this.negative = 0;
      return this;
    }

    this.negative = 0;
    this.isubn(num);
    this.negative = 1;
    return this;
  }

  // Add without checks
  return this._iaddn(num);
};

BN.prototype._iaddn = function _iaddn(num) {
  this.words[0] += num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] >= 0x4000000; i++) {
    this.words[i] -= 0x4000000;
    if (i === this.length - 1)
      this.words[i + 1] = 1;
    else
      this.words[i + 1]++;
  }
  this.length = Math.max(this.length, i + 1);

  return this;
};

// Subtract plain number `num` from `this`
BN.prototype.isubn = function isubn(num) {
  if (num < 0)
    return this.iaddn(-num);

  if (this.negative !== 0) {
    this.negative = 0;
    this.iaddn(num);
    this.negative = 1;
    return this;
  }

  this.words[0] -= num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] < 0; i++) {
    this.words[i] += 0x4000000;
    this.words[i + 1] -= 1;
  }

  return this.strip();
};

BN.prototype.addn = function addn(num) {
  return this.clone().iaddn(num);
};

BN.prototype.subn = function subn(num) {
  return this.clone().isubn(num);
};

BN.prototype.iabs = function iabs() {
  this.negative = 0;

  return this;
};

BN.prototype.abs = function abs() {
  return this.clone().iabs();
};

BN.prototype._ishlnsubmul = function _ishlnsubmul(num, mul, shift) {
  // Bigger storage is needed
  var len = num.length + shift;
  var i;
  if (this.words.length < len) {
    var t = new Array(len);
    for (var i = 0; i < this.length; i++)
      t[i] = this.words[i];
    this.words = t;
  } else {
    i = this.length;
  }

  // Zeroify rest
  this.length = Math.max(this.length, len);
  for (; i < this.length; i++)
    this.words[i] = 0;

  var carry = 0;
  for (var i = 0; i < num.length; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    var right = (num.words[i] | 0) * mul;
    w -= right & 0x3ffffff;
    carry = (w >> 26) - ((right / 0x4000000) | 0);
    this.words[i + shift] = w & 0x3ffffff;
  }
  for (; i < this.length - shift; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    carry = w >> 26;
    this.words[i + shift] = w & 0x3ffffff;
  }

  if (carry === 0)
    return this.strip();

  carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = -(this.words[i] | 0) + carry;
    carry = w >> 26;
    this.words[i] = w & 0x3ffffff;
  }
  this.negative = 1;

  return this.strip();
};

BN.prototype._wordDiv = function _wordDiv(num, mode) {
  var shift = this.length - num.length;

  var a = this.clone();
  var b = num;

  // Normalize
  var bhi = b.words[b.length - 1] | 0;
  var bhiBits = this._countBits(bhi);
  shift = 26 - bhiBits;
  if (shift !== 0) {
    b = b.ushln(shift);
    a.iushln(shift);
    bhi = b.words[b.length - 1] | 0;
  }

  // Initialize quotient
  var m = a.length - b.length;
  var q;

  if (mode !== 'mod') {
    q = new BN(null);
    q.length = m + 1;
    q.words = new Array(q.length);
    for (var i = 0; i < q.length; i++)
      q.words[i] = 0;
  }

  var diff = a.clone()._ishlnsubmul(b, 1, m);
  if (diff.negative === 0) {
    a = diff;
    if (q)
      q.words[m] = 1;
  }

  for (var j = m - 1; j >= 0; j--) {
    var qj = (a.words[b.length + j] | 0) * 0x4000000 +
             (a.words[b.length + j - 1] | 0);

    // NOTE: (qj / bhi) is (0x3ffffff * 0x4000000 + 0x3ffffff) / 0x2000000 max
    // (0x7ffffff)
    qj = Math.min((qj / bhi) | 0, 0x3ffffff);

    a._ishlnsubmul(b, qj, j);
    while (a.negative !== 0) {
      qj--;
      a.negative = 0;
      a._ishlnsubmul(b, 1, j);
      if (a.cmpn(0) !== 0)
        a.negative ^= 1;
    }
    if (q)
      q.words[j] = qj;
  }
  if (q)
    q.strip();
  a.strip();

  // Denormalize
  if (mode !== 'div' && shift !== 0)
    a.iushrn(shift);
  return { div: q ? q : null, mod: a };
};

BN.prototype.divmod = function divmod(num, mode, positive) {
  if (this.negative !== 0 && num.negative === 0) {
    var res = this.neg().divmod(num, mode);
    var div;
    var mod;
    if (mode !== 'mod')
      div = res.div.neg();
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.add(num);
    }
    return {
      div: div,
      mod: mod
    };
  } else if (this.negative === 0 && num.negative !== 0) {
    var res = this.divmod(num.neg(), mode);
    var div;
    if (mode !== 'mod')
      div = res.div.neg();
    return { div: div, mod: res.mod };
  } else if ((this.negative & num.negative) !== 0) {
    var res = this.neg().divmod(num.neg(), mode);
    var mod;
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.isub(num);
    }
    return {
      div: res.div,
      mod: mod
    };
  }

  // Both numbers are positive at this point

  // Strip both numbers to approximate shift value
  if (num.length > this.length || this.cmp(num) < 0)
    return { div: new BN(0), mod: this };

  // Very short reduction
  if (num.length === 1) {
    if (mode === 'div')
      return { div: this.divn(num.words[0]), mod: null };
    else if (mode === 'mod')
      return { div: null, mod: new BN(this.modn(num.words[0])) };
    return {
      div: this.divn(num.words[0]),
      mod: new BN(this.modn(num.words[0]))
    };
  }

  return this._wordDiv(num, mode);
};

// Find `this` / `num`
BN.prototype.div = function div(num) {
  return this.divmod(num, 'div', false).div;
};

// Find `this` % `num`
BN.prototype.mod = function mod(num) {
  return this.divmod(num, 'mod', false).mod;
};

BN.prototype.umod = function umod(num) {
  return this.divmod(num, 'mod', true).mod;
};

// Find Round(`this` / `num`)
BN.prototype.divRound = function divRound(num) {
  var dm = this.divmod(num);

  // Fast case - exact division
  if (dm.mod.cmpn(0) === 0)
    return dm.div;

  var mod = dm.div.negative !== 0 ? dm.mod.isub(num) : dm.mod;

  var half = num.ushrn(1);
  var r2 = num.andln(1);
  var cmp = mod.cmp(half);

  // Round down
  if (cmp < 0 || r2 === 1 && cmp === 0)
    return dm.div;

  // Round up
  return dm.div.negative !== 0 ? dm.div.isubn(1) : dm.div.iaddn(1);
};

BN.prototype.modn = function modn(num) {
  var p = (1 << 26) % num;

  var acc = 0;
  for (var i = this.length - 1; i >= 0; i--)
    acc = (p * acc + (this.words[i] | 0)) % num;

  return acc;
};

// In-place division by number
BN.prototype.idivn = function idivn(num) {
  var carry = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var w = (this.words[i] | 0) + carry * 0x4000000;
    this.words[i] = (w / num) | 0;
    carry = w % num;
  }

  return this.strip();
};

BN.prototype.divn = function divn(num) {
  return this.clone().idivn(num);
};

BN.prototype.isEven = function isEven() {
  return (this.words[0] & 1) === 0;
};

BN.prototype.isOdd = function isOdd() {
  return (this.words[0] & 1) === 1;
};

// And first word and num
BN.prototype.andln = function andln(num) {
  return this.words[0] & num;
};

BN.prototype.cmpn = function cmpn(num) {
  var negative = num < 0;
  if (negative)
    num = -num;

  if (this.negative !== 0 && !negative)
    return -1;
  else if (this.negative === 0 && negative)
    return 1;

  num &= 0x3ffffff;
  this.strip();

  var res;
  if (this.length > 1) {
    res = 1;
  } else {
    var w = this.words[0] | 0;
    res = w === num ? 0 : w < num ? -1 : 1;
  }
  if (this.negative !== 0)
    res = -res;
  return res;
};

// Compare two numbers and return:
// 1 - if `this` > `num`
// 0 - if `this` == `num`
// -1 - if `this` < `num`
BN.prototype.cmp = function cmp(num) {
  if (this.negative !== 0 && num.negative === 0)
    return -1;
  else if (this.negative === 0 && num.negative !== 0)
    return 1;

  var res = this.ucmp(num);
  if (this.negative !== 0)
    return -res;
  else
    return res;
};

// Unsigned comparison
BN.prototype.ucmp = function ucmp(num) {
  // At this point both numbers have the same sign
  if (this.length > num.length)
    return 1;
  else if (this.length < num.length)
    return -1;

  var res = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var a = this.words[i] | 0;
    var b = num.words[i] | 0;

    if (a === b)
      continue;
    if (a < b)
      res = -1;
    else if (a > b)
      res = 1;
    break;
  }
  return res;
};
})(undefined, __bn);

// MVar implementation.
// Since Haste isn't concurrent, takeMVar and putMVar don't block on empty
// and full MVars respectively, but terminate the program since they would
// otherwise be blocking forever.

function newMVar() {
    return ({empty: true});
}

function tryTakeMVar(mv) {
    if(mv.empty) {
        return {_:0, a:0, b:undefined};
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return {_:0, a:1, b:val};
    }
}

function takeMVar(mv) {
    if(mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to take empty MVar!");
    }
    var val = mv.x;
    mv.empty = true;
    mv.x = null;
    return val;
}

function putMVar(mv, val) {
    if(!mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to put full MVar!");
    }
    mv.empty = false;
    mv.x = val;
}

function tryPutMVar(mv, val) {
    if(!mv.empty) {
        return 0;
    } else {
        mv.empty = false;
        mv.x = val;
        return 1;
    }
}

function sameMVar(a, b) {
    return (a == b);
}

function isEmptyMVar(mv) {
    return mv.empty ? 1 : 0;
}

// Implementation of stable names.
// Unlike native GHC, the garbage collector isn't going to move data around
// in a way that we can detect, so each object could serve as its own stable
// name if it weren't for the fact we can't turn a JS reference into an
// integer.
// So instead, each object has a unique integer attached to it, which serves
// as its stable name.

var __next_stable_name = 1;
var __stable_table;

function makeStableName(x) {
    if(x instanceof Object) {
        if(!x.stableName) {
            x.stableName = __next_stable_name;
            __next_stable_name += 1;
        }
        return {type: 'obj', name: x.stableName};
    } else {
        return {type: 'prim', name: Number(x)};
    }
}

function eqStableName(x, y) {
    return (x.type == y.type && x.name == y.name) ? 1 : 0;
}

// TODO: inefficient compared to real fromInt?
__bn.Z = new __bn.BN(0);
__bn.ONE = new __bn.BN(1);
__bn.MOD32 = new __bn.BN(0x100000000); // 2^32
var I_fromNumber = function(x) {return new __bn.BN(x);}
var I_fromInt = I_fromNumber;
var I_fromBits = function(lo,hi) {
    var x = new __bn.BN(lo >>> 0);
    var y = new __bn.BN(hi >>> 0);
    y.ishln(32);
    x.iadd(y);
    return x;
}
var I_fromString = function(s) {return new __bn.BN(s);}
var I_toInt = function(x) {return I_toNumber(x.mod(__bn.MOD32));}
var I_toWord = function(x) {return I_toInt(x) >>> 0;};
// TODO: inefficient!
var I_toNumber = function(x) {return Number(x.toString());}
var I_equals = function(a,b) {return a.cmp(b) === 0;}
var I_compare = function(a,b) {return a.cmp(b);}
var I_compareInt = function(x,i) {return x.cmp(new __bn.BN(i));}
var I_negate = function(x) {return x.neg();}
var I_add = function(a,b) {return a.add(b);}
var I_sub = function(a,b) {return a.sub(b);}
var I_mul = function(a,b) {return a.mul(b);}
var I_mod = function(a,b) {return I_rem(I_add(b, I_rem(a, b)), b);}
var I_quotRem = function(a,b) {
    var qr = a.divmod(b);
    return {_:0, a:qr.div, b:qr.mod};
}
var I_div = function(a,b) {
    if((a.cmp(__bn.Z)>=0) != (a.cmp(__bn.Z)>=0)) {
        if(a.cmp(a.rem(b), __bn.Z) !== 0) {
            return a.div(b).sub(__bn.ONE);
        }
    }
    return a.div(b);
}
var I_divMod = function(a,b) {
    return {_:0, a:I_div(a,b), b:a.mod(b)};
}
var I_quot = function(a,b) {return a.div(b);}
var I_rem = function(a,b) {return a.mod(b);}
var I_and = function(a,b) {return a.and(b);}
var I_or = function(a,b) {return a.or(b);}
var I_xor = function(a,b) {return a.xor(b);}
var I_shiftLeft = function(a,b) {return a.shln(b);}
var I_shiftRight = function(a,b) {return a.shrn(b);}
var I_signum = function(x) {return x.cmp(new __bn.BN(0));}
var I_abs = function(x) {return x.abs();}
var I_decodeDouble = function(x) {
    var dec = decodeDouble(x);
    var mantissa = I_fromBits(dec.c, dec.b);
    if(dec.a < 0) {
        mantissa = I_negate(mantissa);
    }
    return {_:0, a:dec.d, b:mantissa};
}
var I_toString = function(x) {return x.toString();}
var I_fromRat = function(a, b) {
    return I_toNumber(a) / I_toNumber(b);
}

function I_fromInt64(x) {
    if(x.isNegative()) {
        return I_negate(I_fromInt64(x.negate()));
    } else {
        return I_fromBits(x.low, x.high);
    }
}

function I_toInt64(x) {
    if(x.negative) {
        return I_toInt64(I_negate(x)).negate();
    } else {
        return new Long(I_toInt(x), I_toInt(I_shiftRight(x,32)));
    }
}

function I_fromWord64(x) {
    return I_fromBits(x.toInt(), x.shru(32).toInt());
}

function I_toWord64(x) {
    var w = I_toInt64(x);
    w.unsigned = true;
    return w;
}

/**
 * @license long.js (c) 2013 Daniel Wirtz <dcode@dcode.io>
 * Released under the Apache License, Version 2.0
 * see: https://github.com/dcodeIO/long.js for details
 */
function Long(low, high, unsigned) {
    this.low = low | 0;
    this.high = high | 0;
    this.unsigned = !!unsigned;
}

var INT_CACHE = {};
var UINT_CACHE = {};
function cacheable(x, u) {
    return u ? 0 <= (x >>>= 0) && x < 256 : -128 <= (x |= 0) && x < 128;
}

function __fromInt(value, unsigned) {
    var obj, cachedObj, cache;
    if (unsigned) {
        if (cache = cacheable(value >>>= 0, true)) {
            cachedObj = UINT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, (value | 0) < 0 ? -1 : 0, true);
        if (cache)
            UINT_CACHE[value] = obj;
        return obj;
    } else {
        if (cache = cacheable(value |= 0, false)) {
            cachedObj = INT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, value < 0 ? -1 : 0, false);
        if (cache)
            INT_CACHE[value] = obj;
        return obj;
    }
}

function __fromNumber(value, unsigned) {
    if (isNaN(value) || !isFinite(value))
        return unsigned ? UZERO : ZERO;
    if (unsigned) {
        if (value < 0)
            return UZERO;
        if (value >= TWO_PWR_64_DBL)
            return MAX_UNSIGNED_VALUE;
    } else {
        if (value <= -TWO_PWR_63_DBL)
            return MIN_VALUE;
        if (value + 1 >= TWO_PWR_63_DBL)
            return MAX_VALUE;
    }
    if (value < 0)
        return __fromNumber(-value, unsigned).neg();
    return new Long((value % TWO_PWR_32_DBL) | 0, (value / TWO_PWR_32_DBL) | 0, unsigned);
}
var pow_dbl = Math.pow;
var TWO_PWR_16_DBL = 1 << 16;
var TWO_PWR_24_DBL = 1 << 24;
var TWO_PWR_32_DBL = TWO_PWR_16_DBL * TWO_PWR_16_DBL;
var TWO_PWR_64_DBL = TWO_PWR_32_DBL * TWO_PWR_32_DBL;
var TWO_PWR_63_DBL = TWO_PWR_64_DBL / 2;
var TWO_PWR_24 = __fromInt(TWO_PWR_24_DBL);
var ZERO = __fromInt(0);
Long.ZERO = ZERO;
var UZERO = __fromInt(0, true);
Long.UZERO = UZERO;
var ONE = __fromInt(1);
Long.ONE = ONE;
var UONE = __fromInt(1, true);
Long.UONE = UONE;
var NEG_ONE = __fromInt(-1);
Long.NEG_ONE = NEG_ONE;
var MAX_VALUE = new Long(0xFFFFFFFF|0, 0x7FFFFFFF|0, false);
Long.MAX_VALUE = MAX_VALUE;
var MAX_UNSIGNED_VALUE = new Long(0xFFFFFFFF|0, 0xFFFFFFFF|0, true);
Long.MAX_UNSIGNED_VALUE = MAX_UNSIGNED_VALUE;
var MIN_VALUE = new Long(0, 0x80000000|0, false);
Long.MIN_VALUE = MIN_VALUE;
var __lp = Long.prototype;
__lp.toInt = function() {return this.unsigned ? this.low >>> 0 : this.low;};
__lp.toNumber = function() {
    if (this.unsigned)
        return ((this.high >>> 0) * TWO_PWR_32_DBL) + (this.low >>> 0);
    return this.high * TWO_PWR_32_DBL + (this.low >>> 0);
};
__lp.isZero = function() {return this.high === 0 && this.low === 0;};
__lp.isNegative = function() {return !this.unsigned && this.high < 0;};
__lp.isOdd = function() {return (this.low & 1) === 1;};
__lp.eq = function(other) {
    if (this.unsigned !== other.unsigned && (this.high >>> 31) === 1 && (other.high >>> 31) === 1)
        return false;
    return this.high === other.high && this.low === other.low;
};
__lp.neq = function(other) {return !this.eq(other);};
__lp.lt = function(other) {return this.comp(other) < 0;};
__lp.lte = function(other) {return this.comp(other) <= 0;};
__lp.gt = function(other) {return this.comp(other) > 0;};
__lp.gte = function(other) {return this.comp(other) >= 0;};
__lp.compare = function(other) {
    if (this.eq(other))
        return 0;
    var thisNeg = this.isNegative(),
        otherNeg = other.isNegative();
    if (thisNeg && !otherNeg)
        return -1;
    if (!thisNeg && otherNeg)
        return 1;
    if (!this.unsigned)
        return this.sub(other).isNegative() ? -1 : 1;
    return (other.high >>> 0) > (this.high >>> 0) || (other.high === this.high && (other.low >>> 0) > (this.low >>> 0)) ? -1 : 1;
};
__lp.comp = __lp.compare;
__lp.negate = function() {
    if (!this.unsigned && this.eq(MIN_VALUE))
        return MIN_VALUE;
    return this.not().add(ONE);
};
__lp.neg = __lp.negate;
__lp.add = function(addend) {
    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = addend.high >>> 16;
    var b32 = addend.high & 0xFFFF;
    var b16 = addend.low >>> 16;
    var b00 = addend.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 + b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 + b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 + b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 + b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.subtract = function(subtrahend) {return this.add(subtrahend.neg());};
__lp.sub = __lp.subtract;
__lp.multiply = function(multiplier) {
    if (this.isZero())
        return ZERO;
    if (multiplier.isZero())
        return ZERO;
    if (this.eq(MIN_VALUE))
        return multiplier.isOdd() ? MIN_VALUE : ZERO;
    if (multiplier.eq(MIN_VALUE))
        return this.isOdd() ? MIN_VALUE : ZERO;

    if (this.isNegative()) {
        if (multiplier.isNegative())
            return this.neg().mul(multiplier.neg());
        else
            return this.neg().mul(multiplier).neg();
    } else if (multiplier.isNegative())
        return this.mul(multiplier.neg()).neg();

    if (this.lt(TWO_PWR_24) && multiplier.lt(TWO_PWR_24))
        return __fromNumber(this.toNumber() * multiplier.toNumber(), this.unsigned);

    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = multiplier.high >>> 16;
    var b32 = multiplier.high & 0xFFFF;
    var b16 = multiplier.low >>> 16;
    var b00 = multiplier.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 * b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 * b00;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c16 += a00 * b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 * b00;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a16 * b16;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a00 * b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.mul = __lp.multiply;
__lp.divide = function(divisor) {
    if (divisor.isZero())
        throw Error('division by zero');
    if (this.isZero())
        return this.unsigned ? UZERO : ZERO;
    var approx, rem, res;
    if (this.eq(MIN_VALUE)) {
        if (divisor.eq(ONE) || divisor.eq(NEG_ONE))
            return MIN_VALUE;
        else if (divisor.eq(MIN_VALUE))
            return ONE;
        else {
            var halfThis = this.shr(1);
            approx = halfThis.div(divisor).shl(1);
            if (approx.eq(ZERO)) {
                return divisor.isNegative() ? ONE : NEG_ONE;
            } else {
                rem = this.sub(divisor.mul(approx));
                res = approx.add(rem.div(divisor));
                return res;
            }
        }
    } else if (divisor.eq(MIN_VALUE))
        return this.unsigned ? UZERO : ZERO;
    if (this.isNegative()) {
        if (divisor.isNegative())
            return this.neg().div(divisor.neg());
        return this.neg().div(divisor).neg();
    } else if (divisor.isNegative())
        return this.div(divisor.neg()).neg();

    res = ZERO;
    rem = this;
    while (rem.gte(divisor)) {
        approx = Math.max(1, Math.floor(rem.toNumber() / divisor.toNumber()));
        var log2 = Math.ceil(Math.log(approx) / Math.LN2),
            delta = (log2 <= 48) ? 1 : pow_dbl(2, log2 - 48),
            approxRes = __fromNumber(approx),
            approxRem = approxRes.mul(divisor);
        while (approxRem.isNegative() || approxRem.gt(rem)) {
            approx -= delta;
            approxRes = __fromNumber(approx, this.unsigned);
            approxRem = approxRes.mul(divisor);
        }
        if (approxRes.isZero())
            approxRes = ONE;

        res = res.add(approxRes);
        rem = rem.sub(approxRem);
    }
    return res;
};
__lp.div = __lp.divide;
__lp.modulo = function(divisor) {return this.sub(this.div(divisor).mul(divisor));};
__lp.mod = __lp.modulo;
__lp.not = function not() {return new Long(~this.low, ~this.high, this.unsigned);};
__lp.and = function(other) {return new Long(this.low & other.low, this.high & other.high, this.unsigned);};
__lp.or = function(other) {return new Long(this.low | other.low, this.high | other.high, this.unsigned);};
__lp.xor = function(other) {return new Long(this.low ^ other.low, this.high ^ other.high, this.unsigned);};

__lp.shl = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long(this.low << numBits, (this.high << numBits) | (this.low >>> (32 - numBits)), this.unsigned);
    else
        return new Long(0, this.low << (numBits - 32), this.unsigned);
};

__lp.shr = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long((this.low >>> numBits) | (this.high << (32 - numBits)), this.high >> numBits, this.unsigned);
    else
        return new Long(this.high >> (numBits - 32), this.high >= 0 ? 0 : -1, this.unsigned);
};

__lp.shru = function(numBits) {
    numBits &= 63;
    if (numBits === 0)
        return this;
    else {
        var high = this.high;
        if (numBits < 32) {
            var low = this.low;
            return new Long((low >>> numBits) | (high << (32 - numBits)), high >>> numBits, this.unsigned);
        } else if (numBits === 32)
            return new Long(high, 0, this.unsigned);
        else
            return new Long(high >>> (numBits - 32), 0, this.unsigned);
    }
};

__lp.toSigned = function() {return this.unsigned ? new Long(this.low, this.high, false) : this;};
__lp.toUnsigned = function() {return this.unsigned ? this : new Long(this.low, this.high, true);};

// Int64
function hs_eqInt64(x, y) {return x.eq(y);}
function hs_neInt64(x, y) {return x.neq(y);}
function hs_ltInt64(x, y) {return x.lt(y);}
function hs_leInt64(x, y) {return x.lte(y);}
function hs_gtInt64(x, y) {return x.gt(y);}
function hs_geInt64(x, y) {return x.gte(y);}
function hs_quotInt64(x, y) {return x.div(y);}
function hs_remInt64(x, y) {return x.modulo(y);}
function hs_plusInt64(x, y) {return x.add(y);}
function hs_minusInt64(x, y) {return x.subtract(y);}
function hs_timesInt64(x, y) {return x.multiply(y);}
function hs_negateInt64(x) {return x.negate();}
function hs_uncheckedIShiftL64(x, bits) {return x.shl(bits);}
function hs_uncheckedIShiftRA64(x, bits) {return x.shr(bits);}
function hs_uncheckedIShiftRL64(x, bits) {return x.shru(bits);}
function hs_int64ToInt(x) {return x.toInt();}
var hs_intToInt64 = __fromInt;

// Word64
function hs_wordToWord64(x) {return __fromInt(x, true);}
function hs_word64ToWord(x) {return x.toInt(x);}
function hs_mkWord64(low, high) {return new Long(low,high,true);}
function hs_and64(a,b) {return a.and(b);};
function hs_or64(a,b) {return a.or(b);};
function hs_xor64(a,b) {return a.xor(b);};
function hs_not64(x) {return x.not();}
var hs_eqWord64 = hs_eqInt64;
var hs_neWord64 = hs_neInt64;
var hs_ltWord64 = hs_ltInt64;
var hs_leWord64 = hs_leInt64;
var hs_gtWord64 = hs_gtInt64;
var hs_geWord64 = hs_geInt64;
var hs_quotWord64 = hs_quotInt64;
var hs_remWord64 = hs_remInt64;
var hs_uncheckedShiftL64 = hs_uncheckedIShiftL64;
var hs_uncheckedShiftRL64 = hs_uncheckedIShiftRL64;
function hs_int64ToWord64(x) {return x.toUnsigned();}
function hs_word64ToInt64(x) {return x.toSigned();}

// Joseph Myers' MD5 implementation, ported to work on typed arrays.
// Used under the BSD license.
function md5cycle(x, k) {
    var a = x[0], b = x[1], c = x[2], d = x[3];

    a = ff(a, b, c, d, k[0], 7, -680876936);
    d = ff(d, a, b, c, k[1], 12, -389564586);
    c = ff(c, d, a, b, k[2], 17,  606105819);
    b = ff(b, c, d, a, k[3], 22, -1044525330);
    a = ff(a, b, c, d, k[4], 7, -176418897);
    d = ff(d, a, b, c, k[5], 12,  1200080426);
    c = ff(c, d, a, b, k[6], 17, -1473231341);
    b = ff(b, c, d, a, k[7], 22, -45705983);
    a = ff(a, b, c, d, k[8], 7,  1770035416);
    d = ff(d, a, b, c, k[9], 12, -1958414417);
    c = ff(c, d, a, b, k[10], 17, -42063);
    b = ff(b, c, d, a, k[11], 22, -1990404162);
    a = ff(a, b, c, d, k[12], 7,  1804603682);
    d = ff(d, a, b, c, k[13], 12, -40341101);
    c = ff(c, d, a, b, k[14], 17, -1502002290);
    b = ff(b, c, d, a, k[15], 22,  1236535329);

    a = gg(a, b, c, d, k[1], 5, -165796510);
    d = gg(d, a, b, c, k[6], 9, -1069501632);
    c = gg(c, d, a, b, k[11], 14,  643717713);
    b = gg(b, c, d, a, k[0], 20, -373897302);
    a = gg(a, b, c, d, k[5], 5, -701558691);
    d = gg(d, a, b, c, k[10], 9,  38016083);
    c = gg(c, d, a, b, k[15], 14, -660478335);
    b = gg(b, c, d, a, k[4], 20, -405537848);
    a = gg(a, b, c, d, k[9], 5,  568446438);
    d = gg(d, a, b, c, k[14], 9, -1019803690);
    c = gg(c, d, a, b, k[3], 14, -187363961);
    b = gg(b, c, d, a, k[8], 20,  1163531501);
    a = gg(a, b, c, d, k[13], 5, -1444681467);
    d = gg(d, a, b, c, k[2], 9, -51403784);
    c = gg(c, d, a, b, k[7], 14,  1735328473);
    b = gg(b, c, d, a, k[12], 20, -1926607734);

    a = hh(a, b, c, d, k[5], 4, -378558);
    d = hh(d, a, b, c, k[8], 11, -2022574463);
    c = hh(c, d, a, b, k[11], 16,  1839030562);
    b = hh(b, c, d, a, k[14], 23, -35309556);
    a = hh(a, b, c, d, k[1], 4, -1530992060);
    d = hh(d, a, b, c, k[4], 11,  1272893353);
    c = hh(c, d, a, b, k[7], 16, -155497632);
    b = hh(b, c, d, a, k[10], 23, -1094730640);
    a = hh(a, b, c, d, k[13], 4,  681279174);
    d = hh(d, a, b, c, k[0], 11, -358537222);
    c = hh(c, d, a, b, k[3], 16, -722521979);
    b = hh(b, c, d, a, k[6], 23,  76029189);
    a = hh(a, b, c, d, k[9], 4, -640364487);
    d = hh(d, a, b, c, k[12], 11, -421815835);
    c = hh(c, d, a, b, k[15], 16,  530742520);
    b = hh(b, c, d, a, k[2], 23, -995338651);

    a = ii(a, b, c, d, k[0], 6, -198630844);
    d = ii(d, a, b, c, k[7], 10,  1126891415);
    c = ii(c, d, a, b, k[14], 15, -1416354905);
    b = ii(b, c, d, a, k[5], 21, -57434055);
    a = ii(a, b, c, d, k[12], 6,  1700485571);
    d = ii(d, a, b, c, k[3], 10, -1894986606);
    c = ii(c, d, a, b, k[10], 15, -1051523);
    b = ii(b, c, d, a, k[1], 21, -2054922799);
    a = ii(a, b, c, d, k[8], 6,  1873313359);
    d = ii(d, a, b, c, k[15], 10, -30611744);
    c = ii(c, d, a, b, k[6], 15, -1560198380);
    b = ii(b, c, d, a, k[13], 21,  1309151649);
    a = ii(a, b, c, d, k[4], 6, -145523070);
    d = ii(d, a, b, c, k[11], 10, -1120210379);
    c = ii(c, d, a, b, k[2], 15,  718787259);
    b = ii(b, c, d, a, k[9], 21, -343485551);

    x[0] = add32(a, x[0]);
    x[1] = add32(b, x[1]);
    x[2] = add32(c, x[2]);
    x[3] = add32(d, x[3]);

}

function cmn(q, a, b, x, s, t) {
    a = add32(add32(a, q), add32(x, t));
    return add32((a << s) | (a >>> (32 - s)), b);
}

function ff(a, b, c, d, x, s, t) {
    return cmn((b & c) | ((~b) & d), a, b, x, s, t);
}

function gg(a, b, c, d, x, s, t) {
    return cmn((b & d) | (c & (~d)), a, b, x, s, t);
}

function hh(a, b, c, d, x, s, t) {
    return cmn(b ^ c ^ d, a, b, x, s, t);
}

function ii(a, b, c, d, x, s, t) {
    return cmn(c ^ (b | (~d)), a, b, x, s, t);
}

function md51(s, n) {
    var a = s['v']['w8'];
    var orig_n = n,
        state = [1732584193, -271733879, -1732584194, 271733878], i;
    for (i=64; i<=n; i+=64) {
        md5cycle(state, md5blk(a.subarray(i-64, i)));
    }
    a = a.subarray(i-64);
    n = n < (i-64) ? 0 : n-(i-64);
    var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
    for (i=0; i<n; i++)
        tail[i>>2] |= a[i] << ((i%4) << 3);
    tail[i>>2] |= 0x80 << ((i%4) << 3);
    if (i > 55) {
        md5cycle(state, tail);
        for (i=0; i<16; i++) tail[i] = 0;
    }
    tail[14] = orig_n*8;
    md5cycle(state, tail);
    return state;
}
window['md51'] = md51;

function md5blk(s) {
    var md5blks = [], i;
    for (i=0; i<64; i+=4) {
        md5blks[i>>2] = s[i]
            + (s[i+1] << 8)
            + (s[i+2] << 16)
            + (s[i+3] << 24);
    }
    return md5blks;
}

var hex_chr = '0123456789abcdef'.split('');

function rhex(n)
{
    var s='', j=0;
    for(; j<4; j++)
        s += hex_chr[(n >> (j * 8 + 4)) & 0x0F]
        + hex_chr[(n >> (j * 8)) & 0x0F];
    return s;
}

function hex(x) {
    for (var i=0; i<x.length; i++)
        x[i] = rhex(x[i]);
    return x.join('');
}

function md5(s, n) {
    return hex(md51(s, n));
}

window['md5'] = md5;

function add32(a, b) {
    return (a + b) & 0xFFFFFFFF;
}

function __hsbase_MD5Init(ctx) {}
// Note that this is a one time "update", since that's all that's used by
// GHC.Fingerprint.
function __hsbase_MD5Update(ctx, s, n) {
    ctx.md5 = md51(s, n);
}
function __hsbase_MD5Final(out, ctx) {
    var a = out['v']['i32'];
    a[0] = ctx.md5[0];
    a[1] = ctx.md5[1];
    a[2] = ctx.md5[2];
    a[3] = ctx.md5[3];
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = new Array(n);
    for(var i = 0; i < n; ++i) {
        arr[i] = x;
    }
    return arr;
}

// Create all views at once; perhaps it's wasteful, but it's better than having
// to check for the right view at each read or write.
function newByteArr(n) {
    // Pad the thing to multiples of 8.
    var padding = 8 - n % 8;
    if(padding < 8) {
        n += padding;
    }
    return new ByteArray(new ArrayBuffer(n));
}

// Wrap a JS ArrayBuffer into a ByteArray. Truncates the array length to the
// closest multiple of 8 bytes.
function wrapByteArr(buffer) {
    var diff = buffer.byteLength % 8;
    if(diff != 0) {
        var buffer = buffer.slice(0, buffer.byteLength-diff);
    }
    return new ByteArray(buffer);
}

function ByteArray(buffer) {
    var views =
        { 'i8' : new Int8Array(buffer)
        , 'i16': new Int16Array(buffer)
        , 'i32': new Int32Array(buffer)
        , 'w8' : new Uint8Array(buffer)
        , 'w16': new Uint16Array(buffer)
        , 'w32': new Uint32Array(buffer)
        , 'f32': new Float32Array(buffer)
        , 'f64': new Float64Array(buffer)
        };
    this['b'] = buffer;
    this['v'] = views;
    this['off'] = 0;
}
window['newArr'] = newArr;
window['newByteArr'] = newByteArr;
window['wrapByteArr'] = wrapByteArr;
window['ByteArray'] = ByteArray;

// An attempt at emulating pointers enough for ByteString and Text to be
// usable without patching the hell out of them.
// The general idea is that Addr# is a byte array with an associated offset.

function plusAddr(addr, off) {
    var newaddr = {};
    newaddr['off'] = addr['off'] + off;
    newaddr['b']   = addr['b'];
    newaddr['v']   = addr['v'];
    return newaddr;
}

function writeOffAddr(type, elemsize, addr, off, x) {
    addr['v'][type][addr.off/elemsize + off] = x;
}

function writeOffAddr64(addr, off, x) {
    addr['v']['w32'][addr.off/8 + off*2] = x.low;
    addr['v']['w32'][addr.off/8 + off*2 + 1] = x.high;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

function readOffAddr64(signed, addr, off) {
    var w64 = hs_mkWord64( addr['v']['w32'][addr.off/8 + off*2]
                         , addr['v']['w32'][addr.off/8 + off*2 + 1]);
    return signed ? hs_word64ToInt64(w64) : w64;
}

// Two addresses are equal if they point to the same buffer and have the same
// offset. For other comparisons, just use the offsets - nobody in their right
// mind would check if one pointer is less than another, completely unrelated,
// pointer and then act on that information anyway.
function addrEq(a, b) {
    if(a == b) {
        return true;
    }
    return a && b && a['b'] == b['b'] && a['off'] == b['off'];
}

function addrLT(a, b) {
    if(a) {
        return b && a['off'] < b['off'];
    } else {
        return (b != 0); 
    }
}

function addrGT(a, b) {
    if(b) {
        return a && a['off'] > b['off'];
    } else {
        return (a != 0);
    }
}

function withChar(f, charCode) {
    return f(String.fromCharCode(charCode)).charCodeAt(0);
}

function u_towlower(charCode) {
    return withChar(function(c) {return c.toLowerCase()}, charCode);
}

function u_towupper(charCode) {
    return withChar(function(c) {return c.toUpperCase()}, charCode);
}

var u_towtitle = u_towupper;

function u_iswupper(charCode) {
    var c = String.fromCharCode(charCode);
    return c == c.toUpperCase() && c != c.toLowerCase();
}

function u_iswlower(charCode) {
    var c = String.fromCharCode(charCode);
    return  c == c.toLowerCase() && c != c.toUpperCase();
}

function u_iswdigit(charCode) {
    return charCode >= 48 && charCode <= 57;
}

function u_iswcntrl(charCode) {
    return charCode <= 0x1f || charCode == 0x7f;
}

function u_iswspace(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(/\s/g,'') != c;
}

function u_iswalpha(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(__hs_alphare, '') != c;
}

function u_iswalnum(charCode) {
    return u_iswdigit(charCode) || u_iswalpha(charCode);
}

function u_iswprint(charCode) {
    return !u_iswcntrl(charCode);
}

function u_gencat(c) {
    throw 'u_gencat is only supported with --full-unicode.';
}

// Regex that matches any alphabetic character in any language. Horrible thing.
var __hs_alphare = /[\u0041-\u005A\u0061-\u007A\u00AA\u00B5\u00BA\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0370-\u0374\u0376\u0377\u037A-\u037D\u0386\u0388-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u048A-\u0527\u0531-\u0556\u0559\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2\u0620-\u064A\u066E\u066F\u0671-\u06D3\u06D5\u06E5\u06E6\u06EE\u06EF\u06FA-\u06FC\u06FF\u0710\u0712-\u072F\u074D-\u07A5\u07B1\u07CA-\u07EA\u07F4\u07F5\u07FA\u0800-\u0815\u081A\u0824\u0828\u0840-\u0858\u08A0\u08A2-\u08AC\u0904-\u0939\u093D\u0950\u0958-\u0961\u0971-\u0977\u0979-\u097F\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BD\u09CE\u09DC\u09DD\u09DF-\u09E1\u09F0\u09F1\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A59-\u0A5C\u0A5E\u0A72-\u0A74\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABD\u0AD0\u0AE0\u0AE1\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3D\u0B5C\u0B5D\u0B5F-\u0B61\u0B71\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C33\u0C35-\u0C39\u0C3D\u0C58\u0C59\u0C60\u0C61\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD\u0CDE\u0CE0\u0CE1\u0CF1\u0CF2\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D\u0D4E\u0D60\u0D61\u0D7A-\u0D7F\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0E01-\u0E30\u0E32\u0E33\u0E40-\u0E46\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB0\u0EB2\u0EB3\u0EBD\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF\u0F00\u0F40-\u0F47\u0F49-\u0F6C\u0F88-\u0F8C\u1000-\u102A\u103F\u1050-\u1055\u105A-\u105D\u1061\u1065\u1066\u106E-\u1070\u1075-\u1081\u108E\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u1700-\u170C\u170E-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176C\u176E-\u1770\u1780-\u17B3\u17D7\u17DC\u1820-\u1877\u1880-\u18A8\u18AA\u18B0-\u18F5\u1900-\u191C\u1950-\u196D\u1970-\u1974\u1980-\u19AB\u19C1-\u19C7\u1A00-\u1A16\u1A20-\u1A54\u1AA7\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0\u1BAE\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23\u1C4D-\u1C4F\u1C5A-\u1C7D\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5\u1CF6\u1D00-\u1DBF\u1E00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u2071\u207F\u2090-\u209C\u2102\u2107\u210A-\u2113\u2115\u2119-\u211D\u2124\u2126\u2128\u212A-\u212D\u212F-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2183\u2184\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CEE\u2CF2\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u2E2F\u3005\u3006\u3031-\u3035\u303B\u303C\u3041-\u3096\u309D-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA61F\uA62A\uA62B\uA640-\uA66E\uA67F-\uA697\uA6A0-\uA6E5\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA793\uA7A0-\uA7AA\uA7F8-\uA801\uA803-\uA805\uA807-\uA80A\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3\uA8F2-\uA8F7\uA8FB\uA90A-\uA925\uA930-\uA946\uA960-\uA97C\uA984-\uA9B2\uA9CF\uAA00-\uAA28\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76\uAA7A\uAA80-\uAAAF\uAAB1\uAAB5\uAAB6\uAAB9-\uAABD\uAAC0\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uABC0-\uABE2\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D\uFB1F-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]/g;

// Simulate handles.
// When implementing new handles, remember that passed strings may be thunks,
// and so need to be evaluated before use.

function jsNewHandle(init, read, write, flush, close, seek, tell) {
    var h = {
        read: read || function() {},
        write: write || function() {},
        seek: seek || function() {},
        tell: tell || function() {},
        close: close || function() {},
        flush: flush || function() {}
    };
    init.call(h);
    return h;
}

function jsReadHandle(h, len) {return h.read(len);}
function jsWriteHandle(h, str) {return h.write(str);}
function jsFlushHandle(h) {return h.flush();}
function jsCloseHandle(h) {return h.close();}

function jsMkConWriter(op) {
    return function(str) {
        str = E(str);
        var lines = (this.buf + str).split('\n');
        for(var i = 0; i < lines.length-1; ++i) {
            op.call(console, lines[i]);
        }
        this.buf = lines[lines.length-1];
    }
}

function jsMkStdout() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.log),
        function() {console.log(this.buf); this.buf = '';}
    );
}

function jsMkStderr() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.warn),
        function() {console.warn(this.buf); this.buf = '';}
    );
}

function jsMkStdin() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(len) {
            while(this.buf.length < len) {
                this.buf += prompt('[stdin]') + '\n';
            }
            var ret = this.buf.substr(0, len);
            this.buf = this.buf.substr(len);
            return ret;
        }
    );
}

// "Weak Pointers". Mostly useless implementation since
// JS does its own GC.

function mkWeak(key, val, fin) {
    fin = !fin? function() {}: fin;
    return {key: key, val: val, fin: fin};
}

function derefWeak(w) {
    return {_:0, a:1, b:E(w).val};
}

function finalizeWeak(w) {
    return {_:0, a:B(A1(E(w).fin, __Z))};
}

/* For foreign import ccall "wrapper" */
function createAdjustor(args, f, a, b) {
    return function(){
        var x = f.apply(null, arguments);
        while(x instanceof F) {x = x.f();}
        return x;
    };
}

var __apply = function(f,as) {
    var arr = [];
    for(; as._ === 1; as = as.b) {
        arr.push(as.a);
    }
    arr.reverse();
    return f.apply(null, arr);
}
var __app0 = function(f) {return f();}
var __app1 = function(f,a) {return f(a);}
var __app2 = function(f,a,b) {return f(a,b);}
var __app3 = function(f,a,b,c) {return f(a,b,c);}
var __app4 = function(f,a,b,c,d) {return f(a,b,c,d);}
var __app5 = function(f,a,b,c,d,e) {return f(a,b,c,d,e);}
var __jsNull = function() {return null;}
var __eq = function(a,b) {return a===b;}
var __createJSFunc = function(arity, f){
    if(f instanceof Function && arity === f.length) {
        return (function() {
            var x = f.apply(null,arguments);
            if(x instanceof T) {
                if(x.f !== __blackhole) {
                    var ff = x.f;
                    x.f = __blackhole;
                    return x.x = ff();
                }
                return x.x;
            } else {
                while(x instanceof F) {
                    x = x.f();
                }
                return E(x);
            }
        });
    } else {
        return (function(){
            var as = Array.prototype.slice.call(arguments);
            as.push(0);
            return E(B(A(f,as)));
        });
    }
}


function __arr2lst(elem,arr) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1,
            a:arr[elem],
            b:new T(function(){return __arr2lst(elem+1,arr);})};
}

function __lst2arr(xs) {
    var arr = [];
    xs = E(xs);
    for(;xs._ === 1; xs = E(xs.b)) {
        arr.push(E(xs.a));
    }
    return arr;
}

var __new = function() {return ({});}
var __set = function(o,k,v) {o[k]=v;}
var __get = function(o,k) {return o[k];}
var __has = function(o,k) {return o[k]!==undefined;}

var _0=function(_1,_2,_){var _3=B(A1(_1,_)),_4=B(A1(_2,_));return new T(function(){return B(A1(_3,_4));});},_5=function(_6,_7,_){var _8=B(A1(_7,_));return new T(function(){return B(A1(_6,_8));});},_9=function(_a,_){return _a;},_b=function(_c,_d,_){var _e=B(A1(_c,_));return C > 19 ? new F(function(){return A1(_d,_);}) : (++C,A1(_d,_));},_f=new T(function(){return unCStr("base");}),_g=new T(function(){return unCStr("GHC.IO.Exception");}),_h=new T(function(){return unCStr("IOException");}),_i=function(_j){return E(new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_f,_g,_h),__Z,__Z));},_k=function(_l){return E(E(_l).a);},_m=function(_n,_o,_p){var _q=B(A1(_n,_)),_r=B(A1(_o,_)),_s=hs_eqWord64(_q.a,_r.a);if(!_s){return __Z;}else{var _t=hs_eqWord64(_q.b,_r.b);return (!_t)?__Z:new T1(1,_p);}},_u=new T(function(){return unCStr(": ");}),_v=new T(function(){return unCStr(")");}),_w=new T(function(){return unCStr(" (");}),_x=function(_y,_z){var _A=E(_y);return (_A._==0)?E(_z):new T2(1,_A.a,new T(function(){return _x(_A.b,_z);}));},_B=new T(function(){return unCStr("interrupted");}),_C=new T(function(){return unCStr("system error");}),_D=new T(function(){return unCStr("unsatisified constraints");}),_E=new T(function(){return unCStr("user error");}),_F=new T(function(){return unCStr("permission denied");}),_G=new T(function(){return unCStr("illegal operation");}),_H=new T(function(){return unCStr("end of file");}),_I=new T(function(){return unCStr("resource exhausted");}),_J=new T(function(){return unCStr("resource busy");}),_K=new T(function(){return unCStr("does not exist");}),_L=new T(function(){return unCStr("already exists");}),_M=new T(function(){return unCStr("resource vanished");}),_N=new T(function(){return unCStr("timeout");}),_O=new T(function(){return unCStr("unsupported operation");}),_P=new T(function(){return unCStr("hardware fault");}),_Q=new T(function(){return unCStr("inappropriate type");}),_R=new T(function(){return unCStr("invalid argument");}),_S=new T(function(){return unCStr("failed");}),_T=new T(function(){return unCStr("protocol error");}),_U=function(_V,_W){switch(E(_V)){case 0:return _x(_L,_W);case 1:return _x(_K,_W);case 2:return _x(_J,_W);case 3:return _x(_I,_W);case 4:return _x(_H,_W);case 5:return _x(_G,_W);case 6:return _x(_F,_W);case 7:return _x(_E,_W);case 8:return _x(_D,_W);case 9:return _x(_C,_W);case 10:return _x(_T,_W);case 11:return _x(_S,_W);case 12:return _x(_R,_W);case 13:return _x(_Q,_W);case 14:return _x(_P,_W);case 15:return _x(_O,_W);case 16:return _x(_N,_W);case 17:return _x(_M,_W);default:return _x(_B,_W);}},_X=new T(function(){return unCStr("}");}),_Y=new T(function(){return unCStr("{handle: ");}),_Z=function(_10,_11,_12,_13,_14,_15){var _16=new T(function(){var _17=new T(function(){var _18=new T(function(){var _19=E(_13);if(!_19._){return E(_15);}else{var _1a=new T(function(){return _x(_19,new T(function(){return _x(_v,_15);},1));},1);return _x(_w,_1a);}},1);return _U(_11,_18);}),_1b=E(_12);if(!_1b._){return E(_17);}else{return _x(_1b,new T(function(){return _x(_u,_17);},1));}}),_1c=E(_14);if(!_1c._){var _1d=E(_10);if(!_1d._){return E(_16);}else{var _1e=E(_1d.a);if(!_1e._){var _1f=new T(function(){var _1g=new T(function(){return _x(_X,new T(function(){return _x(_u,_16);},1));},1);return _x(_1e.a,_1g);},1);return _x(_Y,_1f);}else{var _1h=new T(function(){var _1i=new T(function(){return _x(_X,new T(function(){return _x(_u,_16);},1));},1);return _x(_1e.a,_1i);},1);return _x(_Y,_1h);}}}else{return _x(_1c.a,new T(function(){return _x(_u,_16);},1));}},_1j=function(_1k){var _1l=E(_1k);return _Z(_1l.a,_1l.b,_1l.c,_1l.d,_1l.f,__Z);},_1m=function(_1n,_1o){var _1p=E(_1n);return _Z(_1p.a,_1p.b,_1p.c,_1p.d,_1p.f,_1o);},_1q=function(_1r,_1s,_1t){var _1u=E(_1s);if(!_1u._){return unAppCStr("[]",_1t);}else{var _1v=new T(function(){var _1w=new T(function(){var _1x=function(_1y){var _1z=E(_1y);if(!_1z._){return E(new T2(1,93,_1t));}else{var _1A=new T(function(){return B(A2(_1r,_1z.a,new T(function(){return _1x(_1z.b);})));});return new T2(1,44,_1A);}};return _1x(_1u.b);});return B(A2(_1r,_1u.a,_1w));});return new T2(1,91,_1v);}},_1B=new T(function(){return new T5(0,_i,new T3(0,function(_1C,_1D,_1E){var _1F=E(_1D);return _Z(_1F.a,_1F.b,_1F.c,_1F.d,_1F.f,_1E);},_1j,function(_1G,_1H){return _1q(_1m,_1G,_1H);}),function(_1I){return new T2(0,_1B,_1I);},function(_1J){var _1K=E(_1J);return _m(_k(_1K.a),_i,_1K.b);},_1j);}),_1L=new T(function(){return E(_1B);}),_1M=function(_1N){return E(E(_1N).c);},_1O=function(_1P){return new T6(0,__Z,7,__Z,_1P,__Z,__Z);},_1Q=function(_1R,_){var _1S=new T(function(){return B(A2(_1M,_1L,new T(function(){return B(A1(_1O,_1R));})));});return die(_1S);},_1T=function(_1U,_){return _1Q(_1U,_);},_1V=function(_1W){return E(_1W);},_1X=new T2(0,new T5(0,new T5(0,new T2(0,_5,function(_1Y,_1Z,_){var _20=B(A1(_1Z,_));return _1Y;}),_9,_0,_b,function(_21,_22,_){var _23=B(A1(_21,_)),_24=B(A1(_22,_));return _23;}),function(_25,_26,_){var _27=B(A1(_25,_));return C > 19 ? new F(function(){return A2(_26,_27,_);}) : (++C,A2(_26,_27,_));},_b,_9,function(_28){return C > 19 ? new F(function(){return A1(_1T,_28);}) : (++C,A1(_1T,_28));}),_1V),_29=new T1(0,1),_2a=function(_2b,_){var _2c=_2b["keyCode"],_2d=_2b["ctrlKey"],_2e=_2b["altKey"],_2f=_2b["shiftKey"],_2g=_2b["metaKey"];return new T(function(){var _2h=Number(_2c),_2i=jsTrunc(_2h);return new T5(0,_2i,E(_2d),E(_2e),E(_2f),E(_2g));});},_2j=new T2(0,function(_2k){switch(E(_2k)){case 0:return "keypress";case 1:return "keyup";default:return "keydown";}},function(_2l,_2m,_){return _2a(E(_2m),_);}),_2n=new T(function(){return unCStr("%Y-%m-%d");}),_2o=new T(function(){return unCStr("%m/%d/%y");}),_2p=function(_2q,_2r){var _2s=jsShowI(_2q);return _x(fromJSStr(_2s),_2r);},_2t=function(_2u,_2v,_2w){if(_2v>=0){return _2p(_2v,_2w);}else{if(_2u<=6){return _2p(_2v,_2w);}else{return new T2(1,40,new T(function(){var _2x=jsShowI(_2v);return _x(fromJSStr(_2x),new T2(1,41,_2w));}));}}},_2y=function(_2z,_2A){if(_2z<=0){if(_2z>=0){return quot(_2z,_2A);}else{if(_2A<=0){return quot(_2z,_2A);}else{return quot(_2z+1|0,_2A)-1|0;}}}else{if(_2A>=0){if(_2z>=0){return quot(_2z,_2A);}else{if(_2A<=0){return quot(_2z,_2A);}else{return quot(_2z+1|0,_2A)-1|0;}}}else{return quot(_2z-1|0,_2A)-1|0;}}},_2B=function(_2C,_2D){while(1){var _2E=E(_2C);if(!_2E._){var _2F=E(_2E.a);if(_2F==(-2147483648)){_2C=new T1(1,I_fromInt(-2147483648));continue;}else{var _2G=E(_2D);if(!_2G._){return new T1(0,_2y(_2F,_2G.a));}else{_2C=new T1(1,I_fromInt(_2F));_2D=_2G;continue;}}}else{var _2H=_2E.a,_2I=E(_2D);return (_2I._==0)?new T1(1,I_div(_2H,I_fromInt(_2I.a))):new T1(1,I_div(_2H,_2I.a));}}},_2J=new T(function(){return unCStr("base");}),_2K=new T(function(){return unCStr("GHC.Exception");}),_2L=new T(function(){return unCStr("ArithException");}),_2M=function(_2N){return E(new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_2J,_2K,_2L),__Z,__Z));},_2O=new T(function(){return unCStr("Ratio has zero denominator");}),_2P=new T(function(){return unCStr("denormal");}),_2Q=new T(function(){return unCStr("divide by zero");}),_2R=new T(function(){return unCStr("loss of precision");}),_2S=new T(function(){return unCStr("arithmetic underflow");}),_2T=new T(function(){return unCStr("arithmetic overflow");}),_2U=function(_2V,_2W){switch(E(_2V)){case 0:return _x(_2T,_2W);case 1:return _x(_2S,_2W);case 2:return _x(_2R,_2W);case 3:return _x(_2Q,_2W);case 4:return _x(_2P,_2W);default:return _x(_2O,_2W);}},_2X=function(_2Y){return _2U(_2Y,__Z);},_2Z=new T(function(){return new T5(0,_2M,new T3(0,function(_30,_31,_32){return _2U(_31,_32);},_2X,function(_33,_34){return _1q(_2U,_33,_34);}),_35,function(_36){var _37=E(_36);return _m(_k(_37.a),_2M,_37.b);},_2X);}),_35=function(_38){return new T2(0,_2Z,_38);},_39=new T(function(){return die(new T(function(){return _35(3);}));}),_3a=new T1(0,1),_3b=new T1(0,365),_3c=function(_3d){var _3e=E(_3d);if(!_3e._){return E(_3e.a);}else{return I_toInt(_3e.a);}},_3f=new T1(0,100),_3g=new T1(0,400),_3h=new T1(0,4),_3i=function(_3j,_3k){var _3l=E(_3j);if(!_3l._){var _3m=_3l.a,_3n=E(_3k);return (_3n._==0)?_3m<=_3n.a:I_compareInt(_3n.a,_3m)>=0;}else{var _3o=_3l.a,_3p=E(_3k);return (_3p._==0)?I_compareInt(_3o,_3p.a)<=0:I_compare(_3o,_3p.a)<=0;}},_3q=new T1(0,146097),_3r=new T1(0,36524),_3s=new T1(0,1461),_3t=function(_3u,_3v){var _3w=E(_3u);if(!_3w._){var _3x=_3w.a,_3y=E(_3v);return (_3y._==0)?_3x==_3y.a:(I_compareInt(_3y.a,_3x)==0)?true:false;}else{var _3z=_3w.a,_3A=E(_3v);return (_3A._==0)?(I_compareInt(_3z,_3A.a)==0)?true:false:(I_compare(_3z,_3A.a)==0)?true:false;}},_3B=new T1(0,0),_3C=new T(function(){return _3t(_3q,_3B);}),_3D=new T(function(){return _3t(_3r,_3B);}),_3E=new T(function(){return _3t(_3s,_3B);}),_3F=new T(function(){return _3t(_3b,_3B);}),_3G=function(_3H,_3I){while(1){var _3J=E(_3H);if(!_3J._){var _3K=_3J.a,_3L=E(_3I);if(!_3L._){var _3M=_3L.a,_3N=subC(_3K,_3M);if(!E(_3N.b)){return new T1(0,_3N.a);}else{_3H=new T1(1,I_fromInt(_3K));_3I=new T1(1,I_fromInt(_3M));continue;}}else{_3H=new T1(1,I_fromInt(_3K));_3I=_3L;continue;}}else{var _3O=E(_3I);if(!_3O._){_3H=_3J;_3I=new T1(1,I_fromInt(_3O.a));continue;}else{return new T1(1,I_sub(_3J.a,_3O.a));}}}},_3P=function(_3Q,_3R){var _3S=_3Q%_3R;if(_3Q<=0){if(_3Q>=0){return _3S;}else{if(_3R<=0){return _3S;}else{return (_3S==0)?0:_3S+_3R|0;}}}else{if(_3R>=0){if(_3Q>=0){return _3S;}else{if(_3R<=0){return _3S;}else{return (_3S==0)?0:_3S+_3R|0;}}}else{return (_3S==0)?0:_3S+_3R|0;}}},_3T=function(_3U,_3V){while(1){var _3W=E(_3U);if(!_3W._){var _3X=E(_3W.a);if(_3X==(-2147483648)){_3U=new T1(1,I_fromInt(-2147483648));continue;}else{var _3Y=E(_3V);if(!_3Y._){return new T1(0,_3P(_3X,_3Y.a));}else{_3U=new T1(1,I_fromInt(_3X));_3V=_3Y;continue;}}}else{var _3Z=_3W.a,_40=E(_3V);return (_40._==0)?new T1(1,I_mod(_3Z,I_fromInt(_40.a))):new T1(1,I_mod(_3Z,_40.a));}}},_41=function(_42,_43){while(1){var _44=E(_42);if(!_44._){var _45=_44.a,_46=E(_43);if(!_46._){var _47=_46.a,_48=addC(_45,_47);if(!E(_48.b)){return new T1(0,_48.a);}else{_42=new T1(1,I_fromInt(_45));_43=new T1(1,I_fromInt(_47));continue;}}else{_42=new T1(1,I_fromInt(_45));_43=_46;continue;}}else{var _49=E(_43);if(!_49._){_42=_44;_43=new T1(1,I_fromInt(_49.a));continue;}else{return new T1(1,I_add(_44.a,_49.a));}}}},_4a=new T1(0,3),_4b=function(_4c,_4d){while(1){var _4e=E(_4c);if(!_4e._){var _4f=_4e.a,_4g=E(_4d);if(!_4g._){var _4h=_4g.a;if(!(imul(_4f,_4h)|0)){return new T1(0,imul(_4f,_4h)|0);}else{_4c=new T1(1,I_fromInt(_4f));_4d=new T1(1,I_fromInt(_4h));continue;}}else{_4c=new T1(1,I_fromInt(_4f));_4d=_4g;continue;}}else{var _4i=E(_4d);if(!_4i._){_4c=_4e;_4d=new T1(1,I_fromInt(_4i.a));continue;}else{return new T1(1,I_mul(_4e.a,_4i.a));}}}},_4j=function(_4k){var _4l=new T(function(){return _41(_4k,new T1(0,678575));}),_4m=new T(function(){if(!E(_3C)){return _3T(_4l,_3q);}else{return E(_39);}}),_4n=new T(function(){if(!E(_3D)){var _4o=_2B(_4m,_3r);if(!_3i(_4o,_4a)){return E(_4a);}else{return E(_4o);}}else{return E(_39);}}),_4p=new T(function(){return _3G(_4m,_4b(_4n,_3r));}),_4q=new T(function(){if(!E(_3E)){return _3T(_4p,_3s);}else{return E(_39);}}),_4r=new T(function(){if(!E(_3F)){var _4s=_2B(_4q,_3b);if(!_3i(_4s,_4a)){return E(_4a);}else{return E(_4s);}}else{return E(_39);}});return new T2(0,new T(function(){if(!E(_3C)){if(!E(_3E)){return _41(_41(_41(_41(_4b(_2B(_4l,_3q),_3g),_4b(_4n,_3f)),_4b(_2B(_4p,_3s),_3h)),_4r),_3a);}else{return E(_39);}}else{return E(_39);}}),new T(function(){return _3c(_41(_3G(_4q,_4b(_4r,_3b)),_3a));}));},_4t=new T1(0,7),_4u=new T(function(){return _3t(_4t,_3B);}),_4v=function(_4w){return new T1(0,_4w);},_4x=function(_4y){var _4z=new T(function(){return _41(_4y,_4a);});return new T2(0,new T(function(){if(!E(_4u)){return _3c(_3G(_2B(_4z,_4t),_2B(_3G(_4z,_4v(E(_4j(_4y).b))),_4t)));}else{return E(_39);}}),new T(function(){if(!E(_4u)){return _3c(_3T(_4z,_4t));}else{return E(_39);}}));},_4A=function(_4B,_4C,_4D){return _2t(0,E(_4x(_4D).b),__Z);},_4E=new T1(0,678576),_4F=new T(function(){return _3t(_3f,_3B);}),_4G=new T(function(){return _3t(_3g,_3B);}),_4H=new T(function(){return _3t(_3h,_3B);}),_4I=function(_4J){return (!E(_4H))?(!_3t(_3T(_4J,_3h),_3B))?false:(!E(_4G))?(!_3t(_3T(_4J,_3g),_3B))?(!E(_4F))?(!_3t(_3T(_4J,_3f),_3B))?true:false:E(_39):true:E(_39):E(_39);},_4K=function(_4L,_4M){if(!E(_4H)){if(!E(_4F)){if(!E(_4G)){var _4N=_3G(_4L,_3a);if(_4M>=1){if(!_4I(_4L)){if(_4M<=365){return _3G(_41(_3G(_41(_41(_4v(_4M),_4b(_3b,_4N)),_2B(_4N,_3h)),_2B(_4N,_3f)),_2B(_4N,_3g)),_4E);}else{return _3G(_41(_3G(_41(_41(_3b,_4b(_3b,_4N)),_2B(_4N,_3h)),_2B(_4N,_3f)),_2B(_4N,_3g)),_4E);}}else{if(_4M<=366){return _3G(_41(_3G(_41(_41(_4v(_4M),_4b(_3b,_4N)),_2B(_4N,_3h)),_2B(_4N,_3f)),_2B(_4N,_3g)),_4E);}else{return _3G(_41(_3G(_41(_41(new T1(0,366),_4b(_3b,_4N)),_2B(_4N,_3h)),_2B(_4N,_3f)),_2B(_4N,_3g)),_4E);}}}else{return _3G(_41(_3G(_41(_41(_3a,_4b(_3b,_4N)),_2B(_4N,_3h)),_2B(_4N,_3f)),_2B(_4N,_3g)),_4E);}}else{return E(_39);}}else{return E(_39);}}else{return E(_39);}},_4O=function(_4P,_4Q){while(1){var _4R=E(_4P);if(!_4R._){var _4S=E(_4R.a);if(_4S==(-2147483648)){_4P=new T1(1,I_fromInt(-2147483648));continue;}else{var _4T=E(_4Q);if(!_4T._){var _4U=_4T.a;return new T2(0,new T1(0,_2y(_4S,_4U)),new T1(0,_3P(_4S,_4U)));}else{_4P=new T1(1,I_fromInt(_4S));_4Q=_4T;continue;}}}else{var _4V=E(_4Q);if(!_4V._){_4P=_4R;_4Q=new T1(1,I_fromInt(_4V.a));continue;}else{var _4W=I_divMod(_4R.a,_4V.a);return new T2(0,new T1(1,_4W.a),new T1(1,_4W.b));}}}},_4X=new T1(0,7),_4Y=new T1(0,0),_4Z=new T(function(){return _3t(_4X,_4Y);}),_50=new T1(0,52),_51=new T1(0,1),_52=function(_53){var _54=new T(function(){return _41(_53,new T1(0,2));}),_55=new T(function(){if(!E(_4Z)){var _56=_4O(_54,_4X);return new T2(0,_56.a,_56.b);}else{return E(_39);}}),_57=new T(function(){var _58=E(_55).a,_59=_4j(_53),_5a=_59.a;if(!E(_4Z)){var _5b=_3G(_58,_2B(_41(_3G(_54,_4v(E(_59.b))),new T1(0,4)),_4X));}else{var _5b=E(_39);}if(!_3t(_5b,new T1(0,-1))){if(!_3t(_5b,_50)){return new T2(0,_5a,_5b);}else{if(!E(_4Z)){if(!_3t(_3G(_58,_2B(_4K(_41(_5a,_51),6),_4X)),_4Y)){return new T2(0,_5a,_50);}else{return new T2(0,new T(function(){return _41(_5a,_51);}),_4Y);}}else{return E(_39);}}}else{return new T2(0,new T(function(){return _3G(_5a,_51);}),new T(function(){if(!E(_4Z)){return _3G(_58,_2B(_4K(_3G(_5a,_51),6),_4X));}else{return E(_39);}}));}});return new T3(0,new T(function(){return E(E(_57).a);}),new T(function(){return _3c(_41(E(_57).b,_51));}),new T(function(){return _3c(E(_55).b)+1|0;}));},_5c=function(_5d,_5e,_5f){return _2t(0,E(_52(_5f).c),__Z);},_5g=new T1(1,48),_5h={_:0,a:function(_5i,_5j){return E(_5i)+E(_5j)|0;},b:function(_5k,_5l){return E(_5k)-E(_5l)|0;},c:function(_5m,_5n){return imul(E(_5m),E(_5n))|0;},d:function(_5o){return  -E(_5o);},e:function(_5p){var _5q=E(_5p);return (_5q<0)? -_5q:_5q;},f:function(_5r){var _5s=E(_5r);return (_5s>=0)?(_5s==0)?0:1:-1;},g:function(_5t){return _3c(_5t);}},_5u=function(_5v,_5w){return (_5v>=_5w)?(_5v!=_5w)?2:1:0;},_5x={_:0,a:new T2(0,function(_5y,_5z){return E(_5y)==E(_5z);},function(_5A,_5B){return E(_5A)!=E(_5B);}),b:function(_5C,_5D){return _5u(E(_5C),E(_5D));},c:function(_5E,_5F){return E(_5E)<E(_5F);},d:function(_5G,_5H){return E(_5G)<=E(_5H);},e:function(_5I,_5J){return E(_5I)>E(_5J);},f:function(_5K,_5L){return E(_5K)>=E(_5L);},g:function(_5M,_5N){var _5O=E(_5M),_5P=E(_5N);return (_5O>_5P)?_5O:_5P;},h:function(_5Q,_5R){var _5S=E(_5Q),_5T=E(_5R);return (_5S>_5T)?_5T:_5S;}},_5U=function(_5V,_5W){return _2t(0,E(_5V),_5W);},_5X=new T3(0,function(_5Y,_5Z,_60){return _2t(E(_5Y),E(_5Z),_60);},function(_61){return _2t(0,E(_61),__Z);},function(_62,_63){return _1q(_5U,_62,_63);}),_64=function(_65,_66){var _67=E(_65);if(!_67._){return new T2(0,1,_66);}else{var _68=E(_66),_69=E(_67.a);if(_68<=_69){return new T2(0,1,_68);}else{var _6a=_64(_67.b,_68-_69|0);return new T2(0,new T(function(){return E(_6a.a)+1|0;}),_6a.b);}}},_6b=function(_6c){return new T2(1,31,new T2(1,new T(function(){if(!E(_6c)){return 28;}else{return 29;}}),new T2(1,31,new T2(1,30,new T2(1,31,new T2(1,30,new T2(1,31,new T2(1,31,new T2(1,30,new T2(1,31,new T2(1,30,new T2(1,31,__Z))))))))))));},_6d=function(_6e,_6f){return _64(_6b(_6e),new T(function(){var _6g=E(_6f);if(_6g>=1){if(!E(_6e)){if(_6g<=365){return _6g;}else{return 365;}}else{if(_6g<=366){return _6g;}else{return 366;}}}else{return 1;}}));},_6h=function(_6i){var _6j=new T(function(){var _6k=_4j(_6i);return new T2(0,_6k.a,_6k.b);}),_6l=new T(function(){return E(E(_6j).a);}),_6m=new T(function(){var _6n=_6d(new T(function(){return _4I(_6l);}),new T(function(){return E(E(_6j).b);},1));return new T2(0,_6n.a,_6n.b);});return new T3(0,_6l,new T(function(){return E(E(_6m).a);}),new T(function(){return E(E(_6m).b);}));},_6o=function(_6p,_6q){while(1){var _6r=E(_6p);if(!_6r._){return E(_6q);}else{var _6s=_6q+1|0;_6p=_6r.b;_6q=_6s;continue;}}},_6t=function(_6u,_6v,_6w){if(_6u>0){if(0>=_6u){return E(_6w);}else{var _6x=function(_6y){var _6z=E(_6y);return (_6z==1)?E(new T2(1,_6v,_6w)):new T2(1,_6v,new T(function(){return _6x(_6z-1|0);}));};return _6x(_6u);}}else{return E(_6w);}},_6A=function(_6B){return E(E(_6B).c);},_6C=function(_6D){return E(E(_6D).g);},_6E=function(_6F){return E(E(_6F).d);},_6G=function(_6H){return E(E(_6H).b);},_6I=function(_6J,_6K,_6L,_6M,_6N,_6O){var _6P=E(_6N);if(!_6P._){return C > 19 ? new F(function(){return A2(_6G,_6L,_6O);}) : (++C,A2(_6G,_6L,_6O));}else{if(!B(A3(_6A,_6K,_6O,new T(function(){return B(A2(_6C,_6J,new T1(0,0)));})))){var _6Q=B(A2(_6G,_6L,_6O));return _6t(E(_6M)-_6o(_6Q,0)|0,_6P.a,_6Q);}else{var _6R=new T(function(){return B(_6I(_6J,_6K,_6L,_6M,_6P,new T(function(){return B(A2(_6E,_6J,_6O));})));});return new T2(1,45,_6R);}}},_6S=function(_6T,_6U){var _6V=E(_6T);if(!_6V._){return C > 19 ? new F(function(){return _6I(_5h,_5x,_5X,2,_5g,new T(function(){return E(_6h(_6U).b);}));}) : (++C,_6I(_5h,_5x,_5X,2,_5g,new T(function(){return E(_6h(_6U).b);})));}else{return C > 19 ? new F(function(){return _6I(_5h,_5x,_5X,2,_6V.a,new T(function(){return E(_6h(_6U).b);}));}) : (++C,_6I(_5h,_5x,_5X,2,_6V.a,new T(function(){return E(_6h(_6U).b);})));}},_6W=function(_6X,_6Y,_6Z){return C > 19 ? new F(function(){return _6S(_6Y,_6Z);}) : (++C,_6S(_6Y,_6Z));},_70=function(_71,_72){var _73=E(_71);if(!_73._){return C > 19 ? new F(function(){return _6I(_5h,_5x,_5X,3,_5g,new T(function(){return E(_4j(_72).b);}));}) : (++C,_6I(_5h,_5x,_5X,3,_5g,new T(function(){return E(_4j(_72).b);})));}else{return C > 19 ? new F(function(){return _6I(_5h,_5x,_5X,3,_73.a,new T(function(){return E(_4j(_72).b);}));}) : (++C,_6I(_5h,_5x,_5X,3,_73.a,new T(function(){return E(_4j(_72).b);})));}},_74=function(_75,_76,_77){return C > 19 ? new F(function(){return _70(_76,_77);}) : (++C,_70(_76,_77));},_78=new T(function(){return unCStr("Prelude.");}),_79=new T(function(){return err(new T(function(){return _x(_78,new T(function(){return unCStr("!!: negative index");}));}));}),_7a=new T(function(){return err(new T(function(){return _x(_78,new T(function(){return unCStr("!!: index too large");}));}));}),_7b=function(_7c,_7d){while(1){var _7e=E(_7c);if(!_7e._){return E(_7a);}else{var _7f=E(_7d);if(!_7f){return E(_7e.a);}else{_7c=_7e.b;_7d=_7f-1|0;continue;}}}},_7g=function(_7h,_7i){if(_7i>=0){return _7b(_7h,_7i);}else{return E(_79);}},_7j=function(_7k,_7l){return E(_7g(_7k,E(_6h(_7l).b)-1|0).b);},_7m=function(_7n,_7o,_7p){return _7j(E(_7n).b,_7p);},_7q=new T1(0,100),_7r=new T(function(){return _3t(_7q,new T1(0,0));}),_7s=new T1(0,1),_7t=new T(function(){return _41(new T1(0,2147483647),_7s);}),_7u=function(_7v){var _7w=E(_7v);if(!_7w._){var _7x=E(_7w.a);return (_7x==(-2147483648))?E(_7t):(_7x<0)?new T1(0, -_7x):_7w;}else{var _7y=_7w.a;return (I_compareInt(_7y,0)>=0)?_7w:new T1(1,I_negate(_7y));}},_7z=function(_7A){var _7B=E(_7A);if(!_7B._){var _7C=E(_7B.a);return (_7C==(-2147483648))?E(_7t):new T1(0, -_7C);}else{return new T1(1,I_negate(_7B.a));}},_7D=new T1(0,0),_7E=new T1(0,-1),_7F=function(_7G){var _7H=E(_7G);if(!_7H._){var _7I=_7H.a;return (_7I>=0)?(E(_7I)==0)?E(_7D):E(_7s):E(_7E);}else{var _7J=I_compareInt(_7H.a,0);return (_7J<=0)?(E(_7J)==0)?E(_7D):E(_7E):E(_7s);}},_7K={_:0,a:_41,b:_3G,c:_4b,d:_7z,e:_7u,f:_7F,g:function(_7L){return E(_7L);}},_7M=function(_7N,_7O){var _7P=E(_7N);if(!_7P._){var _7Q=_7P.a,_7R=E(_7O);return (_7R._==0)?_7Q!=_7R.a:(I_compareInt(_7R.a,_7Q)==0)?false:true;}else{var _7S=_7P.a,_7T=E(_7O);return (_7T._==0)?(I_compareInt(_7S,_7T.a)==0)?false:true:(I_compare(_7S,_7T.a)==0)?false:true;}},_7U=function(_7V,_7W){return (!_3i(_7V,_7W))?E(_7V):E(_7W);},_7X=function(_7Y,_7Z){return (!_3i(_7Y,_7Z))?E(_7Z):E(_7Y);},_80=function(_81,_82){var _83=E(_81);if(!_83._){var _84=_83.a,_85=E(_82);if(!_85._){var _86=_85.a;return (_84!=_86)?(_84>_86)?2:0:1;}else{var _87=I_compareInt(_85.a,_84);return (_87<=0)?(_87>=0)?1:2:0;}}else{var _88=_83.a,_89=E(_82);if(!_89._){var _8a=I_compareInt(_88,_89.a);return (_8a>=0)?(_8a<=0)?1:2:0;}else{var _8b=I_compare(_88,_89.a);return (_8b>=0)?(_8b<=0)?1:2:0;}}},_8c=function(_8d,_8e){var _8f=E(_8d);if(!_8f._){var _8g=_8f.a,_8h=E(_8e);return (_8h._==0)?_8g>=_8h.a:I_compareInt(_8h.a,_8g)<=0;}else{var _8i=_8f.a,_8j=E(_8e);return (_8j._==0)?I_compareInt(_8i,_8j.a)>=0:I_compare(_8i,_8j.a)>=0;}},_8k=function(_8l,_8m){var _8n=E(_8l);if(!_8n._){var _8o=_8n.a,_8p=E(_8m);return (_8p._==0)?_8o>_8p.a:I_compareInt(_8p.a,_8o)<0;}else{var _8q=_8n.a,_8r=E(_8m);return (_8r._==0)?I_compareInt(_8q,_8r.a)>0:I_compare(_8q,_8r.a)>0;}},_8s=function(_8t,_8u){var _8v=E(_8t);if(!_8v._){var _8w=_8v.a,_8x=E(_8u);return (_8x._==0)?_8w<_8x.a:I_compareInt(_8x.a,_8w)>0;}else{var _8y=_8v.a,_8z=E(_8u);return (_8z._==0)?I_compareInt(_8y,_8z.a)<0:I_compare(_8y,_8z.a)<0;}},_8A={_:0,a:new T2(0,_3t,_7M),b:_80,c:_8s,d:_3i,e:_8k,f:_8c,g:_7U,h:_7X},_8B=function(_8C){while(1){var _8D=E(_8C);if(!_8D._){_8C=new T1(1,I_fromInt(_8D.a));continue;}else{return I_toString(_8D.a);}}},_8E=function(_8F,_8G){return _x(fromJSStr(_8B(_8F)),_8G);},_8H=function(_8I,_8J,_8K){if(_8I<=6){return _8E(_8J,_8K);}else{if(!_8s(_8J,new T1(0,0))){return _8E(_8J,_8K);}else{return new T2(1,40,new T(function(){return _x(fromJSStr(_8B(_8J)),new T2(1,41,_8K));}));}}},_8L=function(_8M){return _8H(0,_8M,__Z);},_8N=function(_8O,_8P){var _8Q=E(_8O);if(!_8Q._){return unAppCStr("[]",_8P);}else{var _8R=new T(function(){var _8S=new T(function(){var _8T=function(_8U){var _8V=E(_8U);if(!_8V._){return E(new T2(1,93,_8P));}else{var _8W=new T(function(){return _8H(0,_8V.a,new T(function(){return _8T(_8V.b);}));});return new T2(1,44,_8W);}};return _8T(_8Q.b);});return _8H(0,_8Q.a,_8S);});return new T2(1,91,_8R);}},_8X=new T3(0,function(_8Y,_8Z,_90){return _8H(E(_8Y),_8Z,_90);},_8L,_8N),_91=function(_92,_93){var _94=new T(function(){if(!E(_7r)){return _3T(_4j(_93).a,_7q);}else{return E(_39);}}),_95=E(_92);if(!_95._){return C > 19 ? new F(function(){return _6I(_7K,_8A,_8X,2,_5g,_94);}) : (++C,_6I(_7K,_8A,_8X,2,_5g,_94));}else{return C > 19 ? new F(function(){return _6I(_7K,_8A,_8X,2,_95.a,_94);}) : (++C,_6I(_7K,_8A,_8X,2,_95.a,_94));}},_96=function(_97,_98,_99){return C > 19 ? new F(function(){return _91(_98,_99);}) : (++C,_91(_98,_99));},_9a=function(_9b,_9c){var _9d=new T(function(){if(!E(_7r)){return _3T(_52(_9c).a,_7q);}else{return E(_39);}}),_9e=E(_9b);if(!_9e._){return C > 19 ? new F(function(){return _6I(_7K,_8A,_8X,2,_5g,_9d);}) : (++C,_6I(_7K,_8A,_8X,2,_5g,_9d));}else{return C > 19 ? new F(function(){return _6I(_7K,_8A,_8X,2,_9e.a,_9d);}) : (++C,_6I(_7K,_8A,_8X,2,_9e.a,_9d));}},_9f=function(_9g,_9h,_9i){return C > 19 ? new F(function(){return _9a(_9h,_9i);}) : (++C,_9a(_9h,_9i));},_9j=function(_9k,_9l){var _9m=new T(function(){if(!E(_7r)){return _2B(_52(_9l).a,_7q);}else{return E(_39);}}),_9n=E(_9k);if(!_9n._){return C > 19 ? new F(function(){return _6I(_7K,_8A,_8X,2,__Z,_9m);}) : (++C,_6I(_7K,_8A,_8X,2,__Z,_9m));}else{return C > 19 ? new F(function(){return _6I(_7K,_8A,_8X,2,_9n.a,_9m);}) : (++C,_6I(_7K,_8A,_8X,2,_9n.a,_9m));}},_9o=function(_9p,_9q,_9r){return C > 19 ? new F(function(){return _9j(_9q,_9r);}) : (++C,_9j(_9q,_9r));},_9s=new T1(1,32),_9t=function(_9u,_9v){var _9w=E(_9u);if(!_9w._){return C > 19 ? new F(function(){return _6I(_5h,_5x,_5X,2,_9s,new T(function(){return E(_6h(_9v).c);}));}) : (++C,_6I(_5h,_5x,_5X,2,_9s,new T(function(){return E(_6h(_9v).c);})));}else{return C > 19 ? new F(function(){return _6I(_5h,_5x,_5X,2,_9w.a,new T(function(){return E(_6h(_9v).c);}));}) : (++C,_6I(_5h,_5x,_5X,2,_9w.a,new T(function(){return E(_6h(_9v).c);})));}},_9x=function(_9y,_9z,_9A){return C > 19 ? new F(function(){return _9t(_9z,_9A);}) : (++C,_9t(_9z,_9A));},_9B=function(_9C,_9D){var _9E=E(_9C);if(!_9E._){return C > 19 ? new F(function(){return _6I(_5h,_5x,_5X,2,_5g,new T(function(){return E(_6h(_9D).c);}));}) : (++C,_6I(_5h,_5x,_5X,2,_5g,new T(function(){return E(_6h(_9D).c);})));}else{return C > 19 ? new F(function(){return _6I(_5h,_5x,_5X,2,_9E.a,new T(function(){return E(_6h(_9D).c);}));}) : (++C,_6I(_5h,_5x,_5X,2,_9E.a,new T(function(){return E(_6h(_9D).c);})));}},_9F=function(_9G,_9H,_9I){return C > 19 ? new F(function(){return _9B(_9H,_9I);}) : (++C,_9B(_9H,_9I));},_9J=function(_9K,_9L){return E(_7g(_9K,E(_6h(_9L).b)-1|0).b);},_9M=function(_9N,_9O,_9P){return _9J(E(_9N).b,_9P);},_9Q=function(_9R){return E(E(_9R).a);},_9S=function(_9T,_9U,_9V){return E(_7g(_9Q(_9T),E(_4x(_9V).b)).b);},_9W=function(_9X,_9Y){var _9Z=E(_9X);if(!_9Z._){return C > 19 ? new F(function(){return _6I(_7K,_8A,_8X,4,__Z,new T(function(){return E(_4j(_9Y).a);}));}) : (++C,_6I(_7K,_8A,_8X,4,__Z,new T(function(){return E(_4j(_9Y).a);})));}else{return C > 19 ? new F(function(){return _6I(_7K,_8A,_8X,4,_9Z.a,new T(function(){return E(_4j(_9Y).a);}));}) : (++C,_6I(_7K,_8A,_8X,4,_9Z.a,new T(function(){return E(_4j(_9Y).a);})));}},_a0=function(_a1,_a2,_a3){return C > 19 ? new F(function(){return _9W(_a2,_a3);}) : (++C,_9W(_a2,_a3));},_a4=function(_a5){var _a6=new T(function(){return _41(_a5,new T1(0,2));});return new T2(0,new T(function(){if(!E(_4u)){return _3c(_3G(_2B(_a6,_4t),_2B(_3G(_a6,_4v(E(_4j(_a5).b))),_4t)));}else{return E(_39);}}),new T(function(){if(!E(_4u)){return _3c(_3T(_a6,_4t))+1|0;}else{return E(_39);}}));},_a7=function(_a8,_a9){var _aa=E(_a8);if(!_aa._){return C > 19 ? new F(function(){return _6I(_5h,_5x,_5X,2,_5g,new T(function(){return E(_a4(_a9).a);}));}) : (++C,_6I(_5h,_5x,_5X,2,_5g,new T(function(){return E(_a4(_a9).a);})));}else{return C > 19 ? new F(function(){return _6I(_5h,_5x,_5X,2,_aa.a,new T(function(){return E(_a4(_a9).a);}));}) : (++C,_6I(_5h,_5x,_5X,2,_aa.a,new T(function(){return E(_a4(_a9).a);})));}},_ab=function(_ac,_ad,_ae){return C > 19 ? new F(function(){return _a7(_ad,_ae);}) : (++C,_a7(_ad,_ae));},_af=function(_ag,_ah){var _ai=E(_ag);if(!_ai._){return C > 19 ? new F(function(){return _6I(_5h,_5x,_5X,2,_5g,new T(function(){return E(_52(_ah).b);}));}) : (++C,_6I(_5h,_5x,_5X,2,_5g,new T(function(){return E(_52(_ah).b);})));}else{return C > 19 ? new F(function(){return _6I(_5h,_5x,_5X,2,_ai.a,new T(function(){return E(_52(_ah).b);}));}) : (++C,_6I(_5h,_5x,_5X,2,_ai.a,new T(function(){return E(_52(_ah).b);})));}},_aj=function(_ak,_al,_am){return C > 19 ? new F(function(){return _af(_al,_am);}) : (++C,_af(_al,_am));},_an=function(_ao,_ap){var _aq=E(_ao);if(!_aq._){return C > 19 ? new F(function(){return _6I(_5h,_5x,_5X,2,_5g,new T(function(){return E(_4x(_ap).a);}));}) : (++C,_6I(_5h,_5x,_5X,2,_5g,new T(function(){return E(_4x(_ap).a);})));}else{return C > 19 ? new F(function(){return _6I(_5h,_5x,_5X,2,_aq.a,new T(function(){return E(_4x(_ap).a);}));}) : (++C,_6I(_5h,_5x,_5X,2,_aq.a,new T(function(){return E(_4x(_ap).a);})));}},_ar=function(_as,_at,_au){return C > 19 ? new F(function(){return _an(_at,_au);}) : (++C,_an(_at,_au));},_av=function(_aw,_ax){var _ay=E(_aw);if(!_ay._){return C > 19 ? new F(function(){return _6I(_7K,_8A,_8X,4,__Z,new T(function(){return E(_52(_ax).a);}));}) : (++C,_6I(_7K,_8A,_8X,4,__Z,new T(function(){return E(_52(_ax).a);})));}else{return C > 19 ? new F(function(){return _6I(_7K,_8A,_8X,4,_ay.a,new T(function(){return E(_52(_ax).a);}));}) : (++C,_6I(_7K,_8A,_8X,4,_ay.a,new T(function(){return E(_52(_ax).a);})));}},_az=function(_aA,_aB,_aC){return C > 19 ? new F(function(){return _av(_aB,_aC);}) : (++C,_av(_aB,_aC));},_aD=function(_aE,_aF,_aG){return _aH(_aE,_2n,_aG);},_aI=function(_aJ,_aK,_aG){return _aH(_aJ,_2o,_aG);},_aL=function(_aM,_aN){var _aO=new T(function(){if(!E(_7r)){return _2B(_4j(_aN).a,_7q);}else{return E(_39);}}),_aP=E(_aM);if(!_aP._){return C > 19 ? new F(function(){return _6I(_7K,_8A,_8X,2,__Z,_aO);}) : (++C,_6I(_7K,_8A,_8X,2,__Z,_aO));}else{return C > 19 ? new F(function(){return _6I(_7K,_8A,_8X,2,_aP.a,_aO);}) : (++C,_6I(_7K,_8A,_8X,2,_aP.a,_aO));}},_aQ=function(_aR,_aS,_aT){return C > 19 ? new F(function(){return _aL(_aS,_aT);}) : (++C,_aL(_aS,_aT));},_aU=function(_aV,_aW){return E(_7g(_aV,E(_6h(_aW).b)-1|0).a);},_aX=function(_aY,_aZ,_b0){return _aU(E(_aY).b,_b0);},_b1=function(_b2,_b3,_b4){return E(_7g(_9Q(_b2),E(_4x(_b4).b)).a);},_b5=function(_b6,_b7,_b8){var _b9=E(_b6);return _aH(_b9,_b9.e,_b8);},_ba=new T(function(){return unCStr("	");}),_bb=new T(function(){return unCStr("\n");}),_bc=new T(function(){return unCStr("%");}),_bd=new T1(1,_9s),_be=new T1(1,_5g),_bf=new T1(1,__Z),_bg=function(_bh){return err(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return _2t(9,_bh,__Z);})));},_bi=function(_bj){var _bk=u_towlower(E(_bj));if(_bk>>>0>1114111){return _bg(_bk);}else{return _bk;}},_bl=function(_bm){var _bn=u_towupper(E(_bm));if(_bn>>>0>1114111){return _bg(_bn);}else{return _bn;}},_aH=function(_bo,_bp,_bq){while(1){var _br=(function(_bs,_bt,_bu){var _bv=E(_bt);if(!_bv._){return __Z;}else{var _bw=_bv.b,_bx=E(_bv.a);if(_bx==37){var _by=E(_bw);if(!_by._){return new T2(1,_bx,new T(function(){return _aH(_bs,__Z,_bu);}));}else{var _bz=_by.b,_bA=E(_by.a),_bB=function(_bC){switch(_bA){case 37:return _x(_bc,new T(function(){return _aH(_bs,_bz,_bu);},1));case 65:return _x(_7g(_9Q(_bs),E(_4x(_bu).b)).a,new T(function(){return _aH(_bs,_bz,_bu);},1));case 66:var _bD=E(_bs);return _x(_7g(_bD.b,E(_6h(_bu).b)-1|0).a,new T(function(){return _aH(_bD,_bz,_bu);},1));case 67:return _x(B(_aL(__Z,_bu)),new T(function(){return _aH(_bs,_bz,_bu);},1));case 68:return _x(_aH(_bs,_2o,_bu),new T(function(){return _aH(_bs,_bz,_bu);},1));case 70:return _x(_aH(_bs,_2n,_bu),new T(function(){return _aH(_bs,_bz,_bu);},1));case 71:return _x(B(_6I(_7K,_8A,_8X,4,__Z,new T(function(){return E(_52(_bu).a);}))),new T(function(){return _aH(_bs,_bz,_bu);},1));case 85:return _x(B(_6I(_5h,_5x,_5X,2,_5g,new T(function(){return E(_4x(_bu).a);}))),new T(function(){return _aH(_bs,_bz,_bu);},1));case 86:return _x(B(_6I(_5h,_5x,_5X,2,_5g,new T(function(){return E(_52(_bu).b);}))),new T(function(){return _aH(_bs,_bz,_bu);},1));case 87:return _x(B(_6I(_5h,_5x,_5X,2,_5g,new T(function(){return E(_a4(_bu).a);}))),new T(function(){return _aH(_bs,_bz,_bu);},1));case 89:return _x(B(_6I(_7K,_8A,_8X,4,__Z,new T(function(){return E(_4j(_bu).a);}))),new T(function(){return _aH(_bs,_bz,_bu);},1));case 97:return _x(_7g(_9Q(_bs),E(_4x(_bu).b)).b,new T(function(){return _aH(_bs,_bz,_bu);},1));case 98:var _bE=E(_bs);return _x(_7g(_bE.b,E(_6h(_bu).b)-1|0).b,new T(function(){return _aH(_bE,_bz,_bu);},1));case 100:return _x(B(_6I(_5h,_5x,_5X,2,_5g,new T(function(){return E(_6h(_bu).c);}))),new T(function(){return _aH(_bs,_bz,_bu);},1));case 101:return _x(B(_6I(_5h,_5x,_5X,2,_9s,new T(function(){return E(_6h(_bu).c);}))),new T(function(){return _aH(_bs,_bz,_bu);},1));case 102:return _x(B(_9j(__Z,_bu)),new T(function(){return _aH(_bs,_bz,_bu);},1));case 103:return _x(B(_9a(__Z,_bu)),new T(function(){return _aH(_bs,_bz,_bu);},1));case 104:var _bF=E(_bs);return _x(_7g(_bF.b,E(_6h(_bu).b)-1|0).b,new T(function(){return _aH(_bF,_bz,_bu);},1));case 106:return _x(B(_6I(_5h,_5x,_5X,3,_5g,new T(function(){return E(_4j(_bu).b);}))),new T(function(){return _aH(_bs,_bz,_bu);},1));case 109:return _x(B(_6I(_5h,_5x,_5X,2,_5g,new T(function(){return E(_6h(_bu).b);}))),new T(function(){return _aH(_bs,_bz,_bu);},1));case 110:return _x(_bb,new T(function(){return _aH(_bs,_bz,_bu);},1));case 116:return _x(_ba,new T(function(){return _aH(_bs,_bz,_bu);},1));case 117:return _x(_2t(0,E(_52(_bu).c),__Z),new T(function(){return _aH(_bs,_bz,_bu);},1));case 119:return _x(_2t(0,E(_4x(_bu).b),__Z),new T(function(){return _aH(_bs,_bz,_bu);},1));case 120:var _bG=E(_bs);return _x(_aH(_bG,_bG.e,_bu),new T(function(){return _aH(_bG,_bz,_bu);},1));case 121:return _x(B(_91(__Z,_bu)),new T(function(){return _aH(_bs,_bz,_bu);},1));default:return _aH(_bs,_bz,_bu);}};switch(_bA){case 35:var _bH=E(_bz);if(!_bH._){return _bB(_);}else{var _bI=_bH.b,_bJ=E(_bH.a);switch(_bJ){case 37:var _bK=new T(function(){return _aH(_bs,_bI,_bu);}),_bL=function(_bM){var _bN=E(_bM);return (_bN._==0)?E(_bK):new T2(1,new T(function(){return _bi(_bN.a);}),new T(function(){return _bL(_bN.b);}));};return _bL(_bc);case 110:var _bO=new T(function(){return _aH(_bs,_bI,_bu);}),_bP=function(_bQ){var _bR=E(_bQ);return (_bR._==0)?E(_bO):new T2(1,new T(function(){return _bi(_bR.a);}),new T(function(){return _bP(_bR.b);}));};return _bP(_bb);case 116:var _bS=new T(function(){return _aH(_bs,_bI,_bu);}),_bT=function(_bU){var _bV=E(_bU);return (_bV._==0)?E(_bS):new T2(1,new T(function(){return _bi(_bV.a);}),new T(function(){return _bT(_bV.b);}));};return _bT(_ba);default:var _bW=function(_bX){var _bY=new T(function(){return _aH(_bs,_bI,_bu);}),_bZ=function(_c0){var _c1=E(_c0);return (_c1._==0)?E(_bY):new T2(1,new T(function(){return _bi(_c1.a);}),new T(function(){return _bZ(_c1.b);}));};return _bZ(B(A3(_bX,_bs,__Z,_bu)));};switch(_bJ){case 65:return _bW(_b1);case 66:return _bW(_aX);case 67:return _bW(_aQ);case 68:return _bW(_aI);case 70:return _bW(_aD);case 71:return _bW(_az);case 85:return _bW(_ar);case 86:return _bW(_aj);case 87:return _bW(_ab);case 89:return _bW(_a0);case 97:return _bW(_9S);case 98:return _bW(_9M);case 100:return _bW(_9F);case 101:return _bW(_9x);case 102:return _bW(_9o);case 103:return _bW(_9f);case 104:return _bW(_7m);case 106:return _bW(_74);case 109:return _bW(_6W);case 117:return _bW(_5c);case 119:return _bW(_4A);case 120:return _bW(_b5);case 121:return _bW(_96);default:var _c2=_bs,_c3=_bu;_bo=_c2;_bp=_bI;_bq=_c3;return __continue;}}}break;case 45:var _c4=E(_bz);if(!_c4._){return _bB(_);}else{var _c5=_c4.b;switch(E(_c4.a)){case 37:return _x(_bc,new T(function(){return _aH(_bs,_c5,_bu);},1));case 65:return _x(_7g(_9Q(_bs),E(_4x(_bu).b)).a,new T(function(){return _aH(_bs,_c5,_bu);},1));case 66:var _c6=E(_bs);return _x(_7g(_c6.b,E(_6h(_bu).b)-1|0).a,new T(function(){return _aH(_c6,_c5,_bu);},1));case 67:return _x(B(_aL(_bf,_bu)),new T(function(){return _aH(_bs,_c5,_bu);},1));case 68:return _x(_aH(_bs,_2o,_bu),new T(function(){return _aH(_bs,_c5,_bu);},1));case 70:return _x(_aH(_bs,_2n,_bu),new T(function(){return _aH(_bs,_c5,_bu);},1));case 71:return _x(B(_6I(_7K,_8A,_8X,4,__Z,new T(function(){return E(_52(_bu).a);}))),new T(function(){return _aH(_bs,_c5,_bu);},1));case 85:return _x(B(_6I(_5h,_5x,_5X,2,__Z,new T(function(){return E(_4x(_bu).a);}))),new T(function(){return _aH(_bs,_c5,_bu);},1));case 86:return _x(B(_6I(_5h,_5x,_5X,2,__Z,new T(function(){return E(_52(_bu).b);}))),new T(function(){return _aH(_bs,_c5,_bu);},1));case 87:return _x(B(_6I(_5h,_5x,_5X,2,__Z,new T(function(){return E(_a4(_bu).a);}))),new T(function(){return _aH(_bs,_c5,_bu);},1));case 89:return _x(B(_6I(_7K,_8A,_8X,4,__Z,new T(function(){return E(_4j(_bu).a);}))),new T(function(){return _aH(_bs,_c5,_bu);},1));case 97:return _x(_7g(_9Q(_bs),E(_4x(_bu).b)).b,new T(function(){return _aH(_bs,_c5,_bu);},1));case 98:var _c7=E(_bs);return _x(_7g(_c7.b,E(_6h(_bu).b)-1|0).b,new T(function(){return _aH(_c7,_c5,_bu);},1));case 100:return _x(B(_6I(_5h,_5x,_5X,2,__Z,new T(function(){return E(_6h(_bu).c);}))),new T(function(){return _aH(_bs,_c5,_bu);},1));case 101:return _x(B(_6I(_5h,_5x,_5X,2,__Z,new T(function(){return E(_6h(_bu).c);}))),new T(function(){return _aH(_bs,_c5,_bu);},1));case 102:return _x(B(_9j(_bf,_bu)),new T(function(){return _aH(_bs,_c5,_bu);},1));case 103:return _x(B(_9a(_bf,_bu)),new T(function(){return _aH(_bs,_c5,_bu);},1));case 104:var _c8=E(_bs);return _x(_7g(_c8.b,E(_6h(_bu).b)-1|0).b,new T(function(){return _aH(_c8,_c5,_bu);},1));case 106:return _x(B(_6I(_5h,_5x,_5X,3,__Z,new T(function(){return E(_4j(_bu).b);}))),new T(function(){return _aH(_bs,_c5,_bu);},1));case 109:return _x(B(_6I(_5h,_5x,_5X,2,__Z,new T(function(){return E(_6h(_bu).b);}))),new T(function(){return _aH(_bs,_c5,_bu);},1));case 110:return _x(_bb,new T(function(){return _aH(_bs,_c5,_bu);},1));case 116:return _x(_ba,new T(function(){return _aH(_bs,_c5,_bu);},1));case 117:return _x(_2t(0,E(_52(_bu).c),__Z),new T(function(){return _aH(_bs,_c5,_bu);},1));case 119:return _x(_2t(0,E(_4x(_bu).b),__Z),new T(function(){return _aH(_bs,_c5,_bu);},1));case 120:var _c9=E(_bs);return _x(_aH(_c9,_c9.e,_bu),new T(function(){return _aH(_c9,_c5,_bu);},1));case 121:return _x(B(_91(_bf,_bu)),new T(function(){return _aH(_bs,_c5,_bu);},1));default:var _c2=_bs,_c3=_bu;_bo=_c2;_bp=_c5;_bq=_c3;return __continue;}}break;case 48:var _ca=E(_bz);if(!_ca._){return _bB(_);}else{var _cb=_ca.b;switch(E(_ca.a)){case 37:return _x(_bc,new T(function(){return _aH(_bs,_cb,_bu);},1));case 65:return _x(_7g(_9Q(_bs),E(_4x(_bu).b)).a,new T(function(){return _aH(_bs,_cb,_bu);},1));case 66:var _cc=E(_bs);return _x(_7g(_cc.b,E(_6h(_bu).b)-1|0).a,new T(function(){return _aH(_cc,_cb,_bu);},1));case 67:return _x(B(_aL(_be,_bu)),new T(function(){return _aH(_bs,_cb,_bu);},1));case 68:return _x(_aH(_bs,_2o,_bu),new T(function(){return _aH(_bs,_cb,_bu);},1));case 70:return _x(_aH(_bs,_2n,_bu),new T(function(){return _aH(_bs,_cb,_bu);},1));case 71:return _x(B(_6I(_7K,_8A,_8X,4,_5g,new T(function(){return E(_52(_bu).a);}))),new T(function(){return _aH(_bs,_cb,_bu);},1));case 85:return _x(B(_6I(_5h,_5x,_5X,2,_5g,new T(function(){return E(_4x(_bu).a);}))),new T(function(){return _aH(_bs,_cb,_bu);},1));case 86:return _x(B(_6I(_5h,_5x,_5X,2,_5g,new T(function(){return E(_52(_bu).b);}))),new T(function(){return _aH(_bs,_cb,_bu);},1));case 87:return _x(B(_6I(_5h,_5x,_5X,2,_5g,new T(function(){return E(_a4(_bu).a);}))),new T(function(){return _aH(_bs,_cb,_bu);},1));case 89:return _x(B(_6I(_7K,_8A,_8X,4,_5g,new T(function(){return E(_4j(_bu).a);}))),new T(function(){return _aH(_bs,_cb,_bu);},1));case 97:return _x(_7g(_9Q(_bs),E(_4x(_bu).b)).b,new T(function(){return _aH(_bs,_cb,_bu);},1));case 98:var _cd=E(_bs);return _x(_7g(_cd.b,E(_6h(_bu).b)-1|0).b,new T(function(){return _aH(_cd,_cb,_bu);},1));case 100:return _x(B(_6I(_5h,_5x,_5X,2,_5g,new T(function(){return E(_6h(_bu).c);}))),new T(function(){return _aH(_bs,_cb,_bu);},1));case 101:return _x(B(_6I(_5h,_5x,_5X,2,_5g,new T(function(){return E(_6h(_bu).c);}))),new T(function(){return _aH(_bs,_cb,_bu);},1));case 102:return _x(B(_9j(_be,_bu)),new T(function(){return _aH(_bs,_cb,_bu);},1));case 103:return _x(B(_9a(_be,_bu)),new T(function(){return _aH(_bs,_cb,_bu);},1));case 104:var _ce=E(_bs);return _x(_7g(_ce.b,E(_6h(_bu).b)-1|0).b,new T(function(){return _aH(_ce,_cb,_bu);},1));case 106:return _x(B(_6I(_5h,_5x,_5X,3,_5g,new T(function(){return E(_4j(_bu).b);}))),new T(function(){return _aH(_bs,_cb,_bu);},1));case 109:return _x(B(_6I(_5h,_5x,_5X,2,_5g,new T(function(){return E(_6h(_bu).b);}))),new T(function(){return _aH(_bs,_cb,_bu);},1));case 110:return _x(_bb,new T(function(){return _aH(_bs,_cb,_bu);},1));case 116:return _x(_ba,new T(function(){return _aH(_bs,_cb,_bu);},1));case 117:return _x(_2t(0,E(_52(_bu).c),__Z),new T(function(){return _aH(_bs,_cb,_bu);},1));case 119:return _x(_2t(0,E(_4x(_bu).b),__Z),new T(function(){return _aH(_bs,_cb,_bu);},1));case 120:var _cf=E(_bs);return _x(_aH(_cf,_cf.e,_bu),new T(function(){return _aH(_cf,_cb,_bu);},1));case 121:return _x(B(_91(_be,_bu)),new T(function(){return _aH(_bs,_cb,_bu);},1));default:var _c2=_bs,_c3=_bu;_bo=_c2;_bp=_cb;_bq=_c3;return __continue;}}break;case 94:var _cg=E(_bz);if(!_cg._){return _bB(_);}else{var _ch=_cg.b,_ci=E(_cg.a);switch(_ci){case 37:var _cj=new T(function(){return _aH(_bs,_ch,_bu);}),_ck=function(_cl){var _cm=E(_cl);return (_cm._==0)?E(_cj):new T2(1,new T(function(){return _bl(_cm.a);}),new T(function(){return _ck(_cm.b);}));};return _ck(_bc);case 110:var _cn=new T(function(){return _aH(_bs,_ch,_bu);}),_co=function(_cp){var _cq=E(_cp);return (_cq._==0)?E(_cn):new T2(1,new T(function(){return _bl(_cq.a);}),new T(function(){return _co(_cq.b);}));};return _co(_bb);case 116:var _cr=new T(function(){return _aH(_bs,_ch,_bu);}),_cs=function(_ct){var _cu=E(_ct);return (_cu._==0)?E(_cr):new T2(1,new T(function(){return _bl(_cu.a);}),new T(function(){return _cs(_cu.b);}));};return _cs(_ba);default:var _cv=function(_cw){var _cx=new T(function(){return _aH(_bs,_ch,_bu);}),_cy=function(_cz){var _cA=E(_cz);return (_cA._==0)?E(_cx):new T2(1,new T(function(){return _bl(_cA.a);}),new T(function(){return _cy(_cA.b);}));};return _cy(B(A3(_cw,_bs,__Z,_bu)));};switch(_ci){case 65:return _cv(_b1);case 66:return _cv(_aX);case 67:return _cv(_aQ);case 68:return _cv(_aI);case 70:return _cv(_aD);case 71:return _cv(_az);case 85:return _cv(_ar);case 86:return _cv(_aj);case 87:return _cv(_ab);case 89:return _cv(_a0);case 97:return _cv(_9S);case 98:return _cv(_9M);case 100:return _cv(_9F);case 101:return _cv(_9x);case 102:return _cv(_9o);case 103:return _cv(_9f);case 104:return _cv(_7m);case 106:return _cv(_74);case 109:return _cv(_6W);case 117:return _cv(_5c);case 119:return _cv(_4A);case 120:return _cv(_b5);case 121:return _cv(_96);default:var _c2=_bs,_c3=_bu;_bo=_c2;_bp=_ch;_bq=_c3;return __continue;}}}break;case 95:var _cB=E(_bz);if(!_cB._){return _bB(_);}else{var _cC=_cB.b;switch(E(_cB.a)){case 37:return _x(_bc,new T(function(){return _aH(_bs,_cC,_bu);},1));case 65:return _x(_7g(_9Q(_bs),E(_4x(_bu).b)).a,new T(function(){return _aH(_bs,_cC,_bu);},1));case 66:var _cD=E(_bs);return _x(_7g(_cD.b,E(_6h(_bu).b)-1|0).a,new T(function(){return _aH(_cD,_cC,_bu);},1));case 67:return _x(B(_aL(_bd,_bu)),new T(function(){return _aH(_bs,_cC,_bu);},1));case 68:return _x(_aH(_bs,_2o,_bu),new T(function(){return _aH(_bs,_cC,_bu);},1));case 70:return _x(_aH(_bs,_2n,_bu),new T(function(){return _aH(_bs,_cC,_bu);},1));case 71:return _x(B(_6I(_7K,_8A,_8X,4,_9s,new T(function(){return E(_52(_bu).a);}))),new T(function(){return _aH(_bs,_cC,_bu);},1));case 85:return _x(B(_6I(_5h,_5x,_5X,2,_9s,new T(function(){return E(_4x(_bu).a);}))),new T(function(){return _aH(_bs,_cC,_bu);},1));case 86:return _x(B(_6I(_5h,_5x,_5X,2,_9s,new T(function(){return E(_52(_bu).b);}))),new T(function(){return _aH(_bs,_cC,_bu);},1));case 87:return _x(B(_6I(_5h,_5x,_5X,2,_9s,new T(function(){return E(_a4(_bu).a);}))),new T(function(){return _aH(_bs,_cC,_bu);},1));case 89:return _x(B(_6I(_7K,_8A,_8X,4,_9s,new T(function(){return E(_4j(_bu).a);}))),new T(function(){return _aH(_bs,_cC,_bu);},1));case 97:return _x(_7g(_9Q(_bs),E(_4x(_bu).b)).b,new T(function(){return _aH(_bs,_cC,_bu);},1));case 98:var _cE=E(_bs);return _x(_7g(_cE.b,E(_6h(_bu).b)-1|0).b,new T(function(){return _aH(_cE,_cC,_bu);},1));case 100:return _x(B(_6I(_5h,_5x,_5X,2,_9s,new T(function(){return E(_6h(_bu).c);}))),new T(function(){return _aH(_bs,_cC,_bu);},1));case 101:return _x(B(_6I(_5h,_5x,_5X,2,_9s,new T(function(){return E(_6h(_bu).c);}))),new T(function(){return _aH(_bs,_cC,_bu);},1));case 102:return _x(B(_9j(_bd,_bu)),new T(function(){return _aH(_bs,_cC,_bu);},1));case 103:return _x(B(_9a(_bd,_bu)),new T(function(){return _aH(_bs,_cC,_bu);},1));case 104:var _cF=E(_bs);return _x(_7g(_cF.b,E(_6h(_bu).b)-1|0).b,new T(function(){return _aH(_cF,_cC,_bu);},1));case 106:return _x(B(_6I(_5h,_5x,_5X,3,_9s,new T(function(){return E(_4j(_bu).b);}))),new T(function(){return _aH(_bs,_cC,_bu);},1));case 109:return _x(B(_6I(_5h,_5x,_5X,2,_9s,new T(function(){return E(_6h(_bu).b);}))),new T(function(){return _aH(_bs,_cC,_bu);},1));case 110:return _x(_bb,new T(function(){return _aH(_bs,_cC,_bu);},1));case 116:return _x(_ba,new T(function(){return _aH(_bs,_cC,_bu);},1));case 117:return _x(_2t(0,E(_52(_bu).c),__Z),new T(function(){return _aH(_bs,_cC,_bu);},1));case 119:return _x(_2t(0,E(_4x(_bu).b),__Z),new T(function(){return _aH(_bs,_cC,_bu);},1));case 120:var _cG=E(_bs);return _x(_aH(_cG,_cG.e,_bu),new T(function(){return _aH(_cG,_cC,_bu);},1));case 121:return _x(B(_91(_bd,_bu)),new T(function(){return _aH(_bs,_cC,_bu);},1));default:var _c2=_bs,_c3=_bu;_bo=_c2;_bp=_cC;_bq=_c3;return __continue;}}break;default:return _bB(_);}}}else{return new T2(1,_bx,new T(function(){return _aH(_bs,_bw,_bu);}));}}})(_bo,_bp,_bq);if(_br!=__continue){return _br;}}},_cH=function(_cI){return (E(_cI)==46)?false:true;},_cJ=function(_cK){return E(E(_cK).a);},_cL=function(_cM,_cN,_cO){return E(_7g(_9Q(_cM),E(_4x(new T(function(){return _cJ(_cO);})).b)).b);},_cP=new T(function(){return unCStr("%H:%M:%S");}),_cQ=new T(function(){return unCStr("%H:%M");}),_cR=function(_cS,_cT,_cU){return E(_7g(_9Q(_cS),E(_4x(new T(function(){return _cJ(_cU);})).b)).a);},_cV=function(_cW,_cX){var _cY=E(_cW);if(!_cY._){return C > 19 ? new F(function(){return _6I(_5h,_5x,_5X,2,_9s,new T(function(){return E(E(_cX).a);}));}) : (++C,_6I(_5h,_5x,_5X,2,_9s,new T(function(){return E(E(_cX).a);})));}else{return C > 19 ? new F(function(){return _6I(_5h,_5x,_5X,2,_cY.a,new T(function(){return E(E(_cX).a);}));}) : (++C,_6I(_5h,_5x,_5X,2,_cY.a,new T(function(){return E(E(_cX).a);})));}},_cZ=function(_d0,_d1,_d2){return C > 19 ? new F(function(){return _cV(_d1,_d2);}) : (++C,_cV(_d1,_d2));},_d3=function(_d4,_d5,_d6){var _d7=E(_d4);return _d8(_d7,_d7.f,_d6);},_d9=function(_da,_db,_aG){return _d8(_da,_cP,_aG);},_dc=function(_dd,_de){while(1){var _df=E(_dd);if(!_df._){var _dg=_df.a,_dh=E(_de);if(!_dh._){return new T1(0,(_dg>>>0|_dh.a>>>0)>>>0&4294967295);}else{_dd=new T1(1,I_fromInt(_dg));_de=_dh;continue;}}else{var _di=E(_de);if(!_di._){_dd=_df;_de=new T1(1,I_fromInt(_di.a));continue;}else{return new T1(1,I_or(_df.a,_di.a));}}}},_dj=function(_dk,_dl){while(1){var _dm=E(_dk);if(!_dm._){_dk=new T1(1,I_fromInt(_dm.a));continue;}else{return new T1(1,I_shiftLeft(_dm.a,_dl));}}},_dn=function(_do){var _dp=E(_do);if(!_dp._){return E(_7D);}else{return _dc(new T1(0,E(_dp.a)),_dj(_dn(_dp.b),31));}},_dq=function(_dr,_ds){if(!E(_dr)){return _7z(_dn(_ds));}else{return _dn(_ds);}},_dt=new T(function(){return _dq(true,new T2(1,1420103680,new T2(1,465,__Z)));}),_du=function(_dv,_dw){if(_dv<=_dw){var _dx=function(_dy){return new T2(1,_dy,new T(function(){if(_dy!=_dw){return _dx(_dy+1|0);}else{return __Z;}}));};return _dx(_dv);}else{return __Z;}},_dz=function(_dA){return _du(E(_dA),2147483647);},_dB=function(_dC,_dD,_dE){if(_dE<=_dD){var _dF=new T(function(){var _dG=_dD-_dC|0,_dH=function(_dI){return (_dI>=(_dE-_dG|0))?new T2(1,_dI,new T(function(){return _dH(_dI+_dG|0);})):new T2(1,_dI,__Z);};return _dH(_dD);});return new T2(1,_dC,_dF);}else{return (_dE<=_dC)?new T2(1,_dC,__Z):__Z;}},_dJ=function(_dK,_dL,_dM){if(_dM>=_dL){var _dN=new T(function(){var _dO=_dL-_dK|0,_dP=function(_dQ){return (_dQ<=(_dM-_dO|0))?new T2(1,_dQ,new T(function(){return _dP(_dQ+_dO|0);})):new T2(1,_dQ,__Z);};return _dP(_dL);});return new T2(1,_dK,_dN);}else{return (_dM>=_dK)?new T2(1,_dK,__Z):__Z;}},_dR=function(_dS,_dT){if(_dT<_dS){return _dB(_dS,_dT,-2147483648);}else{return _dJ(_dS,_dT,2147483647);}},_dU=function(_dV,_dW){return _dR(E(_dV),E(_dW));},_dX=function(_dY,_dZ,_e0){if(_dZ<_dY){return _dB(_dY,_dZ,_e0);}else{return _dJ(_dY,_dZ,_e0);}},_e1=function(_e2,_e3,_e4){return _dX(E(_e2),E(_e3),E(_e4));},_e5=function(_e6,_e7){return _du(E(_e6),E(_e7));},_e8=function(_e9){return E(_e9);},_ea=new T(function(){return err(new T(function(){return unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound");}));}),_eb=function(_ec){var _ed=E(_ec);return (_ed==(-2147483648))?E(_ea):_ed-1|0;},_ee=new T(function(){return err(new T(function(){return unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound");}));}),_ef=function(_eg){var _eh=E(_eg);return (_eh==2147483647)?E(_ee):_eh+1|0;},_ei=new T(function(){return die(new T(function(){return _35(0);}));}),_ej=function(_ek,_el){var _em=E(_el);switch(_em){case -1:var _en=E(_ek);if(_en==(-2147483648)){return E(_ei);}else{return _2y(_en,-1);}break;case 0:return E(_39);default:return _2y(_ek,_em);}},_eo=function(_ep,_eq){return _ej(E(_ep),E(_eq));},_er=new T2(0,_ei,0),_es=function(_et,_eu){var _ev=E(_et),_ew=E(_eu);switch(_ew){case -1:if(_ev==(-2147483648)){return E(_er);}else{if(_ev<=0){if(_ev>=0){var _ex=quotRemI(_ev,-1);return new T2(0,_ex.a,_ex.b);}else{var _ey=quotRemI(_ev,-1);return new T2(0,_ey.a,_ey.b);}}else{var _ez=quotRemI(_ev-1|0,-1);return new T2(0,_ez.a-1|0,(_ez.b+(-1)|0)+1|0);}}break;case 0:return E(_39);default:if(_ev<=0){if(_ev>=0){var _eA=quotRemI(_ev,_ew);return new T2(0,_eA.a,_eA.b);}else{if(_ew<=0){var _eB=quotRemI(_ev,_ew);return new T2(0,_eB.a,_eB.b);}else{var _eC=quotRemI(_ev+1|0,_ew);return new T2(0,_eC.a-1|0,(_eC.b+_ew|0)-1|0);}}}else{if(_ew>=0){if(_ev>=0){var _eD=quotRemI(_ev,_ew);return new T2(0,_eD.a,_eD.b);}else{if(_ew<=0){var _eE=quotRemI(_ev,_ew);return new T2(0,_eE.a,_eE.b);}else{var _eF=quotRemI(_ev+1|0,_ew);return new T2(0,_eF.a-1|0,(_eF.b+_ew|0)-1|0);}}}else{var _eG=quotRemI(_ev-1|0,_ew);return new T2(0,_eG.a-1|0,(_eG.b+_ew|0)+1|0);}}}},_eH=function(_eI,_eJ){var _eK=E(_eJ);switch(_eK){case -1:return 0;case 0:return E(_39);default:return _3P(E(_eI),_eK);}},_eL=function(_eM,_eN){var _eO=E(_eM),_eP=E(_eN);switch(_eP){case -1:if(_eO==(-2147483648)){return E(_ei);}else{return quot(_eO,-1);}break;case 0:return E(_39);default:return quot(_eO,_eP);}},_eQ=function(_eR,_eS){var _eT=E(_eR),_eU=E(_eS);switch(_eU){case -1:if(_eT==(-2147483648)){return E(_er);}else{var _eV=quotRemI(_eT,-1);return new T2(0,_eV.a,_eV.b);}break;case 0:return E(_39);default:var _eW=quotRemI(_eT,_eU);return new T2(0,_eW.a,_eW.b);}},_eX=function(_eY,_eZ){var _f0=E(_eZ);switch(_f0){case -1:return 0;case 0:return E(_39);default:return E(_eY)%_f0;}},_f1=function(_f2){return _4v(E(_f2));},_f3=function(_f4){return new T2(0,E(_4v(E(_f4))),E(_29));},_f5=new T1(0,0),_f6=function(_f7,_f8){while(1){var _f9=E(_f7);if(!_f9._){var _fa=E(_f9.a);if(_fa==(-2147483648)){_f7=new T1(1,I_fromInt(-2147483648));continue;}else{var _fb=E(_f8);if(!_fb._){return new T1(0,_fa%_fb.a);}else{_f7=new T1(1,I_fromInt(_fa));_f8=_fb;continue;}}}else{var _fc=_f9.a,_fd=E(_f8);return (_fd._==0)?new T1(1,I_rem(_fc,I_fromInt(_fd.a))):new T1(1,I_rem(_fc,_fd.a));}}},_fe=function(_ff,_fg){if(!_3t(_fg,_f5)){return _f6(_ff,_fg);}else{return E(_39);}},_fh=function(_fi,_fj){while(1){if(!_3t(_fj,_f5)){var _fk=_fj,_fl=_fe(_fi,_fj);_fi=_fk;_fj=_fl;continue;}else{return E(_fi);}}},_fm=function(_fn,_fo){while(1){var _fp=E(_fn);if(!_fp._){var _fq=E(_fp.a);if(_fq==(-2147483648)){_fn=new T1(1,I_fromInt(-2147483648));continue;}else{var _fr=E(_fo);if(!_fr._){return new T1(0,quot(_fq,_fr.a));}else{_fn=new T1(1,I_fromInt(_fq));_fo=_fr;continue;}}}else{var _fs=_fp.a,_ft=E(_fo);return (_ft._==0)?new T1(0,I_toInt(I_quot(_fs,I_fromInt(_ft.a)))):new T1(1,I_quot(_fs,_ft.a));}}},_fu=new T(function(){return die(new T(function(){return _35(5);}));}),_fv=function(_fw,_fx){if(!_3t(_fx,_f5)){var _fy=_fh(_7u(_fw),_7u(_fx));return (!_3t(_fy,_f5))?new T2(0,_fm(_fw,_fy),_fm(_fx,_fy)):E(_39);}else{return E(_fu);}},_fz=function(_fA,_fB,_fC,_fD){var _fE=_4b(_fB,_fC);return _fv(_4b(_4b(_fA,_fD),_7F(_fE)),_7u(_fE));},_fF=function(_fG){return E(E(_fG).a);},_fH=function(_fI){return E(E(_fI).a);},_fJ=function(_fK,_fL){while(1){var _fM=E(_fK);if(!_fM._){var _fN=E(_fM.a);if(_fN==(-2147483648)){_fK=new T1(1,I_fromInt(-2147483648));continue;}else{var _fO=E(_fL);if(!_fO._){var _fP=_fO.a;return new T2(0,new T1(0,quot(_fN,_fP)),new T1(0,_fN%_fP));}else{_fK=new T1(1,I_fromInt(_fN));_fL=_fO;continue;}}}else{var _fQ=E(_fL);if(!_fQ._){_fK=_fM;_fL=new T1(1,I_fromInt(_fQ.a));continue;}else{var _fR=I_quotRem(_fM.a,_fQ.a);return new T2(0,new T1(1,_fR.a),new T1(1,_fR.b));}}}},_fS=function(_fT,_fU,_fV){var _fW=new T(function(){if(!_3t(_fV,_f5)){var _fX=_fJ(_fU,_fV);return new T2(0,_fX.a,_fX.b);}else{return E(_39);}}),_fY=new T(function(){return B(A2(_6C,_fH(_fF(_fT)),new T(function(){return E(E(_fW).a);})));});return new T2(0,_fY,new T(function(){return new T2(0,E(E(_fW).b),E(_fV));}));},_fZ=function(_g0,_g1){var _g2=new T(function(){var _g3=_fz(E(_g1).c,_29,_dt,_29);return E(_fS({_:0,a:new T3(0,_5h,_5x,_f3),b:{_:0,a:_ef,b:_eb,c:_e8,d:_e8,e:_dz,f:_dU,g:_e5,h:_e1},c:_eL,d:_eX,e:_eo,f:_eH,g:_eQ,h:_es,i:_f1},_g3.a,_g3.b).a);}),_g4=E(_g0);if(!_g4._){return C > 19 ? new F(function(){return _6I(_5h,_5x,_5X,2,_5g,_g2);}) : (++C,_6I(_5h,_5x,_5X,2,_5g,_g2));}else{return C > 19 ? new F(function(){return _6I(_5h,_5x,_5X,2,_g4.a,_g2);}) : (++C,_6I(_5h,_5x,_5X,2,_g4.a,_g2));}},_g5=function(_g6,_g7,_g8){return C > 19 ? new F(function(){return _fZ(_g7,_g8);}) : (++C,_fZ(_g7,_g8));},_g9=function(_ga,_gb,_aG){return _d8(_ga,_cQ,_aG);},_gc=function(_gd,_ge,_gf){var _gg=E(_gd);return _d8(_gg,_gg.g,_gf);},_gh=function(_gi){return E(_dt);},_gj=function(_gk,_gl){while(1){var _gm=E(_gl);if(!_gm._){return __Z;}else{if(!B(A1(_gk,_gm.a))){return _gm;}else{_gl=_gm.b;continue;}}}},_gn=new T1(0,1),_go=new T1(0,0),_gp=new T1(0,10),_gq=function(_gr,_gs,_gt){while(1){if(!(_gs%2)){var _gu=_4b(_gr,_gr),_gv=quot(_gs,2);_gr=_gu;_gs=_gv;continue;}else{var _gw=E(_gs);if(_gw==1){return _4b(_gr,_gt);}else{var _gu=_4b(_gr,_gr),_gx=_4b(_gr,_gt);_gr=_gu;_gs=quot(_gw-1|0,2);_gt=_gx;continue;}}}},_gy=function(_gz,_gA){while(1){if(!(_gA%2)){var _gB=_4b(_gz,_gz),_gC=quot(_gA,2);_gz=_gB;_gA=_gC;continue;}else{var _gD=E(_gA);if(_gD==1){return E(_gz);}else{return _gq(_4b(_gz,_gz),quot(_gD-1|0,2),_gz);}}}},_gE=new T(function(){return err(new T(function(){return unCStr("Negative exponent");}));}),_gF=new T(function(){return _3t(_gp,_go);}),_gG=function(_gH){while(1){if(!_3t(_gH,_go)){if(!E(_gF)){if(!_3t(_3T(_gH,_gp),_go)){return C > 19 ? new F(function(){return _8L(_gH);}) : (++C,_8L(_gH));}else{var _gI=_2B(_gH,_gp);_gH=_gI;continue;}}else{return E(_39);}}else{return __Z;}}},_gJ=function(_gK){var _gL=E(_gK);if(!_gL._){return _gL.a;}else{return I_toNumber(_gL.a);}},_gM=function(_gN,_gO,_gP){if(!_8s(_gP,_go)){var _gQ=B(A1(_gN,_gP));if(!_3t(_gQ,_go)){var _gR=_4O(_gP,_gQ),_gS=_gR.b,_gT=new T(function(){var _gU=Math.log(_gJ(_gQ))/Math.log(10),_gV=_gU&4294967295,_gW=function(_gX){if(_gX>=0){var _gY=E(_gX);if(!_gY){var _gZ=_2B(_3G(_41(_4b(_gS,_29),_gQ),_gn),_gQ);}else{var _gZ=_2B(_3G(_41(_4b(_gS,_gy(_gp,_gY)),_gQ),_gn),_gQ);}var _h0=function(_h1){var _h2=_8H(0,_gZ,__Z),_h3=_gX-_6o(_h2,0)|0;if(0>=_h3){if(!E(_gO)){return E(_h2);}else{return C > 19 ? new F(function(){return _gG(_gZ);}) : (++C,_gG(_gZ));}}else{var _h4=new T(function(){if(!E(_gO)){return E(_h2);}else{return B(_gG(_gZ));}}),_h5=function(_h6){var _h7=E(_h6);return (_h7==1)?E(new T2(1,48,_h4)):new T2(1,48,new T(function(){return _h5(_h7-1|0);}));};return _h5(_h3);}};if(!E(_gO)){var _h8=B(_h0(_));return (_h8._==0)?__Z:new T2(1,46,_h8);}else{if(!_3t(_gZ,_go)){var _h9=B(_h0(_));return (_h9._==0)?__Z:new T2(1,46,_h9);}else{return __Z;}}}else{return E(_gE);}};if(_gV>=_gU){return _gW(_gV);}else{return _gW(_gV+1|0);}},1);return _x(_8H(0,_gR.a,__Z),_gT);}else{return E(_39);}}else{return unAppCStr("-",new T(function(){return _gM(_gN,_gO,_7z(_gP));}));}},_ha=function(_hb){return E(E(_hb).c);},_hc=function(_hd,_he,_hf){return _gj(_cH,_gM(_gh,true,_ha(_hf)));},_hg=function(_hh,_hi){var _hj=E(_hi);return (_hj._==0)?__Z:new T2(1,new T(function(){return B(A1(_hh,_hj.a));}),new T(function(){return _hg(_hh,_hj.b);}));},_hk=function(_hl,_hm,_hn){if(_hn>=12){return _hg(_bi,_hm);}else{return _hg(_bi,_hl);}},_ho=function(_hp,_hq,_hr){var _hs=E(E(_hp).c);return _hk(_hs.a,_hs.b,E(E(_hr).a));},_ht=function(_hu,_hv){var _hw=E(_hu);if(!_hw._){return C > 19 ? new F(function(){return _6I(_5h,_5x,_5X,2,_5g,new T(function(){return E(E(_hv).b);}));}) : (++C,_6I(_5h,_5x,_5X,2,_5g,new T(function(){return E(E(_hv).b);})));}else{return C > 19 ? new F(function(){return _6I(_5h,_5x,_5X,2,_hw.a,new T(function(){return E(E(_hv).b);}));}) : (++C,_6I(_5h,_5x,_5X,2,_hw.a,new T(function(){return E(E(_hv).b);})));}},_hx=function(_hy,_hz,_hA){return C > 19 ? new F(function(){return _ht(_hz,_hA);}) : (++C,_ht(_hz,_hA));},_hB=function(_hC,_hD){var _hE=new T(function(){return _3P(E(E(_hD).a)-1|0,12)+1|0;}),_hF=E(_hC);if(!_hF._){return C > 19 ? new F(function(){return _6I(_5h,_5x,_5X,2,_5g,_hE);}) : (++C,_6I(_5h,_5x,_5X,2,_5g,_hE));}else{return C > 19 ? new F(function(){return _6I(_5h,_5x,_5X,2,_hF.a,_hE);}) : (++C,_6I(_5h,_5x,_5X,2,_hF.a,_hE));}},_hG=function(_hH,_hI,_hJ){return C > 19 ? new F(function(){return _hB(_hI,_hJ);}) : (++C,_hB(_hI,_hJ));},_hK=function(_hL,_hM){var _hN=E(_hL);if(!_hN._){return C > 19 ? new F(function(){return _6I(_5h,_5x,_5X,2,_5g,new T(function(){return E(E(_hM).a);}));}) : (++C,_6I(_5h,_5x,_5X,2,_5g,new T(function(){return E(E(_hM).a);})));}else{return C > 19 ? new F(function(){return _6I(_5h,_5x,_5X,2,_hN.a,new T(function(){return E(E(_hM).a);}));}) : (++C,_6I(_5h,_5x,_5X,2,_hN.a,new T(function(){return E(E(_hM).a);})));}},_hO=function(_hP,_hQ,_hR){return C > 19 ? new F(function(){return _hK(_hQ,_hR);}) : (++C,_hK(_hQ,_hR));},_hS=function(_hT,_hU){while(1){var _hV=E(_hU);if(!_hV._){return __Z;}else{var _hW=_hV.b,_hX=E(_hT);if(_hX==1){return E(_hW);}else{_hT=_hX-1|0;_hU=_hW;continue;}}}},_hY=function(_hZ){return _hS(1,_gj(_cH,_gM(_gh,false,_hZ)));},_i0=function(_i1,_i2,_i3){return _hY(E(_i3).c);},_i4=function(_i5,_i6,_i7){return (E(E(_i7).a)>=12)?E(E(E(_i5).c).b):E(E(E(_i5).c).a);},_i8=function(_i9,_ia){var _ib=new T(function(){return _3P(E(E(_ia).a)-1|0,12)+1|0;}),_ic=E(_i9);if(!_ic._){return C > 19 ? new F(function(){return _6I(_5h,_5x,_5X,2,_9s,_ib);}) : (++C,_6I(_5h,_5x,_5X,2,_9s,_ib));}else{return C > 19 ? new F(function(){return _6I(_5h,_5x,_5X,2,_ic.a,_ib);}) : (++C,_6I(_5h,_5x,_5X,2,_ic.a,_ib));}},_id=function(_ie,_if,_ig){return C > 19 ? new F(function(){return _i8(_if,_ig);}) : (++C,_i8(_if,_ig));},_d8=function(_ih,_ii,_ij){while(1){var _ik=(function(_il,_im,_in){var _io=E(_im);if(!_io._){return __Z;}else{var _ip=_io.b,_iq=E(_io.a);if(_iq==37){var _ir=E(_ip);if(!_ir._){return new T2(1,_iq,new T(function(){return _d8(_il,__Z,_in);}));}else{var _is=_ir.b,_it=E(_ir.a),_iu=function(_iv){switch(_it){case 37:return _x(_bc,new T(function(){return _d8(_il,_is,_in);},1));case 72:return _x(B(_6I(_5h,_5x,_5X,2,_5g,new T(function(){return E(E(_in).a);}))),new T(function(){return _d8(_il,_is,_in);},1));case 73:return _x(B(_hB(__Z,_in)),new T(function(){return _d8(_il,_is,_in);},1));case 77:return _x(B(_6I(_5h,_5x,_5X,2,_5g,new T(function(){return E(E(_in).b);}))),new T(function(){return _d8(_il,_is,_in);},1));case 80:var _iw=E(_il),_ix=E(_iw.c),_iy=E(_in);if(E(_iy.a)>=12){return _x(_hg(_bi,_ix.b),new T(function(){return _d8(_iw,_is,_iy);},1));}else{return _x(_hg(_bi,_ix.a),new T(function(){return _d8(_iw,_is,_iy);},1));}break;case 81:var _iz=E(_in);return _x(_gj(_cH,_gM(_gh,true,_iz.c)),new T(function(){return _d8(_il,_is,_iz);},1));case 82:return _x(_d8(_il,_cQ,_in),new T(function(){return _d8(_il,_is,_in);},1));case 83:return _x(B(_fZ(__Z,_in)),new T(function(){return _d8(_il,_is,_in);},1));case 84:return _x(_d8(_il,_cP,_in),new T(function(){return _d8(_il,_is,_in);},1));case 88:var _iA=E(_il);return _x(_d8(_iA,_iA.f,_in),new T(function(){return _d8(_iA,_is,_in);},1));case 107:return _x(B(_6I(_5h,_5x,_5X,2,_9s,new T(function(){return E(E(_in).a);}))),new T(function(){return _d8(_il,_is,_in);},1));case 108:return _x(B(_i8(__Z,_in)),new T(function(){return _d8(_il,_is,_in);},1));case 110:return _x(_bb,new T(function(){return _d8(_il,_is,_in);},1));case 112:var _iB=E(_in);if(E(_iB.a)>=12){var _iC=E(_il);return _x(E(_iC.c).b,new T(function(){return _d8(_iC,_is,_iB);},1));}else{var _iD=E(_il);return _x(E(_iD.c).a,new T(function(){return _d8(_iD,_is,_iB);},1));}break;case 113:var _iE=E(_in);return _x(_hY(_iE.c),new T(function(){return _d8(_il,_is,_iE);},1));case 114:var _iF=E(_il);return _x(_d8(_iF,_iF.g,_in),new T(function(){return _d8(_iF,_is,_in);},1));case 116:return _x(_ba,new T(function(){return _d8(_il,_is,_in);},1));default:return _d8(_il,_is,_in);}};switch(_it){case 35:var _iG=E(_is);if(!_iG._){return _iu(_);}else{var _iH=_iG.b,_iI=E(_iG.a);switch(_iI){case 37:var _iJ=new T(function(){return _d8(_il,_iH,_in);}),_iK=function(_iL){var _iM=E(_iL);return (_iM._==0)?E(_iJ):new T2(1,new T(function(){return _bi(_iM.a);}),new T(function(){return _iK(_iM.b);}));};return _iK(_bc);case 110:var _iN=new T(function(){return _d8(_il,_iH,_in);}),_iO=function(_iP){var _iQ=E(_iP);return (_iQ._==0)?E(_iN):new T2(1,new T(function(){return _bi(_iQ.a);}),new T(function(){return _iO(_iQ.b);}));};return _iO(_bb);case 116:var _iR=new T(function(){return _d8(_il,_iH,_in);}),_iS=function(_iT){var _iU=E(_iT);return (_iU._==0)?E(_iR):new T2(1,new T(function(){return _bi(_iU.a);}),new T(function(){return _iS(_iU.b);}));};return _iS(_ba);default:var _iV=function(_iW){var _iX=new T(function(){return _d8(_il,_iH,_in);}),_iY=function(_iZ){var _j0=E(_iZ);return (_j0._==0)?E(_iX):new T2(1,new T(function(){return _bi(_j0.a);}),new T(function(){return _iY(_j0.b);}));};return _iY(B(A3(_iW,_il,__Z,_in)));};switch(_iI){case 72:return _iV(_hO);case 73:return _iV(_hG);case 77:return _iV(_hx);case 80:return _iV(_ho);case 81:return _iV(_hc);case 82:return _iV(_g9);case 83:return _iV(_g5);case 84:return _iV(_d9);case 88:return _iV(_d3);case 107:return _iV(_cZ);case 108:return _iV(_id);case 112:return _iV(_i4);case 113:return _iV(_i0);case 114:return _iV(_gc);default:var _j1=_il,_j2=_in;_ih=_j1;_ii=_iH;_ij=_j2;return __continue;}}}break;case 45:var _j3=E(_is);if(!_j3._){return _iu(_);}else{var _j4=_j3.b;switch(E(_j3.a)){case 37:return _x(_bc,new T(function(){return _d8(_il,_j4,_in);},1));case 72:return _x(B(_6I(_5h,_5x,_5X,2,__Z,new T(function(){return E(E(_in).a);}))),new T(function(){return _d8(_il,_j4,_in);},1));case 73:return _x(B(_hB(_bf,_in)),new T(function(){return _d8(_il,_j4,_in);},1));case 77:return _x(B(_6I(_5h,_5x,_5X,2,__Z,new T(function(){return E(E(_in).b);}))),new T(function(){return _d8(_il,_j4,_in);},1));case 80:var _j5=E(_il),_j6=E(_j5.c),_j7=E(_in);if(E(_j7.a)>=12){return _x(_hg(_bi,_j6.b),new T(function(){return _d8(_j5,_j4,_j7);},1));}else{return _x(_hg(_bi,_j6.a),new T(function(){return _d8(_j5,_j4,_j7);},1));}break;case 81:var _j8=E(_in);return _x(_gj(_cH,_gM(_gh,true,_j8.c)),new T(function(){return _d8(_il,_j4,_j8);},1));case 82:return _x(_d8(_il,_cQ,_in),new T(function(){return _d8(_il,_j4,_in);},1));case 83:return _x(B(_fZ(_bf,_in)),new T(function(){return _d8(_il,_j4,_in);},1));case 84:return _x(_d8(_il,_cP,_in),new T(function(){return _d8(_il,_j4,_in);},1));case 88:var _j9=E(_il);return _x(_d8(_j9,_j9.f,_in),new T(function(){return _d8(_j9,_j4,_in);},1));case 107:return _x(B(_6I(_5h,_5x,_5X,2,__Z,new T(function(){return E(E(_in).a);}))),new T(function(){return _d8(_il,_j4,_in);},1));case 108:return _x(B(_i8(_bf,_in)),new T(function(){return _d8(_il,_j4,_in);},1));case 110:return _x(_bb,new T(function(){return _d8(_il,_j4,_in);},1));case 112:var _ja=E(_in);if(E(_ja.a)>=12){var _jb=E(_il);return _x(E(_jb.c).b,new T(function(){return _d8(_jb,_j4,_ja);},1));}else{var _jc=E(_il);return _x(E(_jc.c).a,new T(function(){return _d8(_jc,_j4,_ja);},1));}break;case 113:var _jd=E(_in);return _x(_hY(_jd.c),new T(function(){return _d8(_il,_j4,_jd);},1));case 114:var _je=E(_il);return _x(_d8(_je,_je.g,_in),new T(function(){return _d8(_je,_j4,_in);},1));case 116:return _x(_ba,new T(function(){return _d8(_il,_j4,_in);},1));default:var _j1=_il,_j2=_in;_ih=_j1;_ii=_j4;_ij=_j2;return __continue;}}break;case 48:var _jf=E(_is);if(!_jf._){return _iu(_);}else{var _jg=_jf.b;switch(E(_jf.a)){case 37:return _x(_bc,new T(function(){return _d8(_il,_jg,_in);},1));case 72:return _x(B(_6I(_5h,_5x,_5X,2,_5g,new T(function(){return E(E(_in).a);}))),new T(function(){return _d8(_il,_jg,_in);},1));case 73:return _x(B(_hB(_be,_in)),new T(function(){return _d8(_il,_jg,_in);},1));case 77:return _x(B(_6I(_5h,_5x,_5X,2,_5g,new T(function(){return E(E(_in).b);}))),new T(function(){return _d8(_il,_jg,_in);},1));case 80:var _jh=E(_il),_ji=E(_jh.c),_jj=E(_in);if(E(_jj.a)>=12){return _x(_hg(_bi,_ji.b),new T(function(){return _d8(_jh,_jg,_jj);},1));}else{return _x(_hg(_bi,_ji.a),new T(function(){return _d8(_jh,_jg,_jj);},1));}break;case 81:var _jk=E(_in);return _x(_gj(_cH,_gM(_gh,true,_jk.c)),new T(function(){return _d8(_il,_jg,_jk);},1));case 82:return _x(_d8(_il,_cQ,_in),new T(function(){return _d8(_il,_jg,_in);},1));case 83:return _x(B(_fZ(_be,_in)),new T(function(){return _d8(_il,_jg,_in);},1));case 84:return _x(_d8(_il,_cP,_in),new T(function(){return _d8(_il,_jg,_in);},1));case 88:var _jl=E(_il);return _x(_d8(_jl,_jl.f,_in),new T(function(){return _d8(_jl,_jg,_in);},1));case 107:return _x(B(_6I(_5h,_5x,_5X,2,_5g,new T(function(){return E(E(_in).a);}))),new T(function(){return _d8(_il,_jg,_in);},1));case 108:return _x(B(_i8(_be,_in)),new T(function(){return _d8(_il,_jg,_in);},1));case 110:return _x(_bb,new T(function(){return _d8(_il,_jg,_in);},1));case 112:var _jm=E(_in);if(E(_jm.a)>=12){var _jn=E(_il);return _x(E(_jn.c).b,new T(function(){return _d8(_jn,_jg,_jm);},1));}else{var _jo=E(_il);return _x(E(_jo.c).a,new T(function(){return _d8(_jo,_jg,_jm);},1));}break;case 113:var _jp=E(_in);return _x(_hY(_jp.c),new T(function(){return _d8(_il,_jg,_jp);},1));case 114:var _jq=E(_il);return _x(_d8(_jq,_jq.g,_in),new T(function(){return _d8(_jq,_jg,_in);},1));case 116:return _x(_ba,new T(function(){return _d8(_il,_jg,_in);},1));default:var _j1=_il,_j2=_in;_ih=_j1;_ii=_jg;_ij=_j2;return __continue;}}break;case 94:var _jr=E(_is);if(!_jr._){return _iu(_);}else{var _js=_jr.b,_jt=E(_jr.a);switch(_jt){case 37:var _ju=new T(function(){return _d8(_il,_js,_in);}),_jv=function(_jw){var _jx=E(_jw);return (_jx._==0)?E(_ju):new T2(1,new T(function(){return _bl(_jx.a);}),new T(function(){return _jv(_jx.b);}));};return _jv(_bc);case 110:var _jy=new T(function(){return _d8(_il,_js,_in);}),_jz=function(_jA){var _jB=E(_jA);return (_jB._==0)?E(_jy):new T2(1,new T(function(){return _bl(_jB.a);}),new T(function(){return _jz(_jB.b);}));};return _jz(_bb);case 116:var _jC=new T(function(){return _d8(_il,_js,_in);}),_jD=function(_jE){var _jF=E(_jE);return (_jF._==0)?E(_jC):new T2(1,new T(function(){return _bl(_jF.a);}),new T(function(){return _jD(_jF.b);}));};return _jD(_ba);default:var _jG=function(_jH){var _jI=new T(function(){return _d8(_il,_js,_in);}),_jJ=function(_jK){var _jL=E(_jK);return (_jL._==0)?E(_jI):new T2(1,new T(function(){return _bl(_jL.a);}),new T(function(){return _jJ(_jL.b);}));};return _jJ(B(A3(_jH,_il,__Z,_in)));};switch(_jt){case 72:return _jG(_hO);case 73:return _jG(_hG);case 77:return _jG(_hx);case 80:return _jG(_ho);case 81:return _jG(_hc);case 82:return _jG(_g9);case 83:return _jG(_g5);case 84:return _jG(_d9);case 88:return _jG(_d3);case 107:return _jG(_cZ);case 108:return _jG(_id);case 112:return _jG(_i4);case 113:return _jG(_i0);case 114:return _jG(_gc);default:var _j1=_il,_j2=_in;_ih=_j1;_ii=_js;_ij=_j2;return __continue;}}}break;case 95:var _jM=E(_is);if(!_jM._){return _iu(_);}else{var _jN=_jM.b;switch(E(_jM.a)){case 37:return _x(_bc,new T(function(){return _d8(_il,_jN,_in);},1));case 72:return _x(B(_6I(_5h,_5x,_5X,2,_9s,new T(function(){return E(E(_in).a);}))),new T(function(){return _d8(_il,_jN,_in);},1));case 73:return _x(B(_hB(_bd,_in)),new T(function(){return _d8(_il,_jN,_in);},1));case 77:return _x(B(_6I(_5h,_5x,_5X,2,_9s,new T(function(){return E(E(_in).b);}))),new T(function(){return _d8(_il,_jN,_in);},1));case 80:var _jO=E(_il),_jP=E(_jO.c),_jQ=E(_in);if(E(_jQ.a)>=12){return _x(_hg(_bi,_jP.b),new T(function(){return _d8(_jO,_jN,_jQ);},1));}else{return _x(_hg(_bi,_jP.a),new T(function(){return _d8(_jO,_jN,_jQ);},1));}break;case 81:var _jR=E(_in);return _x(_gj(_cH,_gM(_gh,true,_jR.c)),new T(function(){return _d8(_il,_jN,_jR);},1));case 82:return _x(_d8(_il,_cQ,_in),new T(function(){return _d8(_il,_jN,_in);},1));case 83:return _x(B(_fZ(_bd,_in)),new T(function(){return _d8(_il,_jN,_in);},1));case 84:return _x(_d8(_il,_cP,_in),new T(function(){return _d8(_il,_jN,_in);},1));case 88:var _jS=E(_il);return _x(_d8(_jS,_jS.f,_in),new T(function(){return _d8(_jS,_jN,_in);},1));case 107:return _x(B(_6I(_5h,_5x,_5X,2,_9s,new T(function(){return E(E(_in).a);}))),new T(function(){return _d8(_il,_jN,_in);},1));case 108:return _x(B(_i8(_bd,_in)),new T(function(){return _d8(_il,_jN,_in);},1));case 110:return _x(_bb,new T(function(){return _d8(_il,_jN,_in);},1));case 112:var _jT=E(_in);if(E(_jT.a)>=12){var _jU=E(_il);return _x(E(_jU.c).b,new T(function(){return _d8(_jU,_jN,_jT);},1));}else{var _jV=E(_il);return _x(E(_jV.c).a,new T(function(){return _d8(_jV,_jN,_jT);},1));}break;case 113:var _jW=E(_in);return _x(_hY(_jW.c),new T(function(){return _d8(_il,_jN,_jW);},1));case 114:var _jX=E(_il);return _x(_d8(_jX,_jX.g,_in),new T(function(){return _d8(_jX,_jN,_in);},1));case 116:return _x(_ba,new T(function(){return _d8(_il,_jN,_in);},1));default:var _j1=_il,_j2=_in;_ih=_j1;_ii=_jN;_ij=_j2;return __continue;}}break;default:return _iu(_);}}}else{return new T2(1,_iq,new T(function(){return _d8(_il,_ip,_in);}));}}})(_ih,_ii,_ij);if(_ik!=__continue){return _ik;}}},_jY=function(_jZ,_k0){return C > 19 ? new F(function(){return _6I(_5h,_5x,_5X,4,_jZ,new T(function(){var _k1=E(_k0);return (imul(_2y(_k1,60),100)|0)+_3P(_k1,60)|0;}));}) : (++C,_6I(_5h,_5x,_5X,4,_jZ,new T(function(){var _k1=E(_k0);return (imul(_2y(_k1,60),100)|0)+_3P(_k1,60)|0;})));},_k2=function(_k3,_k4,_k5){var _k6=E(E(_k5).b),_k7=E(_k6.c);if(!_k7._){var _k8=E(_k6.a);return (_k8>=0)?new T2(1,43,new T(function(){var _k9=E(_k4);if(!_k9._){return B(_jY(_5g,_k8));}else{return B(_jY(_k9.a,_k8));}})):new T2(1,45,new T(function(){var _ka=E(_k4);if(!_ka._){return B(_jY(_5g, -_k8));}else{return B(_jY(_ka.a, -_k8));}}));}else{return _k7;}},_kb=function(_kc,_kd,_ke){while(1){var _kf=(function(_kg,_kh,_ki){var _kj=E(_kh);if(!_kj._){return __Z;}else{var _kk=_kj.b,_kl=E(_kj.a);if(_kl==37){var _km=E(_kk);if(!_km._){return new T2(1,_kl,new T(function(){return _kb(_kg,__Z,_ki);}));}else{var _kn=_km.b,_ko=E(_km.a),_kp=function(_kq){switch(_ko){case 37:return _x(_bc,new T(function(){return _kb(_kg,_kn,_ki);},1));case 110:return _x(_bb,new T(function(){return _kb(_kg,_kn,_ki);},1));case 116:return _x(_ba,new T(function(){return _kb(_kg,_kn,_ki);},1));default:var _kr=_ks(_ko);if(!_kr._){return _kb(_kg,_kn,_ki);}else{return _x(B(A3(_kr.a,_kg,__Z,_ki)),new T(function(){return _kb(_kg,_kn,_ki);},1));}}};switch(_ko){case 35:var _kt=E(_kn);if(!_kt._){return _kp(_);}else{var _ku=_kt.b,_kv=E(_kt.a);switch(_kv){case 37:var _kw=new T(function(){return _kb(_kg,_ku,_ki);}),_kx=function(_ky){var _kz=E(_ky);return (_kz._==0)?E(_kw):new T2(1,new T(function(){return _bi(_kz.a);}),new T(function(){return _kx(_kz.b);}));};return _kx(_bc);case 110:var _kA=new T(function(){return _kb(_kg,_ku,_ki);}),_kB=function(_kC){var _kD=E(_kC);return (_kD._==0)?E(_kA):new T2(1,new T(function(){return _bi(_kD.a);}),new T(function(){return _kB(_kD.b);}));};return _kB(_bb);case 116:var _kE=new T(function(){return _kb(_kg,_ku,_ki);}),_kF=function(_kG){var _kH=E(_kG);return (_kH._==0)?E(_kE):new T2(1,new T(function(){return _bi(_kH.a);}),new T(function(){return _kF(_kH.b);}));};return _kF(_ba);default:var _kI=_ks(_kv);if(!_kI._){var _kJ=_kg,_kK=_ki;_kc=_kJ;_kd=_ku;_ke=_kK;return __continue;}else{var _kL=new T(function(){return _kb(_kg,_ku,_ki);}),_kM=function(_kN){var _kO=E(_kN);return (_kO._==0)?E(_kL):new T2(1,new T(function(){return _bi(_kO.a);}),new T(function(){return _kM(_kO.b);}));};return _kM(B(A3(_kI.a,_kg,__Z,_ki)));}}}break;case 45:var _kP=E(_kn);if(!_kP._){return _kp(_);}else{var _kQ=_kP.b,_kR=E(_kP.a);switch(_kR){case 37:return _x(_bc,new T(function(){return _kb(_kg,_kQ,_ki);},1));case 110:return _x(_bb,new T(function(){return _kb(_kg,_kQ,_ki);},1));case 116:return _x(_ba,new T(function(){return _kb(_kg,_kQ,_ki);},1));default:var _kS=_ks(_kR);if(!_kS._){var _kJ=_kg,_kK=_ki;_kc=_kJ;_kd=_kQ;_ke=_kK;return __continue;}else{return _x(B(A3(_kS.a,_kg,_bf,_ki)),new T(function(){return _kb(_kg,_kQ,_ki);},1));}}}break;case 48:var _kT=E(_kn);if(!_kT._){return _kp(_);}else{var _kU=_kT.b,_kV=E(_kT.a);switch(_kV){case 37:return _x(_bc,new T(function(){return _kb(_kg,_kU,_ki);},1));case 110:return _x(_bb,new T(function(){return _kb(_kg,_kU,_ki);},1));case 116:return _x(_ba,new T(function(){return _kb(_kg,_kU,_ki);},1));default:var _kW=_ks(_kV);if(!_kW._){var _kJ=_kg,_kK=_ki;_kc=_kJ;_kd=_kU;_ke=_kK;return __continue;}else{return _x(B(A3(_kW.a,_kg,_be,_ki)),new T(function(){return _kb(_kg,_kU,_ki);},1));}}}break;case 94:var _kX=E(_kn);if(!_kX._){return _kp(_);}else{var _kY=_kX.b,_kZ=E(_kX.a);switch(_kZ){case 37:var _l0=new T(function(){return _kb(_kg,_kY,_ki);}),_l1=function(_l2){var _l3=E(_l2);return (_l3._==0)?E(_l0):new T2(1,new T(function(){return _bl(_l3.a);}),new T(function(){return _l1(_l3.b);}));};return _l1(_bc);case 110:var _l4=new T(function(){return _kb(_kg,_kY,_ki);}),_l5=function(_l6){var _l7=E(_l6);return (_l7._==0)?E(_l4):new T2(1,new T(function(){return _bl(_l7.a);}),new T(function(){return _l5(_l7.b);}));};return _l5(_bb);case 116:var _l8=new T(function(){return _kb(_kg,_kY,_ki);}),_l9=function(_la){var _lb=E(_la);return (_lb._==0)?E(_l8):new T2(1,new T(function(){return _bl(_lb.a);}),new T(function(){return _l9(_lb.b);}));};return _l9(_ba);default:var _lc=_ks(_kZ);if(!_lc._){var _kJ=_kg,_kK=_ki;_kc=_kJ;_kd=_kY;_ke=_kK;return __continue;}else{var _ld=new T(function(){return _kb(_kg,_kY,_ki);}),_le=function(_lf){var _lg=E(_lf);return (_lg._==0)?E(_ld):new T2(1,new T(function(){return _bl(_lg.a);}),new T(function(){return _le(_lg.b);}));};return _le(B(A3(_lc.a,_kg,__Z,_ki)));}}}break;case 95:var _lh=E(_kn);if(!_lh._){return _kp(_);}else{var _li=_lh.b,_lj=E(_lh.a);switch(_lj){case 37:return _x(_bc,new T(function(){return _kb(_kg,_li,_ki);},1));case 110:return _x(_bb,new T(function(){return _kb(_kg,_li,_ki);},1));case 116:return _x(_ba,new T(function(){return _kb(_kg,_li,_ki);},1));default:var _lk=_ks(_lj);if(!_lk._){var _kJ=_kg,_kK=_ki;_kc=_kJ;_kd=_li;_ke=_kK;return __continue;}else{return _x(B(A3(_lk.a,_kg,_bd,_ki)),new T(function(){return _kb(_kg,_li,_ki);},1));}}}break;default:return _kp(_);}}}else{return new T2(1,_kl,new T(function(){return _kb(_kg,_kk,_ki);}));}}})(_kc,_kd,_ke);if(_kf!=__continue){return _kf;}}},_ll=new T(function(){return new T1(1,function(_lm,_ln,_lo){var _lp=E(_lm);return _kb(_lp,_lp.d,_lo);});}),_lq=new T1(0,1),_lr=function(_ls,_lt){var _lu=E(_ls);return new T2(0,_lu,new T(function(){var _lv=_lr(_41(_lu,_lt),_lt);return new T2(1,_lv.a,_lv.b);}));},_lw=function(_lx,_ly){var _lz=_lr(_lx,new T(function(){return _3G(_ly,_lx);}));return new T2(1,_lz.a,_lz.b);},_lA=function(_lB,_lC,_lD){if(!_8c(_lC,new T1(0,0))){var _lE=function(_lF){return (!_8s(_lF,_lD))?new T2(1,_lF,new T(function(){return _lE(_41(_lF,_lC));})):__Z;};return _lE(_lB);}else{var _lG=function(_lH){return (!_8k(_lH,_lD))?new T2(1,_lH,new T(function(){return _lG(_41(_lH,_lC));})):__Z;};return _lG(_lB);}},_lI=new T3(0,_7K,_8A,function(_lJ){return new T2(0,E(_lJ),E(_29));}),_lK={_:0,a:_lI,b:{_:0,a:function(_lL){return _41(_lL,_lq);},b:function(_lM){return _3G(_lM,_lq);},c:function(_lN){return _4v(E(_lN));},d:function(_lO){return _3c(_lO);},e:function(_lP){var _lQ=_lr(_lP,_lq);return new T2(1,_lQ.a,_lQ.b);},f:_lw,g:function(_lR,_lS){return _lA(_lR,_lq,_lS);},h:function(_lT,_lU,_lV){return _lA(_lT,_3G(_lU,_lT),_lV);}},c:function(_lW,_lX){if(!_3t(_lX,_f5)){return _fm(_lW,_lX);}else{return E(_39);}},d:_fe,e:function(_lY,_lZ){if(!_3t(_lZ,_f5)){return _2B(_lY,_lZ);}else{return E(_39);}},f:function(_m0,_m1){if(!_3t(_m1,_f5)){return _3T(_m0,_m1);}else{return E(_39);}},g:function(_m2,_m3){if(!_3t(_m3,_f5)){var _m4=_fJ(_m2,_m3);return new T2(0,_m4.a,_m4.b);}else{return E(_39);}},h:function(_m5,_m6){if(!_3t(_m6,_f5)){var _m7=_4O(_m5,_m6);return new T2(0,_m7.a,_m7.b);}else{return E(_39);}},i:function(_m8){return E(_m8);}},_m9=function(_ma){return E(E(_ma).b);},_mb=function(_mc,_md,_me){var _mf=_fS(_mc,_md,_me),_mg=_mf.a,_mh=E(_mf.b);if(!_8s(_4b(_mh.a,_29),_4b(_f5,_mh.b))){return E(_mg);}else{var _mi=_fH(_fF(_mc));return C > 19 ? new F(function(){return A3(_m9,_mi,_mg,new T(function(){return B(A2(_6C,_mi,_29));}));}) : (++C,A3(_m9,_mi,_mg,new T(function(){return B(A2(_6C,_mi,_29));})));}},_mj=function(_mk,_ml,_mm,_mn){var _mo=new T(function(){return E(_mm)+E(E(_mk).a)|0;}),_mp=new T(function(){return E(_ml)+_2y(E(_mo),60)|0;});return new T2(0,new T(function(){return _4v(_2y(E(_mp),24));}),new T3(0,new T(function(){return _3P(E(_mp),24);}),new T(function(){return _3P(E(_mo),60);}),_mn));},_mq=function(_mr,_ms,_mt){var _mu=B(A1(_mr,_ms));if(!_3t(_mu,_go)){return _2B(_4b(_ms,_mt),_mu);}else{return E(_39);}},_mv=new T(function(){return _dq(true,new T2(1,1454358528,new T2(1,27939,__Z)));}),_mw=function(_mx,_my,_mz){return _41(_mq(_gh,_41(_mq(_gh,_4b(_4v(_mx),_dt),_mv),_4b(_4v(_my),_dt)),_mv),_mz);},_mA=function(_mB){var _mC=E(_mB);return _mw(E(_mC.a),E(_mC.b),_mC.c);},_mD=function(_mE,_mF,_mG){var _mH=new T(function(){var _mI=E(_mG),_mJ=_mj(new T3(0,new T(function(){return  -E(E(_mE).a);}),false,__Z),_mI.a,_mI.b,_mI.c);return new T2(0,_mJ.a,_mJ.b);});return new T2(0,new T(function(){return _41(_mF,E(_mH).a);}),new T(function(){return _mA(E(_mH).b);}));},_mK=new T(function(){return _dq(true,new T2(1,479723520,new T2(1,40233135,__Z)));}),_mL=new T1(0,40587),_mM=function(_mN,_mO){var _mP=_mq(_gh,_4b(_3G(_mN,_mL),_dt),_mK);if(!_3i(_mK,_mO)){return _41(_mP,_mO);}else{return _41(_mP,_mK);}},_mQ=function(_mR,_mS,_mT){var _mU=_mD(_mT,_mR,_mS),_mV=_fz(_mM(_mU.a,_mU.b),_29,_dt,_29);return _8H(0,B(_mb(_lK,_mV.a,_mV.b)),__Z);},_mW=function(_mX,_mY,_mZ){var _n0=E(_mZ),_n1=E(_n0.a);return C > 19 ? new F(function(){return _mQ(_n1.a,_n1.b,_n0.b);}) : (++C,_mQ(_n1.a,_n1.b,_n0.b));},_n2=function(_n3,_n4,_n5){var _n6=E(E(E(_n5).b).a);return (_n6>=0)?new T2(1,43,new T(function(){var _n7=E(_n4);if(!_n7._){return B(_jY(_5g,_n6));}else{return B(_jY(_n7.a,_n6));}})):new T2(1,45,new T(function(){var _n8=E(_n4);if(!_n8._){return B(_jY(_5g, -_n6));}else{return B(_jY(_n8.a, -_n6));}}));},_n9=function(_na){return E(E(_na).a);},_ks=function(_nb){switch(E(_nb)){case 65:var _nc=function(_nd,_ne,_nf){return _cR(_nd,_ne,new T(function(){return _n9(_nf);}));};return new T1(1,_nc);case 66:var _ng=function(_nh,_ni,_nj){return E(_7g(E(_nh).b,E(_6h(new T(function(){return E(E(E(_nj).a).a);},1)).b)-1|0).a);};return new T1(1,_ng);case 67:var _nk=function(_nl,_nm,_nn){return C > 19 ? new F(function(){return _aL(_nm,new T(function(){return E(E(E(_nn).a).a);},1));}) : (++C,_aL(_nm,new T(function(){return E(E(E(_nn).a).a);},1)));};return new T1(1,_nk);case 68:var _no=function(_np,_nq,_nr){return _aH(_np,_2o,new T(function(){return E(E(E(_nr).a).a);}));};return new T1(1,_no);case 70:var _ns=function(_nt,_nu,_nv){return _aH(_nt,_2n,new T(function(){return E(E(E(_nv).a).a);}));};return new T1(1,_ns);case 71:var _nw=function(_nx,_ny,_nz){return C > 19 ? new F(function(){return _av(_ny,new T(function(){return E(E(E(_nz).a).a);}));}) : (++C,_av(_ny,new T(function(){return E(E(E(_nz).a).a);})));};return new T1(1,_nw);case 72:var _nA=function(_nB,_nC,_nD){return C > 19 ? new F(function(){return _hK(_nC,new T(function(){return E(E(E(_nD).a).b);},1));}) : (++C,_hK(_nC,new T(function(){return E(E(E(_nD).a).b);},1)));};return new T1(1,_nA);case 73:var _nE=function(_nF,_nG,_nH){return C > 19 ? new F(function(){return _hB(_nG,new T(function(){return E(E(E(_nH).a).b);},1));}) : (++C,_hB(_nG,new T(function(){return E(E(E(_nH).a).b);},1)));};return new T1(1,_nE);case 77:var _nI=function(_nJ,_nK,_nL){return C > 19 ? new F(function(){return _ht(_nK,new T(function(){return E(E(E(_nL).a).b);},1));}) : (++C,_ht(_nK,new T(function(){return E(E(E(_nL).a).b);},1)));};return new T1(1,_nI);case 80:return new T1(1,function(_nM,_nN,_nO){var _nP=E(E(_nM).c);return _hk(_nP.a,_nP.b,E(E(E(E(_nO).a).b).a));});case 81:return new T1(1,function(_nQ,_nR,_nS){return _gj(_cH,_gM(_gh,true,E(E(E(_nS).a).b).c));});case 82:var _nT=function(_nU,_nV,_nW){return _d8(_nU,_cQ,new T(function(){return E(E(E(_nW).a).b);}));};return new T1(1,_nT);case 83:var _nX=function(_nY,_nZ,_o0){return C > 19 ? new F(function(){return _fZ(_nZ,new T(function(){return E(E(E(_o0).a).b);},1));}) : (++C,_fZ(_nZ,new T(function(){return E(E(E(_o0).a).b);},1)));};return new T1(1,_nX);case 84:var _o1=function(_o2,_o3,_o4){return _d8(_o2,_cP,new T(function(){return E(E(E(_o4).a).b);}));};return new T1(1,_o1);case 85:var _o5=function(_o6,_o7,_o8){return C > 19 ? new F(function(){return _an(_o7,new T(function(){return E(E(E(_o8).a).a);}));}) : (++C,_an(_o7,new T(function(){return E(E(E(_o8).a).a);})));};return new T1(1,_o5);case 86:var _o9=function(_oa,_ob,_oc){return C > 19 ? new F(function(){return _af(_ob,new T(function(){return E(E(E(_oc).a).a);}));}) : (++C,_af(_ob,new T(function(){return E(E(E(_oc).a).a);})));};return new T1(1,_o9);case 87:var _od=function(_oe,_of,_og){return C > 19 ? new F(function(){return _a7(_of,new T(function(){return E(E(E(_og).a).a);}));}) : (++C,_a7(_of,new T(function(){return E(E(E(_og).a).a);})));};return new T1(1,_od);case 88:var _oh=function(_oi,_oj,_ok){var _ol=E(_oi);return _d8(_ol,_ol.f,new T(function(){return E(E(E(_ok).a).b);}));};return new T1(1,_oh);case 89:var _om=function(_on,_oo,_op){return C > 19 ? new F(function(){return _9W(_oo,new T(function(){return E(E(E(_op).a).a);},1));}) : (++C,_9W(_oo,new T(function(){return E(E(E(_op).a).a);},1)));};return new T1(1,_om);case 90:return E(new T1(1,_k2));case 97:var _oq=function(_or,_os,_ot){return _cL(_or,_os,new T(function(){return _n9(_ot);}));};return new T1(1,_oq);case 98:var _ou=function(_ov,_ow,_ox){return E(_7g(E(_ov).b,E(_6h(new T(function(){return E(E(E(_ox).a).a);},1)).b)-1|0).b);};return new T1(1,_ou);case 99:return E(_ll);case 100:var _oy=function(_oz,_oA,_oB){return C > 19 ? new F(function(){return _9B(_oA,new T(function(){return E(E(E(_oB).a).a);},1));}) : (++C,_9B(_oA,new T(function(){return E(E(E(_oB).a).a);},1)));};return new T1(1,_oy);case 101:var _oC=function(_oD,_oE,_oF){return C > 19 ? new F(function(){return _9t(_oE,new T(function(){return E(E(E(_oF).a).a);},1));}) : (++C,_9t(_oE,new T(function(){return E(E(E(_oF).a).a);},1)));};return new T1(1,_oC);case 102:var _oG=function(_oH,_oI,_oJ){return C > 19 ? new F(function(){return _9j(_oI,new T(function(){return E(E(E(_oJ).a).a);}));}) : (++C,_9j(_oI,new T(function(){return E(E(E(_oJ).a).a);})));};return new T1(1,_oG);case 103:var _oK=function(_oL,_oM,_oN){return C > 19 ? new F(function(){return _9a(_oM,new T(function(){return E(E(E(_oN).a).a);}));}) : (++C,_9a(_oM,new T(function(){return E(E(E(_oN).a).a);})));};return new T1(1,_oK);case 104:var _oO=function(_oP,_oQ,_oR){return E(_7g(E(_oP).b,E(_6h(new T(function(){return E(E(E(_oR).a).a);},1)).b)-1|0).b);};return new T1(1,_oO);case 106:var _oS=function(_oT,_oU,_oV){return C > 19 ? new F(function(){return _70(_oU,new T(function(){return E(E(E(_oV).a).a);},1));}) : (++C,_70(_oU,new T(function(){return E(E(E(_oV).a).a);},1)));};return new T1(1,_oS);case 107:var _oW=function(_oX,_oY,_oZ){return C > 19 ? new F(function(){return _cV(_oY,new T(function(){return E(E(E(_oZ).a).b);},1));}) : (++C,_cV(_oY,new T(function(){return E(E(E(_oZ).a).b);},1)));};return new T1(1,_oW);case 108:var _p0=function(_p1,_p2,_p3){return C > 19 ? new F(function(){return _i8(_p2,new T(function(){return E(E(E(_p3).a).b);},1));}) : (++C,_i8(_p2,new T(function(){return E(E(E(_p3).a).b);},1)));};return new T1(1,_p0);case 109:var _p4=function(_p5,_p6,_p7){return C > 19 ? new F(function(){return _6S(_p6,new T(function(){return E(E(E(_p7).a).a);},1));}) : (++C,_6S(_p6,new T(function(){return E(E(E(_p7).a).a);},1)));};return new T1(1,_p4);case 112:return new T1(1,function(_p8,_p9,_pa){return (E(E(E(E(_pa).a).b).a)>=12)?E(E(E(_p8).c).b):E(E(E(_p8).c).a);});case 113:return new T1(1,function(_pb,_pc,_pd){return _hY(E(E(E(_pd).a).b).c);});case 114:var _pe=function(_pf,_pg,_ph){var _pi=E(_pf);return _d8(_pi,_pi.g,new T(function(){return E(E(E(_ph).a).b);}));};return new T1(1,_pe);case 115:return E(new T1(1,_mW));case 117:var _pj=function(_pk,_pl,_pm){return _2t(0,E(_52(new T(function(){return E(E(E(_pm).a).a);})).c),__Z);};return new T1(1,_pj);case 119:var _pn=function(_po,_pp,_pq){return _2t(0,E(_4x(new T(function(){return E(E(E(_pq).a).a);})).b),__Z);};return new T1(1,_pn);case 120:var _pr=function(_ps,_pt,_pu){var _pv=E(_ps);return _aH(_pv,_pv.e,new T(function(){return E(E(E(_pu).a).a);}));};return new T1(1,_pr);case 121:var _pw=function(_px,_py,_pz){return C > 19 ? new F(function(){return _91(_py,new T(function(){return E(E(E(_pz).a).a);},1));}) : (++C,_91(_py,new T(function(){return E(E(E(_pz).a).a);},1)));};return new T1(1,_pw);case 122:return E(new T1(1,_n2));default:return __Z;}},_pA=function(_pB){var _pC=_fz(_pB,_29,_dt,_29);return new T2(0,E(_pC.a),E(_pC.b));},_pD={_:0,a:_41,b:_3G,c:function(_pE,_pF){return _mq(_gh,_pE,_pF);},d:_7z,e:_7u,f:function(_pG){return _4b(_7F(_pG),_dt);},g:function(_pH){return _4b(_pH,_dt);}},_pI=new T1(0,60),_pJ=new T(function(){return _dq(true,new T2(1,479723520,new T2(1,40233135,__Z)));}),_pK=function(_pL){return E(E(_pL).c);},_pM=function(_pN){return E(E(_pN).c);},_pO=function(_pP,_pQ,_pR,_pS){var _pT=B(A2(_pM,_pP,_pR)),_pU=B(A2(_pM,_pP,_pS)),_pV=_fz(_pT.a,_pT.b,_pU.a,_pU.b);return C > 19 ? new F(function(){return _mb(_pQ,_pV.a,_pV.b);}) : (++C,_mb(_pQ,_pV.a,_pV.b));},_pW=function(_pX,_pY,_pZ){var _q0=_fH(_pX),_q1=new T(function(){var _q2=new T(function(){return B(A2(_6C,_q0,new T(function(){return B(_pO(_pX,_lK,_pY,_pZ));})));});return B(A3(_pK,_q0,_q2,_pZ));});return C > 19 ? new F(function(){return A3(_m9,_q0,_pY,_q1);}) : (++C,A3(_m9,_q0,_pY,_q1));},_q3=function(_q4){if(!_8c(_q4,_pJ)){var _q5=new T(function(){var _q6=_fz(_q4,_29,_dt,_29),_q7=_fz(_mv,_29,_dt,_29),_q8=_fz(_q6.a,_q6.b,_q7.a,_q7.b);return B(_mb(_lK,_q8.a,_q8.b));});return new T3(0,new T(function(){var _q9=_fz(_q5,_29,_pI,_29);return _3c(B(_mb(_lK,_q9.a,_q9.b)));}),new T(function(){return _3c(B(_pW(_lI,_q5,_pI)));}),new T(function(){return B(_pW(new T3(0,_pD,{_:0,a:new T2(0,_3t,_7M),b:_80,c:_8s,d:_3i,e:_8k,f:_8c,g:_7U,h:_7X},_pA),_q4,_mv));}));}else{return new T3(0,23,59,new T(function(){return _41(_mv,_3G(_q4,_pJ));}));}},_qa=function(_qb,_qc,_qd){var _qe=new T(function(){var _qf=_q3(_qd),_qg=_mj(_qb,_qf.a,_qf.b,_qf.c);return new T2(0,_qg.a,_qg.b);});return new T2(0,new T(function(){return _41(_qc,E(_qe).a);}),new T(function(){return E(E(_qe).b);}));},_qh=new T3(0,0,false,new T(function(){return unCStr("UTC");})),_qi=function(_qj){var _qk=_ks(_qj);if(!_qk._){return __Z;}else{var _ql=function(_qm,_qn,_qo){return C > 19 ? new F(function(){return A3(_qk.a,_qm,_qn,new T2(0,new T(function(){var _qp=E(_qo),_qq=_qa(_qh,_qp.a,_qp.b);return new T2(0,_qq.a,_qq.b);}),_qh));}) : (++C,A3(_qk.a,_qm,_qn,new T2(0,new T(function(){var _qp=E(_qo),_qq=_qa(_qh,_qp.a,_qp.b);return new T2(0,_qq.a,_qq.b);}),_qh)));};return new T1(1,_ql);}},_qr=function(_qs){return _qi(E(_qs));},_qt=function(_){return 0;},_qu=new T2(0,_1V,function(_qv,_){return new T1(1,_qv);}),_qw=new T2(0,_1X,_9),_qx=function(_qy,_qz){return (E(_qy)._==0)?__Z:E(_qz);},_qA=function(_qB,_qC){var _qD=E(_qB);return (_qD._==0)?__Z:(E(_qC)._==0)?__Z:_qD;},_qE=function(_qF,_qG){var _qH=E(_qG);return (_qH._==0)?__Z:new T1(1,new T(function(){return B(A1(_qF,_qH.a));}));},_qI=function(_qJ,_qK){var _qL=E(_qJ);if(!_qL._){return __Z;}else{return _qE(_qL.a,_qK);}},_qM=function(_qN,_qO){return (E(_qO)._==0)?__Z:new T1(1,_qN);},_qP=function(_qQ){return new T1(1,_qQ);},_qR=function(_qS,_qT){var _qU=E(_qS);if(!_qU._){return __Z;}else{return C > 19 ? new F(function(){return A1(_qT,_qU.a);}) : (++C,A1(_qT,_qU.a));}},_qV=function(_qW){return __Z;},_qX=function(_qY,_qZ){while(1){var _r0=E(_qY);if(!_r0._){return (E(_qZ)._==0)?true:false;}else{var _r1=E(_qZ);if(!_r1._){return false;}else{if(E(_r0.a)!=E(_r1.a)){return false;}else{_qY=_r0.b;_qZ=_r1.b;continue;}}}}},_r2=function(_r3,_r4,_r5){var _r6=function(_r7){var _r8=_2y((imul(367,_r7)|0)-362|0,12),_r9=function(_ra){if(_r5>=1){var _rb=_7g(_6b(_r3),_r7-1|0);return (_r5<=_rb)?(_r8+_ra|0)+_r5|0:(_r8+_ra|0)+_rb|0;}else{return (_r8+_ra|0)+1|0;}};if(_r7>2){if(!E(_r3)){return _r9(-2);}else{return _r9(-1);}}else{return _r9(0);}};if(_r4>=1){if(_r4<=12){return _r6(_r4);}else{return _r6(12);}}else{return _r6(1);}},_rc=function(_rd,_re,_rf){return _4K(_rd,_r2(new T(function(){return _4I(_rd);}),_re,_rf));},_rg=function(_rh,_ri,_rj){return _rc(_rh,E(_ri),E(_rj));},_rk=new T(function(){return err(new T(function(){return unCStr("Maybe.fromJust: Nothing");}));}),_rl=function(_rm,_rn,_ro){if(!E(_4u)){var _rp=_4K(_rm,1);return _41(_rp,_3G(_41(_41(_3T(_3G(new T1(0,5),_rp),_4t),_4b(_4t,_4v(_rn-1|0))),_4v(_ro)),_3a));}else{return E(_39);}},_rq=function(_rr,_rs,_rt){return _rl(_rr,E(_rs),E(_rt));},_ru=function(_rv,_rw){return _4K(_rv,E(_rw));},_rx=function(_ry,_rz,_rA){if(!E(_4u)){var _rB=_4K(_ry,1);return _41(_rB,_41(_41(_3T(_3G(_3h,_rB),_4t),_4b(_4t,_4v(_rz-1|0))),_4v(_rA)));}else{return E(_39);}},_rC=function(_rD,_rE,_rF){return _rx(_rD,E(_rE),E(_rF));},_rG=function(_rH,_rI,_rJ){if(!E(_4Z)){var _rK=function(_rL){var _rM=function(_rN){var _rO=_4K(_rH,6);return _3G(_41(_3G(_rO,_3T(_rO,_4X)),_4v((imul(_rL,7)|0)+_rN|0)),new T1(0,10));};if(_rJ>=1){if(_rJ<=7){return _rM(_rJ);}else{return _rM(7);}}else{return _rM(1);}};if(_rI>=1){if(E(_52(new T(function(){return _4K(_rH,365);})).b)==53){if(_rI<=53){return _rK(_rI);}else{return _rK(53);}}else{if(_rI<=52){return _rK(_rI);}else{return _rK(52);}}}else{return _rK(1);}}else{return E(_39);}},_rP=function(_rQ,_rR,_rS){return C > 19 ? new F(function(){return _rG(_rQ,E(_rR),E(_rS));}) : (++C,_rG(_rQ,E(_rR),E(_rS)));},_rT=function(_rU){while(1){var _rV=(function(_rW){var _rX=E(_rW);if(!_rX._){return __Z;}else{var _rY=_rX.b,_rZ=E(_rX.a);if(_rZ._==1){return new T2(1,_rZ.a,new T(function(){return _rT(_rY);}));}else{_rU=_rY;return __continue;}}})(_rU);if(_rV!=__continue){return _rV;}}},_s0=function(_s1,_s2){while(1){var _s3=E(_s1);if(!_s3._){return E(_s2);}else{var _s4=_s3.b,_s5=E(_s3.a);if(!_s5._){_s1=_s4;_s2=_s5.a;continue;}else{_s1=_s4;continue;}}}},_s6=function(_s7){while(1){var _s8=(function(_s9){var _sa=E(_s9);if(!_sa._){return __Z;}else{var _sb=_sa.b,_sc=E(_sa.a);if(_sc._==5){return new T2(1,_sc.a,new T(function(){return _s6(_sb);}));}else{_s7=_sb;return __continue;}}})(_s7);if(_s8!=__continue){return _s8;}}},_sd=function(_se){while(1){var _sf=(function(_sg){var _sh=E(_sg);if(!_sh._){return __Z;}else{var _si=_sh.b,_sj=E(_sh.a);if(_sj._==3){return new T2(1,_sj.a,new T(function(){return _sd(_si);}));}else{_se=_si;return __continue;}}})(_se);if(_sf!=__continue){return _sf;}}},_sk=new T(function(){return unCStr(": empty list");}),_sl=function(_sm){return err(_x(_78,new T(function(){return _x(_sm,_sk);},1)));},_sn=new T(function(){return _sl(new T(function(){return unCStr("last");}));}),_so=function(_sp){return _hg(_bl,E(_sp).b);},_sq=new T1(0,100),_sr=new T(function(){return unCStr("Prelude.read: no parse");}),_ss=new T(function(){return err(_sr);}),_st=new T(function(){return unCStr("Prelude.read: ambiguous parse");}),_su=new T(function(){return err(_st);}),_sv=function(_sw){return _hg(_bl,E(_sw).a);},_sx=new T(function(){return unCStr("base");}),_sy=new T(function(){return unCStr("Control.Exception.Base");}),_sz=new T(function(){return unCStr("PatternMatchFail");}),_sA=function(_sB){return E(new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_sx,_sy,_sz),__Z,__Z));},_sC=function(_sD){return E(E(_sD).a);},_sE=function(_sF,_sG){return _x(E(_sF).a,_sG);},_sH=new T(function(){return new T5(0,_sA,new T3(0,function(_sI,_sJ,_sK){return _x(E(_sJ).a,_sK);},_sC,function(_sL,_sM){return _1q(_sE,_sL,_sM);}),function(_sN){return new T2(0,_sH,_sN);},function(_sO){var _sP=E(_sO);return _m(_k(_sP.a),_sA,_sP.b);},_sC);}),_sQ=new T(function(){return unCStr("Non-exhaustive patterns in");}),_sR=function(_sS,_sT){return die(new T(function(){return B(A2(_1M,_sT,_sS));}));},_sU=function(_sV,_38){return _sR(_sV,_38);},_sW=function(_sX,_sY){var _sZ=E(_sY);if(!_sZ._){return new T2(0,__Z,__Z);}else{var _t0=_sZ.a;if(!B(A1(_sX,_t0))){return new T2(0,__Z,_sZ);}else{var _t1=new T(function(){var _t2=_sW(_sX,_sZ.b);return new T2(0,_t2.a,_t2.b);});return new T2(0,new T2(1,_t0,new T(function(){return E(E(_t1).a);})),new T(function(){return E(E(_t1).b);}));}}},_t3=new T(function(){return unCStr("\n");}),_t4=function(_t5){return (E(_t5)==124)?false:true;},_t6=function(_t7,_t8){var _t9=_sW(_t4,unCStr(_t7)),_ta=_t9.a,_tb=function(_tc,_td){var _te=new T(function(){var _tf=new T(function(){return _x(_t8,new T(function(){return _x(_td,_t3);},1));});return unAppCStr(": ",_tf);},1);return _x(_tc,_te);},_tg=E(_t9.b);if(!_tg._){return _tb(_ta,__Z);}else{if(E(_tg.a)==124){return _tb(_ta,new T2(1,32,_tg.b));}else{return _tb(_ta,__Z);}}},_th=function(_ti){return _sU(new T1(0,new T(function(){return _t6(_ti,_sQ);})),_sH);},_tj=new T(function(){return B(_th("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_tk=function(_tl,_tm){while(1){var _tn=(function(_to,_tp){var _tq=E(_to);switch(_tq._){case 0:var _tr=E(_tp);if(!_tr._){return __Z;}else{_tl=B(A1(_tq.a,_tr.a));_tm=_tr.b;return __continue;}break;case 1:var _ts=B(A1(_tq.a,_tp)),_tt=_tp;_tl=_ts;_tm=_tt;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_tq.a,_tp),new T(function(){return _tk(_tq.b,_tp);}));default:return E(_tq.a);}})(_tl,_tm);if(_tn!=__continue){return _tn;}}},_tu=function(_tv,_tw){var _tx=function(_ty){var _tz=E(_tw);if(_tz._==3){return new T2(3,_tz.a,new T(function(){return _tu(_tv,_tz.b);}));}else{var _tA=E(_tv);if(_tA._==2){return _tz;}else{if(_tz._==2){return _tA;}else{var _tB=function(_tC){if(_tz._==4){var _tD=function(_tE){return new T1(4,new T(function(){return _x(_tk(_tA,_tE),_tz.a);}));};return new T1(1,_tD);}else{if(_tA._==1){var _tF=_tA.a;if(!_tz._){return new T1(1,function(_tG){return _tu(B(A1(_tF,_tG)),_tz);});}else{var _tH=function(_tI){return _tu(B(A1(_tF,_tI)),new T(function(){return B(A1(_tz.a,_tI));}));};return new T1(1,_tH);}}else{if(!_tz._){return E(_tj);}else{var _tJ=function(_tK){return _tu(_tA,new T(function(){return B(A1(_tz.a,_tK));}));};return new T1(1,_tJ);}}}};switch(_tA._){case 1:if(_tz._==4){var _tL=function(_tM){return new T1(4,new T(function(){return _x(_tk(B(A1(_tA.a,_tM)),_tM),_tz.a);}));};return new T1(1,_tL);}else{return _tB(_);}break;case 4:var _tN=_tA.a;switch(_tz._){case 0:var _tO=function(_tP){var _tQ=new T(function(){return _x(_tN,new T(function(){return _tk(_tz,_tP);},1));});return new T1(4,_tQ);};return new T1(1,_tO);case 1:var _tR=function(_tS){var _tT=new T(function(){return _x(_tN,new T(function(){return _tk(B(A1(_tz.a,_tS)),_tS);},1));});return new T1(4,_tT);};return new T1(1,_tR);default:return new T1(4,new T(function(){return _x(_tN,_tz.a);}));}break;default:return _tB(_);}}}}},_tU=E(_tv);switch(_tU._){case 0:var _tV=E(_tw);if(!_tV._){var _tW=function(_tX){return _tu(B(A1(_tU.a,_tX)),new T(function(){return B(A1(_tV.a,_tX));}));};return new T1(0,_tW);}else{return _tx(_);}break;case 3:return new T2(3,_tU.a,new T(function(){return _tu(_tU.b,_tw);}));default:return _tx(_);}},_tY=new T(function(){return unCStr("(");}),_tZ=new T(function(){return unCStr(")");}),_u0=new T2(0,function(_u1,_u2){return E(_u1)==E(_u2);},function(_u3,_u4){return E(_u3)!=E(_u4);}),_u5=function(_u6,_u7){while(1){var _u8=E(_u6);if(!_u8._){return (E(_u7)._==0)?true:false;}else{var _u9=E(_u7);if(!_u9._){return false;}else{if(E(_u8.a)!=E(_u9.a)){return false;}else{_u6=_u8.b;_u7=_u9.b;continue;}}}}},_ua=function(_ub,_uc){return (!_u5(_ub,_uc))?true:false;},_ud=function(_ue,_uf){var _ug=E(_ue);switch(_ug._){case 0:return new T1(0,function(_uh){return C > 19 ? new F(function(){return _ud(B(A1(_ug.a,_uh)),_uf);}) : (++C,_ud(B(A1(_ug.a,_uh)),_uf));});case 1:return new T1(1,function(_ui){return C > 19 ? new F(function(){return _ud(B(A1(_ug.a,_ui)),_uf);}) : (++C,_ud(B(A1(_ug.a,_ui)),_uf));});case 2:return new T0(2);case 3:return _tu(B(A1(_uf,_ug.a)),new T(function(){return B(_ud(_ug.b,_uf));}));default:var _uj=function(_uk){var _ul=E(_uk);if(!_ul._){return __Z;}else{var _um=E(_ul.a);return _x(_tk(B(A1(_uf,_um.a)),_um.b),new T(function(){return _uj(_ul.b);},1));}},_un=_uj(_ug.a);return (_un._==0)?new T0(2):new T1(4,_un);}},_uo=new T0(2),_up=function(_uq){return new T2(3,_uq,_uo);},_ur=function(_us,_ut){var _uu=E(_us);if(!_uu){return C > 19 ? new F(function(){return A1(_ut,0);}) : (++C,A1(_ut,0));}else{var _uv=new T(function(){return B(_ur(_uu-1|0,_ut));});return new T1(0,function(_uw){return E(_uv);});}},_ux=function(_uy,_uz,_uA){var _uB=new T(function(){return B(A1(_uy,_up));}),_uC=function(_uD,_uE,_uF,_uG){while(1){var _uH=B((function(_uI,_uJ,_uK,_uL){var _uM=E(_uI);switch(_uM._){case 0:var _uN=E(_uJ);if(!_uN._){return C > 19 ? new F(function(){return A1(_uz,_uL);}) : (++C,A1(_uz,_uL));}else{var _uO=_uK+1|0,_uP=_uL;_uD=B(A1(_uM.a,_uN.a));_uE=_uN.b;_uF=_uO;_uG=_uP;return __continue;}break;case 1:var _uQ=B(A1(_uM.a,_uJ)),_uR=_uJ,_uO=_uK,_uP=_uL;_uD=_uQ;_uE=_uR;_uF=_uO;_uG=_uP;return __continue;case 2:return C > 19 ? new F(function(){return A1(_uz,_uL);}) : (++C,A1(_uz,_uL));break;case 3:var _uS=new T(function(){return B(_ud(_uM,_uL));});return C > 19 ? new F(function(){return _ur(_uK,function(_uT){return E(_uS);});}) : (++C,_ur(_uK,function(_uT){return E(_uS);}));break;default:return C > 19 ? new F(function(){return _ud(_uM,_uL);}) : (++C,_ud(_uM,_uL));}})(_uD,_uE,_uF,_uG));if(_uH!=__continue){return _uH;}}};return function(_uU){return _uC(_uB,_uU,0,_uA);};},_uV=function(_uW){return C > 19 ? new F(function(){return A1(_uW,__Z);}) : (++C,A1(_uW,__Z));},_uX=function(_uY,_uZ){var _v0=function(_v1){var _v2=E(_v1);if(!_v2._){return _uV;}else{var _v3=_v2.a;if(!B(A1(_uY,_v3))){return _uV;}else{var _v4=new T(function(){return _v0(_v2.b);}),_v5=function(_v6){var _v7=new T(function(){return B(A1(_v4,function(_v8){return C > 19 ? new F(function(){return A1(_v6,new T2(1,_v3,_v8));}) : (++C,A1(_v6,new T2(1,_v3,_v8)));}));});return new T1(0,function(_v9){return E(_v7);});};return _v5;}}};return function(_va){return C > 19 ? new F(function(){return A2(_v0,_va,_uZ);}) : (++C,A2(_v0,_va,_uZ));};},_vb=new T(function(){return err(new T(function(){return unCStr("valDig: Bad base");}));}),_vc=function(_vd,_ve){var _vf=function(_vg,_vh){var _vi=E(_vg);if(!_vi._){var _vj=new T(function(){return B(A1(_vh,__Z));});return function(_vk){return C > 19 ? new F(function(){return A1(_vk,_vj);}) : (++C,A1(_vk,_vj));};}else{var _vl=E(_vi.a),_vm=function(_vn){var _vo=new T(function(){return _vf(_vi.b,function(_vp){return C > 19 ? new F(function(){return A1(_vh,new T2(1,_vn,_vp));}) : (++C,A1(_vh,new T2(1,_vn,_vp)));});}),_vq=function(_vr){var _vs=new T(function(){return B(A1(_vo,_vr));});return new T1(0,function(_vt){return E(_vs);});};return _vq;};switch(E(_vd)){case 8:if(48>_vl){var _vu=new T(function(){return B(A1(_vh,__Z));});return function(_vv){return C > 19 ? new F(function(){return A1(_vv,_vu);}) : (++C,A1(_vv,_vu));};}else{if(_vl>55){var _vw=new T(function(){return B(A1(_vh,__Z));});return function(_vx){return C > 19 ? new F(function(){return A1(_vx,_vw);}) : (++C,A1(_vx,_vw));};}else{return _vm(_vl-48|0);}}break;case 10:if(48>_vl){var _vy=new T(function(){return B(A1(_vh,__Z));});return function(_vz){return C > 19 ? new F(function(){return A1(_vz,_vy);}) : (++C,A1(_vz,_vy));};}else{if(_vl>57){var _vA=new T(function(){return B(A1(_vh,__Z));});return function(_vB){return C > 19 ? new F(function(){return A1(_vB,_vA);}) : (++C,A1(_vB,_vA));};}else{return _vm(_vl-48|0);}}break;case 16:if(48>_vl){if(97>_vl){if(65>_vl){var _vC=new T(function(){return B(A1(_vh,__Z));});return function(_vD){return C > 19 ? new F(function(){return A1(_vD,_vC);}) : (++C,A1(_vD,_vC));};}else{if(_vl>70){var _vE=new T(function(){return B(A1(_vh,__Z));});return function(_vF){return C > 19 ? new F(function(){return A1(_vF,_vE);}) : (++C,A1(_vF,_vE));};}else{return _vm((_vl-65|0)+10|0);}}}else{if(_vl>102){if(65>_vl){var _vG=new T(function(){return B(A1(_vh,__Z));});return function(_vH){return C > 19 ? new F(function(){return A1(_vH,_vG);}) : (++C,A1(_vH,_vG));};}else{if(_vl>70){var _vI=new T(function(){return B(A1(_vh,__Z));});return function(_vJ){return C > 19 ? new F(function(){return A1(_vJ,_vI);}) : (++C,A1(_vJ,_vI));};}else{return _vm((_vl-65|0)+10|0);}}}else{return _vm((_vl-97|0)+10|0);}}}else{if(_vl>57){if(97>_vl){if(65>_vl){var _vK=new T(function(){return B(A1(_vh,__Z));});return function(_vL){return C > 19 ? new F(function(){return A1(_vL,_vK);}) : (++C,A1(_vL,_vK));};}else{if(_vl>70){var _vM=new T(function(){return B(A1(_vh,__Z));});return function(_vN){return C > 19 ? new F(function(){return A1(_vN,_vM);}) : (++C,A1(_vN,_vM));};}else{return _vm((_vl-65|0)+10|0);}}}else{if(_vl>102){if(65>_vl){var _vO=new T(function(){return B(A1(_vh,__Z));});return function(_vP){return C > 19 ? new F(function(){return A1(_vP,_vO);}) : (++C,A1(_vP,_vO));};}else{if(_vl>70){var _vQ=new T(function(){return B(A1(_vh,__Z));});return function(_vR){return C > 19 ? new F(function(){return A1(_vR,_vQ);}) : (++C,A1(_vR,_vQ));};}else{return _vm((_vl-65|0)+10|0);}}}else{return _vm((_vl-97|0)+10|0);}}}else{return _vm(_vl-48|0);}}break;default:return E(_vb);}}},_vS=function(_vT){var _vU=E(_vT);if(!_vU._){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_ve,_vU);}) : (++C,A1(_ve,_vU));}};return function(_vV){return C > 19 ? new F(function(){return A3(_vf,_vV,_1V,_vS);}) : (++C,A3(_vf,_vV,_1V,_vS));};},_vW=function(_vX){var _vY=function(_vZ){return C > 19 ? new F(function(){return A1(_vX,new T1(5,new T2(0,8,_vZ)));}) : (++C,A1(_vX,new T1(5,new T2(0,8,_vZ))));},_w0=function(_w1){return C > 19 ? new F(function(){return A1(_vX,new T1(5,new T2(0,16,_w1)));}) : (++C,A1(_vX,new T1(5,new T2(0,16,_w1))));},_w2=function(_w3){switch(E(_w3)){case 79:return new T1(1,_vc(8,_vY));case 88:return new T1(1,_vc(16,_w0));case 111:return new T1(1,_vc(8,_vY));case 120:return new T1(1,_vc(16,_w0));default:return new T0(2);}};return function(_w4){return (E(_w4)==48)?E(new T1(0,_w2)):new T0(2);};},_w5=function(_w6){return new T1(0,_vW(_w6));},_w7=function(_w8){return C > 19 ? new F(function(){return A1(_w8,__Z);}) : (++C,A1(_w8,__Z));},_w9=function(_wa){return C > 19 ? new F(function(){return A1(_wa,__Z);}) : (++C,A1(_wa,__Z));},_wb=new T1(0,10),_wc=function(_wd){return _4v(E(_wd));},_we=new T(function(){return err(new T(function(){return unCStr("this should not happen");}));}),_wf=function(_wg,_wh){var _wi=E(_wh);if(!_wi._){return __Z;}else{var _wj=E(_wi.b);return (_wj._==0)?E(_we):new T2(1,_41(_4b(_wi.a,_wg),_wj.a),new T(function(){return _wf(_wg,_wj.b);}));}},_wk=new T1(0,0),_wl=function(_wm,_wn,_wo){while(1){var _wp=(function(_wq,_wr,_ws){var _wt=E(_ws);if(!_wt._){return E(_wk);}else{if(!E(_wt.b)._){return E(_wt.a);}else{var _wu=E(_wr);if(_wu<=40){var _wv=function(_ww,_wx){while(1){var _wy=E(_wx);if(!_wy._){return E(_ww);}else{var _wz=_41(_4b(_ww,_wq),_wy.a);_ww=_wz;_wx=_wy.b;continue;}}};return _wv(_wk,_wt);}else{var _wA=_4b(_wq,_wq);if(!(_wu%2)){var _wB=_wf(_wq,_wt);_wm=_wA;_wn=quot(_wu+1|0,2);_wo=_wB;return __continue;}else{var _wB=_wf(_wq,new T2(1,_wk,_wt));_wm=_wA;_wn=quot(_wu+1|0,2);_wo=_wB;return __continue;}}}}})(_wm,_wn,_wo);if(_wp!=__continue){return _wp;}}},_wC=function(_wD,_wE){return _wl(_wD,new T(function(){return _6o(_wE,0);},1),_hg(_wc,_wE));},_wF=function(_wG){var _wH=new T(function(){var _wI=new T(function(){var _wJ=function(_wK){return C > 19 ? new F(function(){return A1(_wG,new T1(1,new T(function(){return _wC(_wb,_wK);})));}) : (++C,A1(_wG,new T1(1,new T(function(){return _wC(_wb,_wK);}))));};return new T1(1,_vc(10,_wJ));}),_wL=function(_wM){if(E(_wM)==43){var _wN=function(_wO){return C > 19 ? new F(function(){return A1(_wG,new T1(1,new T(function(){return _wC(_wb,_wO);})));}) : (++C,A1(_wG,new T1(1,new T(function(){return _wC(_wb,_wO);}))));};return new T1(1,_vc(10,_wN));}else{return new T0(2);}},_wP=function(_wQ){if(E(_wQ)==45){var _wR=function(_wS){return C > 19 ? new F(function(){return A1(_wG,new T1(1,new T(function(){return _7z(_wC(_wb,_wS));})));}) : (++C,A1(_wG,new T1(1,new T(function(){return _7z(_wC(_wb,_wS));}))));};return new T1(1,_vc(10,_wR));}else{return new T0(2);}};return _tu(_tu(new T1(0,_wP),new T1(0,_wL)),_wI);});return _tu(new T1(0,function(_wT){return (E(_wT)==101)?E(_wH):new T0(2);}),new T1(0,function(_wU){return (E(_wU)==69)?E(_wH):new T0(2);}));},_wV=function(_wW){var _wX=function(_wY){return C > 19 ? new F(function(){return A1(_wW,new T1(1,_wY));}) : (++C,A1(_wW,new T1(1,_wY)));};return function(_wZ){return (E(_wZ)==46)?new T1(1,_vc(10,_wX)):new T0(2);};},_x0=function(_x1){return new T1(0,_wV(_x1));},_x2=function(_x3){var _x4=function(_x5){var _x6=function(_x7){return new T1(1,_ux(_wF,_w7,function(_x8){return C > 19 ? new F(function(){return A1(_x3,new T1(5,new T3(1,_x5,_x7,_x8)));}) : (++C,A1(_x3,new T1(5,new T3(1,_x5,_x7,_x8))));}));};return new T1(1,_ux(_x0,_w9,_x6));};return _vc(10,_x4);},_x9=function(_xa){return new T1(1,_x2(_xa));},_xb=function(_xc){return E(E(_xc).a);},_xd=function(_xe,_xf,_xg){while(1){var _xh=E(_xg);if(!_xh._){return false;}else{if(!B(A3(_xb,_xe,_xf,_xh.a))){_xg=_xh.b;continue;}else{return true;}}}},_xi=new T(function(){return unCStr("!@#$%&*+./<=>?\\^|:-~");}),_xj=function(_xk){return _xd(_u0,_xk,_xi);},_xl=function(_xm){var _xn=new T(function(){return B(A1(_xm,8));}),_xo=new T(function(){return B(A1(_xm,16));});return function(_xp){switch(E(_xp)){case 79:return E(_xn);case 88:return E(_xo);case 111:return E(_xn);case 120:return E(_xo);default:return new T0(2);}};},_xq=function(_xr){return new T1(0,_xl(_xr));},_xs=function(_xt){return C > 19 ? new F(function(){return A1(_xt,10);}) : (++C,A1(_xt,10));},_xu=function(_xv){return new T0(2);},_xw=function(_xx){var _xy=E(_xx);if(!_xy._){return _xu;}else{var _xz=_xy.a,_xA=E(_xy.b);if(!_xA._){return E(_xz);}else{var _xB=new T(function(){return _xw(_xA);}),_xC=function(_xD){return _tu(B(A1(_xz,_xD)),new T(function(){return B(A1(_xB,_xD));}));};return _xC;}}},_xE=function(_xF,_xG){var _xH=function(_xI,_xJ,_xK){var _xL=E(_xI);if(!_xL._){return C > 19 ? new F(function(){return A1(_xK,_xF);}) : (++C,A1(_xK,_xF));}else{var _xM=E(_xJ);if(!_xM._){return new T0(2);}else{if(E(_xL.a)!=E(_xM.a)){return new T0(2);}else{var _xN=new T(function(){return B(_xH(_xL.b,_xM.b,_xK));});return new T1(0,function(_xO){return E(_xN);});}}}};return function(_xP){return C > 19 ? new F(function(){return _xH(_xF,_xP,_xG);}) : (++C,_xH(_xF,_xP,_xG));};},_xQ=new T(function(){return unCStr("SO");}),_xR=function(_xS){var _xT=new T(function(){return B(A1(_xS,14));});return new T1(1,_xE(_xQ,function(_xU){return E(_xT);}));},_xV=new T(function(){return unCStr("SOH");}),_xW=function(_xX){var _xY=new T(function(){return B(A1(_xX,1));});return new T1(1,_xE(_xV,function(_xZ){return E(_xY);}));},_y0=new T(function(){return unCStr("NUL");}),_y1=function(_y2){var _y3=new T(function(){return B(A1(_y2,0));});return new T1(1,_xE(_y0,function(_y4){return E(_y3);}));},_y5=new T(function(){return unCStr("STX");}),_y6=function(_y7){var _y8=new T(function(){return B(A1(_y7,2));});return new T1(1,_xE(_y5,function(_y9){return E(_y8);}));},_ya=new T(function(){return unCStr("ETX");}),_yb=function(_yc){var _yd=new T(function(){return B(A1(_yc,3));});return new T1(1,_xE(_ya,function(_ye){return E(_yd);}));},_yf=new T(function(){return unCStr("EOT");}),_yg=function(_yh){var _yi=new T(function(){return B(A1(_yh,4));});return new T1(1,_xE(_yf,function(_yj){return E(_yi);}));},_yk=new T(function(){return unCStr("ENQ");}),_yl=function(_ym){var _yn=new T(function(){return B(A1(_ym,5));});return new T1(1,_xE(_yk,function(_yo){return E(_yn);}));},_yp=new T(function(){return unCStr("ACK");}),_yq=function(_yr){var _ys=new T(function(){return B(A1(_yr,6));});return new T1(1,_xE(_yp,function(_yt){return E(_ys);}));},_yu=new T(function(){return unCStr("BEL");}),_yv=function(_yw){var _yx=new T(function(){return B(A1(_yw,7));});return new T1(1,_xE(_yu,function(_yy){return E(_yx);}));},_yz=new T(function(){return unCStr("BS");}),_yA=function(_yB){var _yC=new T(function(){return B(A1(_yB,8));});return new T1(1,_xE(_yz,function(_yD){return E(_yC);}));},_yE=new T(function(){return unCStr("HT");}),_yF=function(_yG){var _yH=new T(function(){return B(A1(_yG,9));});return new T1(1,_xE(_yE,function(_yI){return E(_yH);}));},_yJ=new T(function(){return unCStr("LF");}),_yK=function(_yL){var _yM=new T(function(){return B(A1(_yL,10));});return new T1(1,_xE(_yJ,function(_yN){return E(_yM);}));},_yO=new T(function(){return unCStr("VT");}),_yP=function(_yQ){var _yR=new T(function(){return B(A1(_yQ,11));});return new T1(1,_xE(_yO,function(_yS){return E(_yR);}));},_yT=new T(function(){return unCStr("FF");}),_yU=function(_yV){var _yW=new T(function(){return B(A1(_yV,12));});return new T1(1,_xE(_yT,function(_yX){return E(_yW);}));},_yY=new T(function(){return unCStr("CR");}),_yZ=function(_z0){var _z1=new T(function(){return B(A1(_z0,13));});return new T1(1,_xE(_yY,function(_z2){return E(_z1);}));},_z3=new T(function(){return unCStr("SI");}),_z4=function(_z5){var _z6=new T(function(){return B(A1(_z5,15));});return new T1(1,_xE(_z3,function(_z7){return E(_z6);}));},_z8=new T(function(){return unCStr("DLE");}),_z9=function(_za){var _zb=new T(function(){return B(A1(_za,16));});return new T1(1,_xE(_z8,function(_zc){return E(_zb);}));},_zd=new T(function(){return unCStr("DC1");}),_ze=function(_zf){var _zg=new T(function(){return B(A1(_zf,17));});return new T1(1,_xE(_zd,function(_zh){return E(_zg);}));},_zi=new T(function(){return unCStr("DC2");}),_zj=function(_zk){var _zl=new T(function(){return B(A1(_zk,18));});return new T1(1,_xE(_zi,function(_zm){return E(_zl);}));},_zn=new T(function(){return unCStr("DC3");}),_zo=function(_zp){var _zq=new T(function(){return B(A1(_zp,19));});return new T1(1,_xE(_zn,function(_zr){return E(_zq);}));},_zs=new T(function(){return unCStr("DC4");}),_zt=function(_zu){var _zv=new T(function(){return B(A1(_zu,20));});return new T1(1,_xE(_zs,function(_zw){return E(_zv);}));},_zx=new T(function(){return unCStr("NAK");}),_zy=function(_zz){var _zA=new T(function(){return B(A1(_zz,21));});return new T1(1,_xE(_zx,function(_zB){return E(_zA);}));},_zC=new T(function(){return unCStr("SYN");}),_zD=function(_zE){var _zF=new T(function(){return B(A1(_zE,22));});return new T1(1,_xE(_zC,function(_zG){return E(_zF);}));},_zH=new T(function(){return unCStr("ETB");}),_zI=function(_zJ){var _zK=new T(function(){return B(A1(_zJ,23));});return new T1(1,_xE(_zH,function(_zL){return E(_zK);}));},_zM=new T(function(){return unCStr("CAN");}),_zN=function(_zO){var _zP=new T(function(){return B(A1(_zO,24));});return new T1(1,_xE(_zM,function(_zQ){return E(_zP);}));},_zR=new T(function(){return unCStr("EM");}),_zS=function(_zT){var _zU=new T(function(){return B(A1(_zT,25));});return new T1(1,_xE(_zR,function(_zV){return E(_zU);}));},_zW=new T(function(){return unCStr("SUB");}),_zX=function(_zY){var _zZ=new T(function(){return B(A1(_zY,26));});return new T1(1,_xE(_zW,function(_A0){return E(_zZ);}));},_A1=new T(function(){return unCStr("ESC");}),_A2=function(_A3){var _A4=new T(function(){return B(A1(_A3,27));});return new T1(1,_xE(_A1,function(_A5){return E(_A4);}));},_A6=new T(function(){return unCStr("FS");}),_A7=function(_A8){var _A9=new T(function(){return B(A1(_A8,28));});return new T1(1,_xE(_A6,function(_Aa){return E(_A9);}));},_Ab=new T(function(){return unCStr("GS");}),_Ac=function(_Ad){var _Ae=new T(function(){return B(A1(_Ad,29));});return new T1(1,_xE(_Ab,function(_Af){return E(_Ae);}));},_Ag=new T(function(){return unCStr("RS");}),_Ah=function(_Ai){var _Aj=new T(function(){return B(A1(_Ai,30));});return new T1(1,_xE(_Ag,function(_Ak){return E(_Aj);}));},_Al=new T(function(){return unCStr("US");}),_Am=function(_An){var _Ao=new T(function(){return B(A1(_An,31));});return new T1(1,_xE(_Al,function(_Ap){return E(_Ao);}));},_Aq=new T(function(){return unCStr("SP");}),_Ar=function(_As){var _At=new T(function(){return B(A1(_As,32));});return new T1(1,_xE(_Aq,function(_Au){return E(_At);}));},_Av=new T(function(){return unCStr("DEL");}),_Aw=function(_Ax){var _Ay=new T(function(){return B(A1(_Ax,127));});return new T1(1,_xE(_Av,function(_Az){return E(_Ay);}));},_AA=new T(function(){return _xw(new T2(1,function(_AB){return new T1(1,_ux(_xW,_xR,_AB));},new T2(1,_y1,new T2(1,_y6,new T2(1,_yb,new T2(1,_yg,new T2(1,_yl,new T2(1,_yq,new T2(1,_yv,new T2(1,_yA,new T2(1,_yF,new T2(1,_yK,new T2(1,_yP,new T2(1,_yU,new T2(1,_yZ,new T2(1,_z4,new T2(1,_z9,new T2(1,_ze,new T2(1,_zj,new T2(1,_zo,new T2(1,_zt,new T2(1,_zy,new T2(1,_zD,new T2(1,_zI,new T2(1,_zN,new T2(1,_zS,new T2(1,_zX,new T2(1,_A2,new T2(1,_A7,new T2(1,_Ac,new T2(1,_Ah,new T2(1,_Am,new T2(1,_Ar,new T2(1,_Aw,__Z))))))))))))))))))))))))))))))))));}),_AC=function(_AD){var _AE=new T(function(){return B(A1(_AD,7));}),_AF=new T(function(){return B(A1(_AD,8));}),_AG=new T(function(){return B(A1(_AD,9));}),_AH=new T(function(){return B(A1(_AD,10));}),_AI=new T(function(){return B(A1(_AD,11));}),_AJ=new T(function(){return B(A1(_AD,12));}),_AK=new T(function(){return B(A1(_AD,13));}),_AL=new T(function(){return B(A1(_AD,92));}),_AM=new T(function(){return B(A1(_AD,39));}),_AN=new T(function(){return B(A1(_AD,34));}),_AO=new T(function(){var _AP=function(_AQ){var _AR=new T(function(){return _4v(E(_AQ));}),_AS=function(_AT){var _AU=_wC(_AR,_AT);if(!_3i(_AU,new T1(0,1114111))){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_AD,new T(function(){var _AV=_3c(_AU);if(_AV>>>0>1114111){return _bg(_AV);}else{return _AV;}}));}) : (++C,A1(_AD,new T(function(){var _AV=_3c(_AU);if(_AV>>>0>1114111){return _bg(_AV);}else{return _AV;}})));}};return new T1(1,_vc(_AQ,_AS));},_AW=new T(function(){var _AX=new T(function(){return B(A1(_AD,31));}),_AY=new T(function(){return B(A1(_AD,30));}),_AZ=new T(function(){return B(A1(_AD,29));}),_B0=new T(function(){return B(A1(_AD,28));}),_B1=new T(function(){return B(A1(_AD,27));}),_B2=new T(function(){return B(A1(_AD,26));}),_B3=new T(function(){return B(A1(_AD,25));}),_B4=new T(function(){return B(A1(_AD,24));}),_B5=new T(function(){return B(A1(_AD,23));}),_B6=new T(function(){return B(A1(_AD,22));}),_B7=new T(function(){return B(A1(_AD,21));}),_B8=new T(function(){return B(A1(_AD,20));}),_B9=new T(function(){return B(A1(_AD,19));}),_Ba=new T(function(){return B(A1(_AD,18));}),_Bb=new T(function(){return B(A1(_AD,17));}),_Bc=new T(function(){return B(A1(_AD,16));}),_Bd=new T(function(){return B(A1(_AD,15));}),_Be=new T(function(){return B(A1(_AD,14));}),_Bf=new T(function(){return B(A1(_AD,6));}),_Bg=new T(function(){return B(A1(_AD,5));}),_Bh=new T(function(){return B(A1(_AD,4));}),_Bi=new T(function(){return B(A1(_AD,3));}),_Bj=new T(function(){return B(A1(_AD,2));}),_Bk=new T(function(){return B(A1(_AD,1));}),_Bl=new T(function(){return B(A1(_AD,0));}),_Bm=function(_Bn){switch(E(_Bn)){case 64:return E(_Bl);case 65:return E(_Bk);case 66:return E(_Bj);case 67:return E(_Bi);case 68:return E(_Bh);case 69:return E(_Bg);case 70:return E(_Bf);case 71:return E(_AE);case 72:return E(_AF);case 73:return E(_AG);case 74:return E(_AH);case 75:return E(_AI);case 76:return E(_AJ);case 77:return E(_AK);case 78:return E(_Be);case 79:return E(_Bd);case 80:return E(_Bc);case 81:return E(_Bb);case 82:return E(_Ba);case 83:return E(_B9);case 84:return E(_B8);case 85:return E(_B7);case 86:return E(_B6);case 87:return E(_B5);case 88:return E(_B4);case 89:return E(_B3);case 90:return E(_B2);case 91:return E(_B1);case 92:return E(_B0);case 93:return E(_AZ);case 94:return E(_AY);case 95:return E(_AX);default:return new T0(2);}};return _tu(new T1(0,function(_Bo){return (E(_Bo)==94)?E(new T1(0,_Bm)):new T0(2);}),new T(function(){return B(A1(_AA,_AD));}));});return _tu(new T1(1,_ux(_xq,_xs,_AP)),_AW);});return _tu(new T1(0,function(_Bp){switch(E(_Bp)){case 34:return E(_AN);case 39:return E(_AM);case 92:return E(_AL);case 97:return E(_AE);case 98:return E(_AF);case 102:return E(_AJ);case 110:return E(_AH);case 114:return E(_AK);case 116:return E(_AG);case 118:return E(_AI);default:return new T0(2);}}),_AO);},_Bq=function(_Br){return C > 19 ? new F(function(){return A1(_Br,0);}) : (++C,A1(_Br,0));},_Bs=function(_Bt){var _Bu=E(_Bt);if(!_Bu._){return _Bq;}else{var _Bv=E(_Bu.a),_Bw=_Bv>>>0,_Bx=new T(function(){return _Bs(_Bu.b);});if(_Bw>887){var _By=u_iswspace(_Bv);if(!E(_By)){return _Bq;}else{var _Bz=function(_BA){var _BB=new T(function(){return B(A1(_Bx,_BA));});return new T1(0,function(_BC){return E(_BB);});};return _Bz;}}else{if(_Bw==32){var _BD=function(_BE){var _BF=new T(function(){return B(A1(_Bx,_BE));});return new T1(0,function(_BG){return E(_BF);});};return _BD;}else{if(_Bw-9>>>0>4){if(_Bw==160){var _BH=function(_BI){var _BJ=new T(function(){return B(A1(_Bx,_BI));});return new T1(0,function(_BK){return E(_BJ);});};return _BH;}else{return _Bq;}}else{var _BL=function(_BM){var _BN=new T(function(){return B(A1(_Bx,_BM));});return new T1(0,function(_BO){return E(_BN);});};return _BL;}}}}},_BP=function(_BQ){var _BR=new T(function(){return B(_BP(_BQ));}),_BS=function(_BT){return (E(_BT)==92)?E(_BR):new T0(2);},_BU=function(_BV){return E(new T1(0,_BS));},_BW=new T1(1,function(_BX){return C > 19 ? new F(function(){return A2(_Bs,_BX,_BU);}) : (++C,A2(_Bs,_BX,_BU));}),_BY=new T(function(){return B(_AC(function(_BZ){return C > 19 ? new F(function(){return A1(_BQ,new T2(0,_BZ,true));}) : (++C,A1(_BQ,new T2(0,_BZ,true)));}));}),_C0=function(_C1){var _C2=E(_C1);if(_C2==38){return E(_BR);}else{var _C3=_C2>>>0;if(_C3>887){var _C4=u_iswspace(_C2);return (E(_C4)==0)?new T0(2):E(_BW);}else{return (_C3==32)?E(_BW):(_C3-9>>>0>4)?(_C3==160)?E(_BW):new T0(2):E(_BW);}}};return _tu(new T1(0,function(_C5){return (E(_C5)==92)?E(new T1(0,_C0)):new T0(2);}),new T1(0,function(_C6){var _C7=E(_C6);if(_C7==92){return E(_BY);}else{return C > 19 ? new F(function(){return A1(_BQ,new T2(0,_C7,false));}) : (++C,A1(_BQ,new T2(0,_C7,false)));}}));},_C8=function(_C9,_Ca){var _Cb=new T(function(){return B(A1(_Ca,new T1(1,new T(function(){return B(A1(_C9,__Z));}))));}),_Cc=function(_Cd){var _Ce=E(_Cd),_Cf=E(_Ce.a);if(_Cf==34){if(!E(_Ce.b)){return E(_Cb);}else{return C > 19 ? new F(function(){return _C8(function(_Cg){return C > 19 ? new F(function(){return A1(_C9,new T2(1,_Cf,_Cg));}) : (++C,A1(_C9,new T2(1,_Cf,_Cg)));},_Ca);}) : (++C,_C8(function(_Cg){return C > 19 ? new F(function(){return A1(_C9,new T2(1,_Cf,_Cg));}) : (++C,A1(_C9,new T2(1,_Cf,_Cg)));},_Ca));}}else{return C > 19 ? new F(function(){return _C8(function(_Ch){return C > 19 ? new F(function(){return A1(_C9,new T2(1,_Cf,_Ch));}) : (++C,A1(_C9,new T2(1,_Cf,_Ch)));},_Ca);}) : (++C,_C8(function(_Ch){return C > 19 ? new F(function(){return A1(_C9,new T2(1,_Cf,_Ch));}) : (++C,A1(_C9,new T2(1,_Cf,_Ch)));},_Ca));}};return C > 19 ? new F(function(){return _BP(_Cc);}) : (++C,_BP(_Cc));},_Ci=new T(function(){return unCStr("_\'");}),_Cj=function(_Ck){var _Cl=u_iswalnum(_Ck);if(!E(_Cl)){return _xd(_u0,_Ck,_Ci);}else{return true;}},_Cm=function(_Cn){return _Cj(E(_Cn));},_Co=new T(function(){return unCStr(",;()[]{}`");}),_Cp=new T(function(){return unCStr("=>");}),_Cq=new T(function(){return unCStr("~");}),_Cr=new T(function(){return unCStr("@");}),_Cs=new T(function(){return unCStr("->");}),_Ct=new T(function(){return unCStr("<-");}),_Cu=new T(function(){return unCStr("|");}),_Cv=new T(function(){return unCStr("\\");}),_Cw=new T(function(){return unCStr("=");}),_Cx=new T(function(){return unCStr("::");}),_Cy=new T(function(){return unCStr("..");}),_Cz=function(_CA){var _CB=new T(function(){return B(A1(_CA,new T0(6)));}),_CC=new T(function(){var _CD=new T(function(){var _CE=function(_CF){var _CG=new T(function(){return B(A1(_CA,new T1(0,_CF)));});return new T1(0,function(_CH){return (E(_CH)==39)?E(_CG):new T0(2);});};return B(_AC(_CE));}),_CI=function(_CJ){var _CK=E(_CJ);switch(_CK){case 39:return new T0(2);case 92:return E(_CD);default:var _CL=new T(function(){return B(A1(_CA,new T1(0,_CK)));});return new T1(0,function(_CM){return (E(_CM)==39)?E(_CL):new T0(2);});}},_CN=new T(function(){var _CO=new T(function(){return B(_C8(_1V,_CA));}),_CP=new T(function(){var _CQ=new T(function(){var _CR=new T(function(){var _CS=function(_CT){var _CU=E(_CT),_CV=u_iswalpha(_CU);return (E(_CV)==0)?(_CU==95)?new T1(1,_uX(_Cm,function(_CW){return C > 19 ? new F(function(){return A1(_CA,new T1(3,new T2(1,_CU,_CW)));}) : (++C,A1(_CA,new T1(3,new T2(1,_CU,_CW))));})):new T0(2):new T1(1,_uX(_Cm,function(_CX){return C > 19 ? new F(function(){return A1(_CA,new T1(3,new T2(1,_CU,_CX)));}) : (++C,A1(_CA,new T1(3,new T2(1,_CU,_CX))));}));};return _tu(new T1(0,_CS),new T(function(){return new T1(1,_ux(_w5,_x9,_CA));}));}),_CY=function(_CZ){return (!_xd(_u0,_CZ,_xi))?new T0(2):new T1(1,_uX(_xj,function(_D0){var _D1=new T2(1,_CZ,_D0);if(!_xd(new T2(0,_u5,_ua),_D1,new T2(1,_Cy,new T2(1,_Cx,new T2(1,_Cw,new T2(1,_Cv,new T2(1,_Cu,new T2(1,_Ct,new T2(1,_Cs,new T2(1,_Cr,new T2(1,_Cq,new T2(1,_Cp,__Z)))))))))))){return C > 19 ? new F(function(){return A1(_CA,new T1(4,_D1));}) : (++C,A1(_CA,new T1(4,_D1)));}else{return C > 19 ? new F(function(){return A1(_CA,new T1(2,_D1));}) : (++C,A1(_CA,new T1(2,_D1)));}}));};return _tu(new T1(0,_CY),_CR);});return _tu(new T1(0,function(_D2){if(!_xd(_u0,_D2,_Co)){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_CA,new T1(2,new T2(1,_D2,__Z)));}) : (++C,A1(_CA,new T1(2,new T2(1,_D2,__Z))));}}),_CQ);});return _tu(new T1(0,function(_D3){return (E(_D3)==34)?E(_CO):new T0(2);}),_CP);});return _tu(new T1(0,function(_D4){return (E(_D4)==39)?E(new T1(0,_CI)):new T0(2);}),_CN);});return _tu(new T1(1,function(_D5){return (E(_D5)._==0)?E(_CB):new T0(2);}),_CC);},_D6=function(_D7,_D8){var _D9=new T(function(){var _Da=new T(function(){var _Db=function(_Dc){var _Dd=new T(function(){var _De=new T(function(){return B(A1(_D8,_Dc));});return B(_Cz(function(_Df){var _Dg=E(_Df);return (_Dg._==2)?(!_qX(_Dg.a,_tZ))?new T0(2):E(_De):new T0(2);}));}),_Dh=function(_Di){return E(_Dd);};return new T1(1,function(_Dj){return C > 19 ? new F(function(){return A2(_Bs,_Dj,_Dh);}) : (++C,A2(_Bs,_Dj,_Dh));});};return B(A2(_D7,0,_Db));});return B(_Cz(function(_Dk){var _Dl=E(_Dk);return (_Dl._==2)?(!_qX(_Dl.a,_tY))?new T0(2):E(_Da):new T0(2);}));}),_Dm=function(_Dn){return E(_D9);};return function(_Do){return C > 19 ? new F(function(){return A2(_Bs,_Do,_Dm);}) : (++C,A2(_Bs,_Do,_Dm));};},_Dp=function(_Dq,_Dr){var _Ds=function(_Dt){var _Du=new T(function(){return B(A1(_Dq,_Dt));}),_Dv=function(_Dw){return _tu(B(A1(_Du,_Dw)),new T(function(){return new T1(1,_D6(_Ds,_Dw));}));};return _Dv;},_Dx=new T(function(){return B(A1(_Dq,_Dr));}),_Dy=function(_Dz){return _tu(B(A1(_Dx,_Dz)),new T(function(){return new T1(1,_D6(_Ds,_Dz));}));};return _Dy;},_DA=function(_DB,_DC){var _DD=function(_DE,_DF){var _DG=function(_DH){return C > 19 ? new F(function(){return A1(_DF,new T(function(){return  -E(_DH);}));}) : (++C,A1(_DF,new T(function(){return  -E(_DH);})));},_DI=new T(function(){return B(_Cz(function(_DJ){return C > 19 ? new F(function(){return A3(_DB,_DJ,_DE,_DG);}) : (++C,A3(_DB,_DJ,_DE,_DG));}));}),_DK=function(_DL){return E(_DI);},_DM=function(_DN){return C > 19 ? new F(function(){return A2(_Bs,_DN,_DK);}) : (++C,A2(_Bs,_DN,_DK));},_DO=new T(function(){return B(_Cz(function(_DP){var _DQ=E(_DP);if(_DQ._==4){var _DR=E(_DQ.a);if(!_DR._){return C > 19 ? new F(function(){return A3(_DB,_DQ,_DE,_DF);}) : (++C,A3(_DB,_DQ,_DE,_DF));}else{if(E(_DR.a)==45){if(!E(_DR.b)._){return E(new T1(1,_DM));}else{return C > 19 ? new F(function(){return A3(_DB,_DQ,_DE,_DF);}) : (++C,A3(_DB,_DQ,_DE,_DF));}}else{return C > 19 ? new F(function(){return A3(_DB,_DQ,_DE,_DF);}) : (++C,A3(_DB,_DQ,_DE,_DF));}}}else{return C > 19 ? new F(function(){return A3(_DB,_DQ,_DE,_DF);}) : (++C,A3(_DB,_DQ,_DE,_DF));}}));}),_DS=function(_DT){return E(_DO);};return new T1(1,function(_DU){return C > 19 ? new F(function(){return A2(_Bs,_DU,_DS);}) : (++C,A2(_Bs,_DU,_DS));});};return _Dp(_DD,_DC);},_DV=function(_DW){var _DX=E(_DW);if(!_DX._){var _DY=_DX.b,_DZ=new T(function(){return _wl(new T(function(){return _4v(E(_DX.a));}),new T(function(){return _6o(_DY,0);},1),_hg(_wc,_DY));});return new T1(1,_DZ);}else{return (E(_DX.b)._==0)?(E(_DX.c)._==0)?new T1(1,new T(function(){return _wC(_wb,_DX.a);})):__Z:__Z;}},_E0=function(_E1,_E2){return new T0(2);},_E3=function(_E4){var _E5=E(_E4);if(_E5._==5){var _E6=_DV(_E5.a);if(!_E6._){return _E0;}else{var _E7=new T(function(){return _3c(_E6.a);});return function(_E8,_E9){return C > 19 ? new F(function(){return A1(_E9,_E7);}) : (++C,A1(_E9,_E7));};}}else{return _E0;}},_Ea=function(_Eb){var _Ec=function(_Ed){return E(new T2(3,_Eb,_uo));};return new T1(1,function(_Ee){return C > 19 ? new F(function(){return A2(_Bs,_Ee,_Ec);}) : (++C,A2(_Bs,_Ee,_Ec));});},_Ef=new T(function(){return B(A3(_DA,_E3,0,_Ea));}),_Eg=new T(function(){return err(_sr);}),_Eh=new T(function(){return err(_st);}),_Ei=function(_Ej,_Ek){var _El=function(_Em,_En){var _Eo=function(_Ep){return C > 19 ? new F(function(){return A1(_En,new T(function(){return _7z(_Ep);}));}) : (++C,A1(_En,new T(function(){return _7z(_Ep);})));},_Eq=new T(function(){return B(_Cz(function(_Er){return C > 19 ? new F(function(){return A3(_Ej,_Er,_Em,_Eo);}) : (++C,A3(_Ej,_Er,_Em,_Eo));}));}),_Es=function(_Et){return E(_Eq);},_Eu=function(_Ev){return C > 19 ? new F(function(){return A2(_Bs,_Ev,_Es);}) : (++C,A2(_Bs,_Ev,_Es));},_Ew=new T(function(){return B(_Cz(function(_Ex){var _Ey=E(_Ex);if(_Ey._==4){var _Ez=E(_Ey.a);if(!_Ez._){return C > 19 ? new F(function(){return A3(_Ej,_Ey,_Em,_En);}) : (++C,A3(_Ej,_Ey,_Em,_En));}else{if(E(_Ez.a)==45){if(!E(_Ez.b)._){return E(new T1(1,_Eu));}else{return C > 19 ? new F(function(){return A3(_Ej,_Ey,_Em,_En);}) : (++C,A3(_Ej,_Ey,_Em,_En));}}else{return C > 19 ? new F(function(){return A3(_Ej,_Ey,_Em,_En);}) : (++C,A3(_Ej,_Ey,_Em,_En));}}}else{return C > 19 ? new F(function(){return A3(_Ej,_Ey,_Em,_En);}) : (++C,A3(_Ej,_Ey,_Em,_En));}}));}),_EA=function(_EB){return E(_Ew);};return new T1(1,function(_EC){return C > 19 ? new F(function(){return A2(_Bs,_EC,_EA);}) : (++C,A2(_Bs,_EC,_EA));});};return _Dp(_El,_Ek);},_ED=function(_EE){var _EF=E(_EE);if(_EF._==5){var _EG=_DV(_EF.a);return (_EG._==0)?_E0:function(_EH,_EI){return C > 19 ? new F(function(){return A1(_EI,_EG.a);}) : (++C,A1(_EI,_EG.a));};}else{return _E0;}},_EJ=new T(function(){return B(A3(_Ei,_ED,0,_Ea));}),_EK=new T(function(){return _3t(_sq,new T1(0,0));}),_EL=function(_EM,_EN){while(1){var _EO=E(_EM);if(!_EO._){return E(_EN);}else{_EM=_EO.b;_EN=_EO.a;continue;}}},_EP=function(_EQ){while(1){var _ER=(function(_ES){var _ET=E(_ES);if(!_ET._){return __Z;}else{var _EU=_ET.b,_EV=E(_ET.a);if(!E(_EV.b)._){return new T2(1,_EV.a,new T(function(){return _EP(_EU);}));}else{_EQ=_EU;return __continue;}}})(_EQ);if(_ER!=__continue){return _ER;}}},_EW=function(_EX,_EY){var _EZ=function(_F0){while(1){var _F1=(function(_F2){var _F3=E(_F2);if(!_F3._){return __Z;}else{var _F4=_F3.b,_F5=E(_F3.a),_F6=_F5.b;switch(E(_F5.a)){case 65:var _F7=new T(function(){var _F8=new T(function(){return _hg(_bl,_F6);}),_F9=function(_Fa,_Fb){while(1){var _Fc=(function(_Fd,_Fe){var _Ff=E(_Fd);if(!_Ff._){return __Z;}else{var _Fg=_Ff.b;if(!_qX(_F8,_Ff.a)){var _Fh=_Fe+1|0;_Fa=_Fg;_Fb=_Fh;return __continue;}else{return new T2(1,_Fe,new T(function(){return _F9(_Fg,_Fe+1|0);}));}}})(_Fa,_Fb);if(_Fc!=__continue){return _Fc;}}},_Fi=_F9(_hg(_sv,E(_EX).a),0);if(!_Fi._){return E(_rk);}else{return 1+_3P(E(_Fi.a)+6|0,7)|0;}});return new T2(1,new T1(5,_F7),new T(function(){return _EZ(_F4);}));case 66:var _Fj=new T(function(){var _Fk=new T(function(){return _hg(_bl,_F6);}),_Fl=function(_Fm,_Fn){while(1){var _Fo=(function(_Fp,_Fq){var _Fr=E(_Fp);if(!_Fr._){return __Z;}else{var _Fs=_Fr.b;if(!_qX(_Fk,_Fr.a)){var _Ft=_Fq+1|0;_Fm=_Fs;_Fn=_Ft;return __continue;}else{return new T2(1,_Fq,new T(function(){return _Fl(_Fs,_Fq+1|0);}));}}})(_Fm,_Fn);if(_Fo!=__continue){return _Fo;}}},_Fu=_Fl(_hg(_sv,E(_EX).b),0);if(!_Fu._){return E(_rk);}else{return 1+E(_Fu.a)|0;}});return new T2(1,new T1(2,_Fj),new T(function(){return _EZ(_F4);}));case 67:return new T2(1,new T1(0,new T(function(){var _Fv=_EP(_tk(_EJ,_F6));if(!_Fv._){return E(_Eg);}else{if(!E(_Fv.b)._){return E(_Fv.a);}else{return E(_Eh);}}})),new T(function(){return _EZ(_F4);}));case 71:var _Fw=new T(function(){var _Fx=_EP(_tk(_EJ,_F6));if(!_Fx._){return E(_Eg);}else{if(!E(_Fx.b)._){return E(_Fx.a);}else{return E(_Eh);}}});return new T2(1,new T1(0,new T(function(){if(!E(_EK)){return _2B(_Fw,_sq);}else{return E(_39);}})),new T2(1,new T1(1,new T(function(){if(!E(_EK)){return _3T(_Fw,_sq);}else{return E(_39);}})),new T(function(){return _EZ(_F4);})));case 85:return new T2(1,new T2(6,1,new T(function(){var _Fy=_EP(_tk(_Ef,_F6));if(!_Fy._){return E(_ss);}else{if(!E(_Fy.b)._){return E(_Fy.a);}else{return E(_su);}}})),new T(function(){return _EZ(_F4);}));case 86:return new T2(1,new T2(6,0,new T(function(){var _Fz=_EP(_tk(_Ef,_F6));if(!_Fz._){return E(_ss);}else{if(!E(_Fz.b)._){return E(_Fz.a);}else{return E(_su);}}})),new T(function(){return _EZ(_F4);}));case 87:return new T2(1,new T2(6,2,new T(function(){var _FA=_EP(_tk(_Ef,_F6));if(!_FA._){return E(_ss);}else{if(!E(_FA.b)._){return E(_FA.a);}else{return E(_su);}}})),new T(function(){return _EZ(_F4);}));case 89:var _FB=new T(function(){var _FC=_EP(_tk(_EJ,_F6));if(!_FC._){return E(_Eg);}else{if(!E(_FC.b)._){return E(_FC.a);}else{return E(_Eh);}}});return new T2(1,new T1(0,new T(function(){if(!E(_EK)){return _2B(_FB,_sq);}else{return E(_39);}})),new T2(1,new T1(1,new T(function(){if(!E(_EK)){return _3T(_FB,_sq);}else{return E(_39);}})),new T(function(){return _EZ(_F4);})));case 97:var _FD=new T(function(){var _FE=new T(function(){return _hg(_bl,_F6);}),_FF=function(_FG,_FH){while(1){var _FI=(function(_FJ,_FK){var _FL=E(_FJ);if(!_FL._){return __Z;}else{var _FM=_FL.b;if(!_qX(_FE,_FL.a)){var _FN=_FK+1|0;_FG=_FM;_FH=_FN;return __continue;}else{return new T2(1,_FK,new T(function(){return _FF(_FM,_FK+1|0);}));}}})(_FG,_FH);if(_FI!=__continue){return _FI;}}},_FO=_FF(_hg(_so,E(_EX).a),0);if(!_FO._){return E(_rk);}else{return 1+_3P(E(_FO.a)+6|0,7)|0;}});return new T2(1,new T1(5,_FD),new T(function(){return _EZ(_F4);}));case 98:var _FP=new T(function(){var _FQ=new T(function(){return _hg(_bl,_F6);}),_FR=function(_FS,_FT){while(1){var _FU=(function(_FV,_FW){var _FX=E(_FV);if(!_FX._){return __Z;}else{var _FY=_FX.b;if(!_qX(_FQ,_FX.a)){var _FZ=_FW+1|0;_FS=_FY;_FT=_FZ;return __continue;}else{return new T2(1,_FW,new T(function(){return _FR(_FY,_FW+1|0);}));}}})(_FS,_FT);if(_FU!=__continue){return _FU;}}},_G0=_FR(_hg(_so,E(_EX).b),0);if(!_G0._){return E(_rk);}else{return 1+E(_G0.a)|0;}});return new T2(1,new T1(2,_FP),new T(function(){return _EZ(_F4);}));case 100:return new T2(1,new T1(3,new T(function(){var _G1=_EP(_tk(_Ef,_F6));if(!_G1._){return E(_ss);}else{if(!E(_G1.b)._){return E(_G1.a);}else{return E(_su);}}})),new T(function(){return _EZ(_F4);}));case 101:return new T2(1,new T1(3,new T(function(){var _G2=_EP(_tk(_Ef,_F6));if(!_G2._){return E(_ss);}else{if(!E(_G2.b)._){return E(_G2.a);}else{return E(_su);}}})),new T(function(){return _EZ(_F4);}));case 102:return new T2(1,new T1(0,new T(function(){var _G3=_EP(_tk(_EJ,_F6));if(!_G3._){return E(_Eg);}else{if(!E(_G3.b)._){return E(_G3.a);}else{return E(_Eh);}}})),new T(function(){return _EZ(_F4);}));case 103:return new T2(1,new T1(1,new T(function(){var _G4=_EP(_tk(_EJ,_F6));if(!_G4._){return E(_Eg);}else{if(!E(_G4.b)._){return E(_G4.a);}else{return E(_Eh);}}})),new T(function(){return _EZ(_F4);}));case 106:return new T2(1,new T1(4,new T(function(){var _G5=_EP(_tk(_Ef,_F6));if(!_G5._){return E(_ss);}else{if(!E(_G5.b)._){return E(_G5.a);}else{return E(_su);}}})),new T(function(){return _EZ(_F4);}));case 109:return new T2(1,new T1(2,new T(function(){var _G6=_EP(_tk(_Ef,_F6));if(!_G6._){return E(_ss);}else{if(!E(_G6.b)._){return E(_G6.a);}else{return E(_su);}}})),new T(function(){return _EZ(_F4);}));case 117:return new T2(1,new T1(5,new T(function(){var _G7=_EP(_tk(_Ef,_F6));if(!_G7._){return E(_ss);}else{if(!E(_G7.b)._){return E(_G7.a);}else{return E(_su);}}})),new T(function(){return _EZ(_F4);}));case 119:return new T2(1,new T1(5,new T(function(){var _G8=_EP(_tk(_Ef,_F6));if(!_G8._){return E(_ss);}else{if(!E(_G8.b)._){return _3P(E(_G8.a)+6|0,7)+1|0;}else{return E(_su);}}})),new T(function(){return _EZ(_F4);}));case 121:return new T2(1,new T1(1,new T(function(){var _G9=_EP(_tk(_EJ,_F6));if(!_G9._){return E(_Eg);}else{if(!E(_G9.b)._){return E(_G9.a);}else{return E(_Eh);}}})),new T(function(){return _EZ(_F4);}));default:_F0=_F4;return __continue;}}})(_F0);if(_F1!=__continue){return _F1;}}},_Ga=_EZ(_EY),_Gb=new T(function(){return _EL(new T2(1,1,new T(function(){return _sd(_Ga);})),_sn);}),_Gc=new T(function(){return _EL(new T2(1,4,new T(function(){return _s6(_Ga);})),_sn);}),_Gd=new T(function(){return _3P(E(_Gc),7);}),_Ge=_EL(new T2(1,new T1(0,70),new T(function(){return _rT(_Ga);})),_sn),_Gf=_41(_4b(_sq,_s0(_Ga,new T(function(){if(!_8c(_Ge,new T1(0,69))){return E(new T1(0,20));}else{return E(new T1(0,19));}},1))),_Ge),_Gg=new T(function(){return B(_Gh(new T2(1,new T1(2,1),__Z)));}),_Gh=function(_Gi){while(1){var _Gj=E(_Gi);if(!_Gj._){return E(_Gg);}else{var _Gk=E(_Gj.a);switch(_Gk._){case 2:return C > 19 ? new F(function(){return _rg(_Gf,_Gk.a,_Gb);}) : (++C,_rg(_Gf,_Gk.a,_Gb));break;case 4:return _ru(_Gf,_Gk.a);case 6:var _Gl=_Gk.b;switch(E(_Gk.a)){case 0:return C > 19 ? new F(function(){return _rP(_Gf,_Gl,_Gc);}) : (++C,_rP(_Gf,_Gl,_Gc));break;case 1:return _rC(_Gf,_Gl,_Gd);default:return _rq(_Gf,_Gl,_Gc);}break;default:_Gi=_Gj.b;continue;}}}};return C > 19 ? new F(function(){return _Gh(_Ga);}) : (++C,_Gh(_Ga));},_Gm=function(_Gn,_Go){while(1){var _Gp=E(_Go);if(!_Gp._){return __Z;}else{var _Gq=_Gp.b,_Gr=E(_Gn);if(_Gr==1){return E(_Gq);}else{_Gn=_Gr-1|0;_Go=_Gq;continue;}}}},_Gs=new T2(1,48,__Z),_Gt=function(_Gu,_Gv){var _Gw=E(_Gu);if(_Gw==1){return E(_Gs);}else{var _Gx=E(_Gv);return (_Gx==1)?E(_Gs):new T2(1,48,new T(function(){return _Gt(_Gw-1|0,_Gx-1|0);}));}},_Gy=new T(function(){return err(new T(function(){return unCStr("Prelude.undefined");}));}),_Gz=function(_GA,_GB,_GC){var _GD=_fv(_4b(_GB,B(A1(_GA,_Gy))),_4b(_GC,_29));return C > 19 ? new F(function(){return _mb(_lK,_GD.a,_GD.b);}) : (++C,_mb(_lK,_GD.a,_GD.b));},_GE=function(_GF,_GG){return _fv(_4b(_GF,_7F(_GG)),_7u(_GG));},_GH=new T(function(){return _dq(true,new T2(1,1420103680,new T2(1,465,__Z)));}),_GI=function(_GJ,_GK){var _GL=_GE(_GK,_GH);return _41(_4b(_GJ,_dt),B(_Gz(_gh,_GL.a,_GL.b)));},_GM=function(_GN,_GO){var _GP=new T(function(){return E(E(E(_GN).c).a);}),_GQ=function(_GR,_GS,_GT,_GU){while(1){var _GV=(function(_GW,_GX,_GY,_GZ){var _H0=E(_GW);if(!_H0._){return new T3(0,_GX,_GY,_GZ);}else{var _H1=_H0.b,_H2=E(_H0.a),_H3=_H2.b;switch(E(_H2.a)){case 72:var _H4=_GY,_H5=_GZ;_GR=_H1;_GS=new T(function(){var _H6=_EP(_tk(_Ef,_H3));if(!_H6._){return E(_ss);}else{if(!E(_H6.b)._){return E(_H6.a);}else{return E(_su);}}});_GT=_H4;_GU=_H5;return __continue;case 73:var _H4=_GY,_H5=_GZ;_GR=_H1;_GS=new T(function(){var _H7=_EP(_tk(_Ef,_H3));if(!_H7._){return E(_ss);}else{if(!E(_H7.b)._){return E(_H7.a);}else{return E(_su);}}});_GT=_H4;_GU=_H5;return __continue;case 77:var _H8=_GX,_H5=_GZ;_GR=_H1;_GS=_H8;_GT=new T(function(){var _H9=_EP(_tk(_Ef,_H3));if(!_H9._){return E(_ss);}else{if(!E(_H9.b)._){return E(_H9.a);}else{return E(_su);}}});_GU=_H5;return __continue;case 80:if(!_qX(_hg(_bl,_H3),_GP)){var _H4=_GY,_H5=_GZ;_GR=_H1;_GS=new T(function(){var _Ha=E(_GX);if(_Ha>=12){return _Ha;}else{return _Ha+12|0;}});_GT=_H4;_GU=_H5;return __continue;}else{var _H4=_GY,_H5=_GZ;_GR=_H1;_GS=new T(function(){return _3P(E(_GX),12);});_GT=_H4;_GU=_H5;return __continue;}break;case 81:var _Hb=E(_H3);if(!_Hb._){var _H8=_GX,_H4=_GY,_H5=_GZ;_GR=_H1;_GS=_H8;_GT=_H4;_GU=_H5;return __continue;}else{var _Hc=new T(function(){var _Hd=_fz(_GZ,_29,_dt,_29),_He=new T(function(){var _Hf=_Gm(1,_Hb),_Hg=function(_Hh,_Hi){var _Hj=E(_Hh);if(!_Hj._){var _Hk=12-_6o(_Hf,0)|0;if(0>=_Hk){return __Z;}else{return _Gt(_Hk,_Hi);}}else{var _Hl=_Hj.a,_Hm=E(_Hi);return (_Hm==1)?new T2(1,_Hl,__Z):new T2(1,_Hl,new T(function(){return _Hg(_Hj.b,_Hm-1|0);}));}};return _Hg(_Hf,12);}),_Hn=_EP(_tk(_EJ,_He));if(!_Hn._){return E(_Eg);}else{if(!E(_Hn.b)._){return _GI(_fS(_lK,_Hd.a,_Hd.b).a,_Hn.a);}else{return E(_Eh);}}}),_H8=_GX,_H4=_GY;_GR=_H1;_GS=_H8;_GT=_H4;_GU=_Hc;return __continue;}break;case 83:var _H8=_GX,_H4=_GY;_GR=_H1;_GS=_H8;_GT=_H4;_GU=new T(function(){var _Ho=_EP(_tk(_EJ,_H3));if(!_Ho._){return E(_Eg);}else{if(!E(_Ho.b)._){return _4b(_Ho.a,_dt);}else{return E(_Eh);}}});return __continue;case 107:var _H4=_GY,_H5=_GZ;_GR=_H1;_GS=new T(function(){var _Hp=_EP(_tk(_Ef,_H3));if(!_Hp._){return E(_ss);}else{if(!E(_Hp.b)._){return E(_Hp.a);}else{return E(_su);}}});_GT=_H4;_GU=_H5;return __continue;case 108:var _H4=_GY,_H5=_GZ;_GR=_H1;_GS=new T(function(){var _Hq=_EP(_tk(_Ef,_H3));if(!_Hq._){return E(_ss);}else{if(!E(_Hq.b)._){return E(_Hq.a);}else{return E(_su);}}});_GT=_H4;_GU=_H5;return __continue;case 112:if(!_qX(_hg(_bl,_H3),_GP)){var _H4=_GY,_H5=_GZ;_GR=_H1;_GS=new T(function(){var _Hr=E(_GX);if(_Hr>=12){return _Hr;}else{return _Hr+12|0;}});_GT=_H4;_GU=_H5;return __continue;}else{var _H4=_GY,_H5=_GZ;_GR=_H1;_GS=new T(function(){return _3P(E(_GX),12);});_GT=_H4;_GU=_H5;return __continue;}break;case 113:var _H8=_GX,_H4=_GY;_GR=_H1;_GS=_H8;_GT=_H4;_GU=new T(function(){var _Hs=_fz(_GZ,_29,_dt,_29),_Ht=_EP(_tk(_EJ,_H3));if(!_Ht._){return E(_Eg);}else{if(!E(_Ht.b)._){return _GI(_fS(_lK,_Hs.a,_Hs.b).a,_Ht.a);}else{return E(_Eh);}}});return __continue;default:var _H8=_GX,_H4=_GY,_H5=_GZ;_GR=_H1;_GS=_H8;_GT=_H4;_GU=_H5;return __continue;}}})(_GR,_GS,_GT,_GU);if(_GV!=__continue){return _GV;}}};return _GQ(_GO,0,0,new T1(0,0));},_Hu=function(_Hv,_Hw){var _Hx=_GM(_Hv,_Hw);return new T3(0,_Hx.a,_Hx.b,_Hx.c);},_Hy=function(_Hz,_HA,_HB,_HC,_HD){var _HE=function(_HF){var _HG=_EP(_tk(_Ef,new T2(1,_HA,new T2(1,_HB,__Z))));if(!_HG._){return E(_ss);}else{if(!E(_HG.b)._){var _HH=_EP(_tk(_Ef,new T2(1,_HC,new T2(1,_HD,__Z))));return (_HH._==0)?E(_ss):(E(_HH.b)._==0)?imul(_HF,(imul(60,E(_HG.a))|0)+E(_HH.a)|0)|0:E(_su);}else{return E(_su);}}};if(E(_Hz)==45){return _HE(-1);}else{return _HE(1);}},_HI=function(_HJ,_HK){var _HL=new T(function(){return E(E(_HJ).h);}),_HM=function(_HN,_HO,_HP,_HQ){while(1){var _HR=(function(_HS,_HT,_HU,_HV){var _HW=E(_HS);if(!_HW._){return new T3(0,_HT,_HU,_HV);}else{var _HX=_HW.b,_HY=E(_HW.a),_HZ=_HY.b,_I0=new T(function(){var _I1=E(_HZ);if(!_I1._){return 0;}else{var _I2=_I1.a,_I3=E(_I1.b);if(!_I3._){return 0;}else{var _I4=_I3.a,_I5=E(_I3.b);if(!_I5._){return 0;}else{var _I6=_I5.a,_I7=E(_I5.b);if(!_I7._){return 0;}else{var _I8=_I7.b,_I9=E(_I7.a),_Ia=function(_Ib){var _Ic=E(_I8);if(!_Ic._){return 0;}else{if(!E(_Ic.b)._){return _Hy(E(_I2),_I4,_I6,_I9,_Ic.a);}else{return 0;}}};if(_I9==58){var _Id=E(_I8);if(!_Id._){return _Ia(_);}else{var _Ie=E(_Id.b);if(!_Ie._){return _Ia(_);}else{if(!E(_Ie.b)._){return _Hy(E(_I2),_I4,_I6,_Id.a,_Ie.a);}else{return _Ia(_);}}}}else{return _Ia(_);}}}}}});switch(E(_HY.a)){case 90:var _If=E(_HZ);if(!_If._){var _Ig=_HT,_Ih=_HU,_Ii=_HV;_HN=_HX;_HO=_Ig;_HP=_Ih;_HQ=_Ii;return __continue;}else{var _Ij=u_iswalpha(E(_If.a));if(!E(_Ij)){var _Ih=_HU,_Ii=_HV;_HN=_HX;_HO=_I0;_HP=_Ih;_HQ=_Ii;return __continue;}else{var _Ik=new T(function(){return _hg(_bl,_If);}),_Il=function(_Im){while(1){var _In=E(_Im);if(!_In._){return __Z;}else{var _Io=E(_In.a);if(!_qX(_Ik,_Io.c)){_Im=_In.b;continue;}else{return new T1(1,_Io);}}}},_Ip=_Il(_HL);if(!_Ip._){var _Iq=E(_Ik);if(!_Iq._){var _Ig=_HT,_Ih=_HU;_HN=_HX;_HO=_Ig;_HP=_Ih;_HQ=__Z;return __continue;}else{if(!E(_Iq.b)._){var _Ir=E(_Iq.a);if(_Ir>=65){if(_Ir>73){if(_Ir==74){var _Ig=_HT,_Ih=_HU;_HN=_HX;_HO=_Ig;_HP=_Ih;_HQ=_Iq;return __continue;}else{if(_Ir>77){if(_Ir>89){if(_Ir==90){_HN=_HX;_HO=0;_HP=false;_HQ=_Iq;return __continue;}else{var _Ig=_HT,_Ih=_HU;_HN=_HX;_HO=_Ig;_HP=_Ih;_HQ=_Iq;return __continue;}}else{_HN=_HX;_HO=imul((78-_Ir|0)-1|0,60)|0;_HP=false;_HQ=_Iq;return __continue;}}else{_HN=_HX;_HO=imul(10+(_Ir-75|0)|0,60)|0;_HP=false;_HQ=_Iq;return __continue;}}}else{_HN=_HX;_HO=imul(1+(_Ir-65|0)|0,60)|0;_HP=false;_HQ=_Iq;return __continue;}}else{var _Ig=_HT,_Ih=_HU;_HN=_HX;_HO=_Ig;_HP=_Ih;_HQ=_Iq;return __continue;}}else{var _Ig=_HT,_Ih=_HU;_HN=_HX;_HO=_Ig;_HP=_Ih;_HQ=_Iq;return __continue;}}}else{var _Is=E(_Ip.a);_HN=_HX;_HO=_Is.a;_HP=_Is.b;_HQ=_Is.c;return __continue;}}}break;case 122:var _Ih=_HU,_Ii=_HV;_HN=_HX;_HO=_I0;_HP=_Ih;_HQ=_Ii;return __continue;default:var _Ig=_HT,_Ih=_HU,_Ii=_HV;_HN=_HX;_HO=_Ig;_HP=_Ih;_HQ=_Ii;return __continue;}}})(_HN,_HO,_HP,_HQ);if(_HR!=__continue){return _HR;}}};return _HM(_HK,0,false,__Z);},_It=function(_Iu,_Iv){var _Iw=_HI(_Iu,_Iv);return new T3(0,_Iw.a,_Iw.b,_Iw.c);},_Ix=function(_Iy){var _Iz=E(_Iy);return C > 19 ? new F(function(){return _Gz(_gh,_Iz.a,_Iz.b);}) : (++C,_Gz(_gh,_Iz.a,_Iz.b));},_IA=function(_IB,_IC,_ID){if(!_3t(_ID,_go)){return _2B(_4b(_IC,B(A1(_IB,_IC))),_ID);}else{return E(_39);}},_IE=function(_IF,_IG){return _IA(_gh,_IF,_IG);},_IH=function(_II,_IJ){if(!_3t(_IJ,_go)){var _IK=B(A1(_II,_IJ));return _2B(_4b(_IK,_IK),_IJ);}else{return E(_39);}},_IL=function(_IM){return _IH(_gh,_IM);},_IN=function(_IO){return E(E(_IO).a);},_IP=function(_IQ){return E(E(_IQ).i);},_IR=function(_IS,_IT,_IU,_IV){var _IW=new T(function(){var _IX=_fz(_IV,_29,B(A1(_IT,_IV)),_29);return E(_fS(_IU,_IX.a,_IX.b).a);}),_IY=new T(function(){var _IZ=_IN(_IS),_J0=new T(function(){return B(A2(_6C,_IZ,new T(function(){return B(A2(_IP,_IU,_IW));})));});return B(A3(_m9,_IZ,_IV,_J0));});return new T2(0,_IW,_IY);},_J1=function(_J2){var _J3=new T(function(){var _J4=_fz(_J2,_29,_dt,_29),_J5=_fz(_mK,_29,_dt,_29),_J6=_fz(_J4.a,_J4.b,_J5.a,_J5.b);return B(_mb(_lK,_J6.a,_J6.b));});return new T2(0,new T(function(){return _41(_mL,_J3);}),new T(function(){return _3G(_J2,_mq(_gh,_4b(_J3,_dt),_mK));}));},_J7=function(_J8,_J9,_Ja){while(1){var _Jb=(function(_Jc,_Jd,_Je){var _Jf=E(_Jc);if(!_Jf._){return new T2(0,_Jd,_Je);}else{var _Jg=_Jf.b,_Jh=E(_Jd),_Ji=E(_Jf.a);if(E(_Ji.a)==115){var _Jj=new T(function(){var _Jk=new T(function(){var _Jl=_EP(_tk(_EJ,_Ji.b));if(!_Jl._){return E(_Eg);}else{if(!E(_Jl.b)._){var _Jm=_fz(_IR(new T4(0,_pD,_IE,_IL,_Ix),_gh,_lK,new T(function(){return E(E(_Jh.b).c);})).b,_29,_dt,_29);return _41(_4b(_Jl.a,_dt),B(_Gz(_gh,_Jm.a,_Jm.b)));}else{return E(_Eh);}}}),_Jn=_J1(_Jk),_Jo=_qa(_Je,_Jn.a,_Jn.b);return new T2(0,_Jo.a,_Jo.b);}),_Jp=_Je;_J8=_Jg;_J9=_Jj;_Ja=_Jp;return __continue;}else{var _Jp=_Je;_J8=_Jg;_J9=_Jh;_Ja=_Jp;return __continue;}}})(_J8,_J9,_Ja);if(_Jb!=__continue){return _Jb;}}},_Jq=function(_Jr,_Js){return _J7(_Js,new T2(0,new T(function(){return B(_EW(_Jr,_Js));}),new T(function(){return _Hu(_Jr,_Js);})),new T(function(){return _It(_Jr,_Js);}));},_Jt=function(_Ju,_Jv){var _Jw=E(_Jv),_Jx=_mD(_Ju,_Jw.a,_Jw.b);return new T2(0,_Jx.a,_Jx.b);},_Jy=function(_Jz,_JA){var _JB=_Jq(_Jz,_JA);return _Jt(_JB.b,_JB.a);},_JC=function(_JD,_JE,_JF,_JG){return _fv(_3G(_4b(_JD,_JG),_4b(_JF,_JE)),_4b(_JE,_JG));},_JH=function(_JI){return E(E(_JI).a);},_JJ=function(_JK){return E(E(_JK).a);},_JL=function(_JM){return E(E(_JM).b);},_JN=new T1(0,2),_JO=function(_JP){return E(E(_JP).d);},_JQ=function(_JR,_JS){var _JT=_fF(_JR),_JU=new T(function(){return _fH(_JT);}),_JV=new T(function(){return B(A3(_JO,_JR,_JS,new T(function(){return B(A2(_6C,_JU,_JN));})));});return C > 19 ? new F(function(){return A3(_xb,_JJ(_JL(_JT)),_JV,new T(function(){return B(A2(_6C,_JU,_f5));}));}) : (++C,A3(_xb,_JJ(_JL(_JT)),_JV,new T(function(){return B(A2(_6C,_JU,_f5));})));},_JW=new T(function(){return _3t(_29,_29);}),_JX=new T(function(){return err(new T(function(){return unCStr("round default defn: Bad value");}));}),_JY=function(_JZ,_K0,_K1){var _K2=_fS(_JZ,_K0,_K1),_K3=_K2.a,_K4=E(_K2.b),_K5=_K4.a,_K6=_K4.b,_K7=_7F(_JC(_7u(_K5),_K6,_29,_JN).a),_K8=function(_K9){var _Ka=new T(function(){var _Kb=_fH(_fF(_JZ));if(!_8s(_4b(_K5,_29),_4b(_f5,_K6))){return B(A3(_JH,_Kb,_K3,new T(function(){return B(A2(_6C,_Kb,_29));})));}else{return B(A3(_m9,_Kb,_K3,new T(function(){return B(A2(_6C,_Kb,_29));})));}});if(!_3t(_K7,_f5)){return (!_3t(_K7,_29))?E(_JX):(!E(_JW))?E(_JX):E(_Ka);}else{if(!E(_JW)){var _Kc=_3t(_K7,_29);return E(_JX);}else{return (!B(_JQ(_JZ,_K3)))?E(_Ka):E(_K3);}}};if(!_3t(_K7,new T1(0,-1))){return _K8(_);}else{if(!E(_JW)){return _K8(_);}else{return E(_K3);}}},_Kd=new T1(0,2017),_Ke=new T(function(){return _4K(_Kd,_r2(new T(function(){return _4I(_Kd);}),9,23));}),_Kf=new T(function(){return _dq(true,new T2(1,1813786624,new T2(1,36457087,__Z)));}),_Kg=new T(function(){return _mM(_Ke,_Kf);}),_Kh=function(_Ki,_Kj){var _Kk=_fz(_3G(_mM(_Ki,_Kj),_Kg),_29,_dt,_29);return _JY(_lK,_Kk.a,_Kk.b);},_Kl=new T1(0,10),_Km=new T1(0,0),_Kn=new T1(0,20),_Ko=function(_Kp,_Kq,_Kr){var _Ks=_4b(_4b(_Kr,_Kn),_Kl);if(!_3t(_Ks,_Km)){return _2B(_Kh(_Kp,_Kq),_Ks);}else{return E(_39);}},_Kt=new T(function(){return _3t(_Kn,_Km);}),_Ku=function(_Kv,_Kw,_Kx){if(!E(_Kt)){var _Ky=_4b(_4b(_Kx,_Kn),_Kl);if(!_3t(_Ky,_Km)){return _2B(_f6(_Kh(_Kv,_Kw),_Ky),_Kn);}else{return E(_39);}}else{return E(_39);}},_Kz=function(_KA,_KB){var _KC=E(_KA);return _Ko(_KC.a,_KC.b,_KB);},_KD=function(_KE,_KF){var _KG=E(_KE);return _Ku(_KG.a,_KG.b,_KF);},_KH=new T(function(){return unCStr("May");}),_KI={_:0,a:new T2(1,new T2(0,new T(function(){return unCStr("Sunday");}),new T(function(){return unCStr("Sun");})),new T2(1,new T2(0,new T(function(){return unCStr("Monday");}),new T(function(){return unCStr("Mon");})),new T2(1,new T2(0,new T(function(){return unCStr("Tuesday");}),new T(function(){return unCStr("Tue");})),new T2(1,new T2(0,new T(function(){return unCStr("Wednesday");}),new T(function(){return unCStr("Wed");})),new T2(1,new T2(0,new T(function(){return unCStr("Thursday");}),new T(function(){return unCStr("Thu");})),new T2(1,new T2(0,new T(function(){return unCStr("Friday");}),new T(function(){return unCStr("Fri");})),new T2(1,new T2(0,new T(function(){return unCStr("Saturday");}),new T(function(){return unCStr("Sat");})),__Z))))))),b:new T2(1,new T2(0,new T(function(){return unCStr("January");}),new T(function(){return unCStr("Jan");})),new T2(1,new T2(0,new T(function(){return unCStr("February");}),new T(function(){return unCStr("Feb");})),new T2(1,new T2(0,new T(function(){return unCStr("March");}),new T(function(){return unCStr("Mar");})),new T2(1,new T2(0,new T(function(){return unCStr("April");}),new T(function(){return unCStr("Apr");})),new T2(1,new T2(0,_KH,_KH),new T2(1,new T2(0,new T(function(){return unCStr("June");}),new T(function(){return unCStr("Jun");})),new T2(1,new T2(0,new T(function(){return unCStr("July");}),new T(function(){return unCStr("Jul");})),new T2(1,new T2(0,new T(function(){return unCStr("August");}),new T(function(){return unCStr("Aug");})),new T2(1,new T2(0,new T(function(){return unCStr("September");}),new T(function(){return unCStr("Sep");})),new T2(1,new T2(0,new T(function(){return unCStr("October");}),new T(function(){return unCStr("Oct");})),new T2(1,new T2(0,new T(function(){return unCStr("November");}),new T(function(){return unCStr("Nov");})),new T2(1,new T2(0,new T(function(){return unCStr("December");}),new T(function(){return unCStr("Dec");})),__Z)))))))))))),c:new T2(0,new T(function(){return unCStr("AM");}),new T(function(){return unCStr("PM");})),d:new T(function(){return unCStr("%a %b %e %H:%M:%S %Z %Y");}),e:new T(function(){return unCStr("%m/%d/%y");}),f:new T(function(){return unCStr("%H:%M:%S");}),g:new T(function(){return unCStr("%I:%M:%S %p");}),h:new T2(1,new T3(0,0,false,new T(function(){return unCStr("UT");})),new T2(1,new T3(0,0,false,new T(function(){return unCStr("GMT");})),new T2(1,new T3(0,-300,false,new T(function(){return unCStr("EST");})),new T2(1,new T3(0,-240,true,new T(function(){return unCStr("EDT");})),new T2(1,new T3(0,-360,false,new T(function(){return unCStr("CST");})),new T2(1,new T3(0,-300,true,new T(function(){return unCStr("CDT");})),new T2(1,new T3(0,-420,false,new T(function(){return unCStr("MST");})),new T2(1,new T3(0,-360,true,new T(function(){return unCStr("MDT");})),new T2(1,new T3(0,-480,false,new T(function(){return unCStr("PST");})),new T2(1,new T3(0,-420,true,new T(function(){return unCStr("PDT");})),__Z))))))))))},_KJ=function(_KK,_KL,_KM,_KN){while(1){var _KO=(function(_KP,_KQ,_KR,_KS){var _KT=E(_KR);if(!_KT._){return __Z;}else{var _KU=_KT.b,_KV=E(_KT.a);if(_KV==37){var _KW=E(_KU);if(!_KW._){return new T2(1,_KV,new T(function(){return _KJ(_KP,_KQ,__Z,_KS);}));}else{var _KX=_KW.b,_KY=E(_KW.a),_KZ=function(_L0){switch(_KY){case 37:return _x(_bc,new T(function(){return _KJ(_KP,_KQ,_KX,_KS);},1));case 110:return _x(_bb,new T(function(){return _KJ(_KP,_KQ,_KX,_KS);},1));case 116:return _x(_ba,new T(function(){return _KJ(_KP,_KQ,_KX,_KS);},1));default:var _L1=B(A1(_KP,_KY));if(!_L1._){return _KJ(_KP,_KQ,_KX,_KS);}else{return _x(B(A3(_L1.a,_KQ,__Z,_KS)),new T(function(){return _KJ(_KP,_KQ,_KX,_KS);},1));}}};switch(_KY){case 35:var _L2=E(_KX);if(!_L2._){return _KZ(_);}else{var _L3=_L2.b,_L4=E(_L2.a);switch(_L4){case 37:var _L5=new T(function(){return _KJ(_KP,_KQ,_L3,_KS);}),_L6=function(_L7){var _L8=E(_L7);return (_L8._==0)?E(_L5):new T2(1,new T(function(){return _bi(_L8.a);}),new T(function(){return _L6(_L8.b);}));};return _L6(_bc);case 110:var _L9=new T(function(){return _KJ(_KP,_KQ,_L3,_KS);}),_La=function(_Lb){var _Lc=E(_Lb);return (_Lc._==0)?E(_L9):new T2(1,new T(function(){return _bi(_Lc.a);}),new T(function(){return _La(_Lc.b);}));};return _La(_bb);case 116:var _Ld=new T(function(){return _KJ(_KP,_KQ,_L3,_KS);}),_Le=function(_Lf){var _Lg=E(_Lf);return (_Lg._==0)?E(_Ld):new T2(1,new T(function(){return _bi(_Lg.a);}),new T(function(){return _Le(_Lg.b);}));};return _Le(_ba);default:var _Lh=B(A1(_KP,_L4));if(!_Lh._){var _Li=_KP,_Lj=_KQ,_Lk=_KS;_KK=_Li;_KL=_Lj;_KM=_L3;_KN=_Lk;return __continue;}else{var _Ll=new T(function(){return _KJ(_KP,_KQ,_L3,_KS);}),_Lm=function(_Ln){var _Lo=E(_Ln);return (_Lo._==0)?E(_Ll):new T2(1,new T(function(){return _bi(_Lo.a);}),new T(function(){return _Lm(_Lo.b);}));};return _Lm(B(A3(_Lh.a,_KQ,__Z,_KS)));}}}break;case 45:var _Lp=E(_KX);if(!_Lp._){return _KZ(_);}else{var _Lq=_Lp.b,_Lr=E(_Lp.a);switch(_Lr){case 37:return _x(_bc,new T(function(){return _KJ(_KP,_KQ,_Lq,_KS);},1));case 110:return _x(_bb,new T(function(){return _KJ(_KP,_KQ,_Lq,_KS);},1));case 116:return _x(_ba,new T(function(){return _KJ(_KP,_KQ,_Lq,_KS);},1));default:var _Ls=B(A1(_KP,_Lr));if(!_Ls._){var _Li=_KP,_Lj=_KQ,_Lk=_KS;_KK=_Li;_KL=_Lj;_KM=_Lq;_KN=_Lk;return __continue;}else{return _x(B(A3(_Ls.a,_KQ,_bf,_KS)),new T(function(){return _KJ(_KP,_KQ,_Lq,_KS);},1));}}}break;case 48:var _Lt=E(_KX);if(!_Lt._){return _KZ(_);}else{var _Lu=_Lt.b,_Lv=E(_Lt.a);switch(_Lv){case 37:return _x(_bc,new T(function(){return _KJ(_KP,_KQ,_Lu,_KS);},1));case 110:return _x(_bb,new T(function(){return _KJ(_KP,_KQ,_Lu,_KS);},1));case 116:return _x(_ba,new T(function(){return _KJ(_KP,_KQ,_Lu,_KS);},1));default:var _Lw=B(A1(_KP,_Lv));if(!_Lw._){var _Li=_KP,_Lj=_KQ,_Lk=_KS;_KK=_Li;_KL=_Lj;_KM=_Lu;_KN=_Lk;return __continue;}else{return _x(B(A3(_Lw.a,_KQ,_be,_KS)),new T(function(){return _KJ(_KP,_KQ,_Lu,_KS);},1));}}}break;case 94:var _Lx=E(_KX);if(!_Lx._){return _KZ(_);}else{var _Ly=_Lx.b,_Lz=E(_Lx.a);switch(_Lz){case 37:var _LA=new T(function(){return _KJ(_KP,_KQ,_Ly,_KS);}),_LB=function(_LC){var _LD=E(_LC);return (_LD._==0)?E(_LA):new T2(1,new T(function(){return _bl(_LD.a);}),new T(function(){return _LB(_LD.b);}));};return _LB(_bc);case 110:var _LE=new T(function(){return _KJ(_KP,_KQ,_Ly,_KS);}),_LF=function(_LG){var _LH=E(_LG);return (_LH._==0)?E(_LE):new T2(1,new T(function(){return _bl(_LH.a);}),new T(function(){return _LF(_LH.b);}));};return _LF(_bb);case 116:var _LI=new T(function(){return _KJ(_KP,_KQ,_Ly,_KS);}),_LJ=function(_LK){var _LL=E(_LK);return (_LL._==0)?E(_LI):new T2(1,new T(function(){return _bl(_LL.a);}),new T(function(){return _LJ(_LL.b);}));};return _LJ(_ba);default:var _LM=B(A1(_KP,_Lz));if(!_LM._){var _Li=_KP,_Lj=_KQ,_Lk=_KS;_KK=_Li;_KL=_Lj;_KM=_Ly;_KN=_Lk;return __continue;}else{var _LN=new T(function(){return _KJ(_KP,_KQ,_Ly,_KS);}),_LO=function(_LP){var _LQ=E(_LP);return (_LQ._==0)?E(_LN):new T2(1,new T(function(){return _bl(_LQ.a);}),new T(function(){return _LO(_LQ.b);}));};return _LO(B(A3(_LM.a,_KQ,__Z,_KS)));}}}break;case 95:var _LR=E(_KX);if(!_LR._){return _KZ(_);}else{var _LS=_LR.b,_LT=E(_LR.a);switch(_LT){case 37:return _x(_bc,new T(function(){return _KJ(_KP,_KQ,_LS,_KS);},1));case 110:return _x(_bb,new T(function(){return _KJ(_KP,_KQ,_LS,_KS);},1));case 116:return _x(_ba,new T(function(){return _KJ(_KP,_KQ,_LS,_KS);},1));default:var _LU=B(A1(_KP,_LT));if(!_LU._){var _Li=_KP,_Lj=_KQ,_Lk=_KS;_KK=_Li;_KL=_Lj;_KM=_LS;_KN=_Lk;return __continue;}else{return _x(B(A3(_LU.a,_KQ,_bd,_KS)),new T(function(){return _KJ(_KP,_KQ,_LS,_KS);},1));}}}break;default:return _KZ(_);}}}else{return new T2(1,_KV,new T(function(){return _KJ(_KP,_KQ,_KU,_KS);}));}}})(_KK,_KL,_KM,_KN);if(_KO!=__continue){return _KO;}}},_LV=(function(e,p){var x = e[p];return typeof x === 'undefined' ? '' : x.toString();}),_LW=(function(e,p,v){e[p] = v;}),_LX=new T(function(){return B((function(_LY){return C > 19 ? new F(function(){return _th("calculator.hs:(19,1)-(103,11)|function calculator");}) : (++C,_th("calculator.hs:(19,1)-(103,11)|function calculator"));})(_));}),_LZ=new T(function(){return unCStr("value");}),_M0=new T(function(){return unAppCStr("%Y-%m-%d",new T2(1,84,new T(function(){return unCStr("%H:%M:%S");})));}),_M1=function(_M2){return E(E(_M2).a);},_M3=function(_M4){return E(E(_M4).a);},_M5=function(_M6){return E(E(_M6).b);},_M7=function(_M8){return E(E(_M8).a);},_M9=function(_Ma){return E(E(_Ma).b);},_Mb=function(_Mc){return E(E(_Mc).a);},_Md=function(_Me){var _Mf=B(A1(_Me,_));return E(_Mf);},_Mg=new T(function(){return _Md(function(_){return nMV(__Z);});}),_Mh=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_Mi=new T(function(){return _Md(function(_){return __jsNull();});}),_Mj=function(_Mk){return E(E(_Mk).b);},_Ml=function(_Mm){return E(E(_Mm).b);},_Mn=function(_Mo){return E(E(_Mo).d);},_Mp=function(_Mq,_Mr,_Ms,_Mt,_Mu,_Mv){var _Mw=_M1(_Mq),_Mx=_M3(_Mw),_My=new T(function(){return _Mj(_Mw);}),_Mz=new T(function(){return _Mn(_Mx);}),_MA=new T(function(){return B(A2(_M7,_Mr,_Mt));}),_MB=new T(function(){return B(A2(_Mb,_Ms,_Mu));}),_MC=function(_MD){return C > 19 ? new F(function(){return A1(_Mz,new T3(0,_MB,_MA,_MD));}) : (++C,A1(_Mz,new T3(0,_MB,_MA,_MD)));},_ME=function(_MF){var _MG=new T(function(){var _MH=new T(function(){var _MI=__createJSFunc(2,function(_MJ,_){var _MK=B(A2(E(_MF),_MJ,_));return _Mi;}),_ML=_MI;return function(_){return _Mh(E(_MA),E(_MB),_ML);};});return B(A1(_My,_MH));});return C > 19 ? new F(function(){return A3(_M5,_Mx,_MG,_MC);}) : (++C,A3(_M5,_Mx,_MG,_MC));},_MM=new T(function(){var _MN=new T(function(){return _Mj(_Mw);}),_MO=function(_MP){var _MQ=new T(function(){return B(A1(_MN,function(_){var _=wMV(E(_Mg),new T1(1,_MP));return C > 19 ? new F(function(){return A(_M9,[_Ms,_Mu,_MP,_]);}) : (++C,A(_M9,[_Ms,_Mu,_MP,_]));}));});return C > 19 ? new F(function(){return A3(_M5,_Mx,_MQ,_Mv);}) : (++C,A3(_M5,_Mx,_MQ,_Mv));};return B(A2(_Ml,_Mq,_MO));});return C > 19 ? new F(function(){return A3(_M5,_Mx,_MM,_ME);}) : (++C,A3(_M5,_Mx,_MM,_ME));},_MR=function(_MS){return E(E(_MS).e);},_MT=function(_MU){while(1){var _MV=E(_MU);if(!_MV._){return true;}else{var _MW=_MV.b,_MX=E(_MV.a),_MY=_MX>>>0;if(_MY>887){var _MZ=u_iswspace(_MX);if(!E(_MZ)){return false;}else{_MU=_MW;continue;}}else{if(_MY==32){_MU=_MW;continue;}else{if(_MY-9>>>0>4){if(_MY==160){_MU=_MW;continue;}else{return false;}}else{_MU=_MW;continue;}}}}}},_N0=function(_N1){while(1){var _N2=(function(_N3){var _N4=E(_N3);if(!_N4._){return __Z;}else{var _N5=_N4.b,_N6=E(_N4.a);if(!_MT(_N6.b)){_N1=_N5;return __continue;}else{return new T2(1,_N6.a,new T(function(){return _N0(_N5);}));}}})(_N1);if(_N2!=__continue){return _N2;}}},_N7=function(_N8){while(1){var _N9=(function(_Na){var _Nb=E(_Na);if(!_Nb._){return __Z;}else{var _Nc=_Nb.b,_Nd=E(_Nb.a);if(!E(_Nd.b)._){return new T2(1,_Nd.a,new T(function(){return _N7(_Nc);}));}else{_N8=_Nc;return __continue;}}})(_N8);if(_N9!=__continue){return _N9;}}},_Ne=new T(function(){return unCStr("%Y-%m-%d");}),_Nf=new T0(1),_Ng=function(_Nh){return E(E(_Nh).e);},_Ni=function(_Nj){return E(E(_Nj).d);},_Nk=new T(function(){return unCStr("%b");}),_Nl=new T(function(){return unCStr("%H:%M:%S");}),_Nm=new T(function(){return unCStr("%H:%M");}),_Nn=new T(function(){return unCStr("%m/%d/%y");}),_No=new T2(1,new T1(2,37),__Z),_Np=function(_Nq,_Nr,_Ns){if(0>=_Nq){return C > 19 ? new F(function(){return A1(_Ns,__Z);}) : (++C,A1(_Ns,__Z));}else{var _Nt=function(_Nu,_Nv){var _Nw=E(_Nu);if(_Nw==1){return C > 19 ? new F(function(){return A1(_Nr,function(_Nx){return C > 19 ? new F(function(){return A1(_Nv,new T2(1,_Nx,__Z));}) : (++C,A1(_Nv,new T2(1,_Nx,__Z)));});}) : (++C,A1(_Nr,function(_Nx){return C > 19 ? new F(function(){return A1(_Nv,new T2(1,_Nx,__Z));}) : (++C,A1(_Nv,new T2(1,_Nx,__Z)));}));}else{var _Ny=function(_Nz){return C > 19 ? new F(function(){return _Nt(_Nw-1|0,function(_NA){return C > 19 ? new F(function(){return A1(_Nv,new T2(1,_Nz,_NA));}) : (++C,A1(_Nv,new T2(1,_Nz,_NA)));});}) : (++C,_Nt(_Nw-1|0,function(_NA){return C > 19 ? new F(function(){return A1(_Nv,new T2(1,_Nz,_NA));}) : (++C,A1(_Nv,new T2(1,_Nz,_NA)));}));};return C > 19 ? new F(function(){return A1(_Nr,_Ny);}) : (++C,A1(_Nr,_Ny));}};return C > 19 ? new F(function(){return _Nt(_Nq,_Ns);}) : (++C,_Nt(_Nq,_Ns));}},_NB=function(_NC,_ND){var _NE=function(_NF){return C > 19 ? new F(function(){return A1(_NF,_NC);}) : (++C,A1(_NF,_NC));},_NG=function(_NH,_NI){var _NJ=E(_NH);if(!_NJ._){return _NE;}else{var _NK=E(_NI);if(!_NK._){return _xu;}else{var _NL=u_towupper(E(_NJ.a));if(_NL>>>0>1114111){return _bg(_NL);}else{var _NM=u_towupper(E(_NK.a));if(_NM>>>0>1114111){return _bg(_NM);}else{if(_NL!=_NM){return _xu;}else{var _NN=new T(function(){return _NG(_NJ.b,_NK.b);}),_NO=function(_NP){var _NQ=new T(function(){return B(A1(_NN,_NP));});return new T1(0,function(_NR){return E(_NQ);});};return _NO;}}}}}};return function(_NS){return C > 19 ? new F(function(){return A3(_NG,_NC,_NS,_ND);}) : (++C,A3(_NG,_NC,_NS,_ND));};},_NT=function(_NU){return C > 19 ? new F(function(){return A1(_NU,__Z);}) : (++C,A1(_NU,__Z));},_NV=function(_NW){return new T1(0,function(_NX){var _NY=E(_NX);if((_NY-48|0)>>>0>9){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_NW,_NY);}) : (++C,A1(_NW,_NY));}});},_NZ=function(_O0){return (E(_O0)-48|0)>>>0<=9;},_O1=new T(function(){var _O2=u_towupper(46);if(_O2>>>0>1114111){return _bg(_O2);}else{return _O2;}}),_O3=function(_O4){return function(_O5){var _O6=E(_O5),_O7=u_towupper(_O6);if(_O7>>>0>1114111){return _bg(_O7);}else{return (E(_O1)!=_O7)?new T0(2):new T1(1,_uX(_NZ,function(_O8){return C > 19 ? new F(function(){return A1(_O4,new T2(1,_O6,_O8));}) : (++C,A1(_O4,new T2(1,_O6,_O8)));}));}};},_O9=function(_Oa){return new T1(0,_O3(_Oa));},_Ob=function(_Oc){return C > 19 ? new F(function(){return A1(_Oc,__Z);}) : (++C,A1(_Oc,__Z));},_Od=function(_Oe){return new T1(1,_ux(_O9,_Ob,_Oe));},_Of=function(_Og,_Oh){var _Oi=new T(function(){var _Oj=u_towupper(E(_Og));if(_Oj>>>0>1114111){return _bg(_Oj);}else{return _Oj;}});return function(_Ok){var _Ol=E(_Ok),_Om=u_towupper(_Ol);if(_Om>>>0>1114111){return _bg(_Om);}else{if(E(_Oi)!=_Om){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_Oh,_Ol);}) : (++C,A1(_Oh,_Ol));}}};},_On=new T(function(){return _xw(new T2(1,function(_Oo){return new T1(0,_Of(43,_Oo));},new T2(1,function(_Op){return new T1(0,_Of(45,_Op));},__Z)));}),_Oq=new T(function(){var _Or=u_towupper(58);if(_Or>>>0>1114111){return _bg(_Or);}else{return _Or;}}),_Os=function(_Ot,_Ou){var _Ov=function(_Ow){var _Ox=new T(function(){var _Oy=function(_Oz){return C > 19 ? new F(function(){return A1(_Ou,new T2(1,_Ot,new T(function(){return _x(_Ow,_Oz);})));}) : (++C,A1(_Ou,new T2(1,_Ot,new T(function(){return _x(_Ow,_Oz);}))));};return B(_Np(2,_NV,_Oy));});return _tu(new T1(0,function(_OA){var _OB=u_towupper(E(_OA));if(_OB>>>0>1114111){return _bg(_OB);}else{return (E(_Oq)!=_OB)?new T0(2):E(_Ox);}}),_Ox);};return C > 19 ? new F(function(){return _Np(2,_NV,_Ov);}) : (++C,_Np(2,_NV,_Ov));},_OC=function(_OD){return C > 19 ? new F(function(){return A1(_On,function(_OE){return C > 19 ? new F(function(){return _Os(_OE,_OD);}) : (++C,_Os(_OE,_OD));});}) : (++C,A1(_On,function(_OE){return C > 19 ? new F(function(){return _Os(_OE,_OD);}) : (++C,_Os(_OE,_OD));}));},_OF=function(_OG){return new T1(1,_ux(_OC,_Ob,_OG));},_OH=function(_OI){var _OJ=u_iswalpha(E(_OI));return (E(_OJ)==0)?false:true;},_OK=function(_OL){return function(_OM){var _ON=E(_OM),_OO=u_iswalpha(_ON);return (E(_OO)==0)?new T0(2):new T1(1,_uX(_OH,function(_OP){return C > 19 ? new F(function(){return A1(_OL,new T2(1,_ON,_OP));}) : (++C,A1(_OL,new T2(1,_ON,_OP)));}));};},_OQ=function(_OR){return new T1(0,_OK(_OR));},_OS=function(_OT){return new T1(1,_ux(_OQ,_OF,_OT));},_OU=function(_OV,_OW){var _OX=new T(function(){var _OY=function(_OZ){return C > 19 ? new F(function(){return _OU(_OV,function(_P0){return C > 19 ? new F(function(){return A1(_OW,new T2(1,_OZ,_P0));}) : (++C,A1(_OW,new T2(1,_OZ,_P0)));});}) : (++C,_OU(_OV,function(_P0){return C > 19 ? new F(function(){return A1(_OW,new T2(1,_OZ,_P0));}) : (++C,A1(_OW,new T2(1,_OZ,_P0)));}));};return B(A1(_OV,_OY));});return _tu(B(A1(_OW,__Z)),_OX);},_P1=function(_P2){return function(_P3){var _P4=E(_P3);if((_P4-48|0)>>>0>9){return new T0(2);}else{return C > 19 ? new F(function(){return _OU(_NV,function(_P5){return C > 19 ? new F(function(){return A1(_P2,new T2(1,_P4,_P5));}) : (++C,A1(_P2,new T2(1,_P4,_P5)));});}) : (++C,_OU(_NV,function(_P5){return C > 19 ? new F(function(){return A1(_P2,new T2(1,_P4,_P5));}) : (++C,A1(_P2,new T2(1,_P4,_P5)));}));}};},_P6=function(_P7){return new T1(0,_P1(_P7));},_P8=function(_P9){var _Pa=function(_Pb){var _Pc=E(_Pb);if((_Pc-48|0)>>>0>9){return new T0(2);}else{return C > 19 ? new F(function(){return _OU(_NV,function(_Pd){return C > 19 ? new F(function(){return A1(_P9,new T2(1,_Pc,_Pd));}) : (++C,A1(_P9,new T2(1,_Pc,_Pd)));});}) : (++C,_OU(_NV,function(_Pd){return C > 19 ? new F(function(){return A1(_P9,new T2(1,_Pc,_Pd));}) : (++C,A1(_P9,new T2(1,_Pc,_Pd)));}));}},_Pe=function(_Pf){return E(new T1(0,_Pa));};return function(_Pg){return C > 19 ? new F(function(){return A2(_Bs,_Pg,_Pe);}) : (++C,A2(_Bs,_Pg,_Pe));};},_Ph=function(_Pi){return new T1(1,_P8(_Pi));},_Pj=function(_Pk){return function(_Pl){var _Pm=E(_Pl);return ((_Pm-48|0)>>>0>9)?new T0(2):new T1(1,_uX(_NZ,function(_Pn){return C > 19 ? new F(function(){return A1(_Pk,new T2(1,_Pm,_Pn));}) : (++C,A1(_Pk,new T2(1,_Pm,_Pn)));}));};},_Po=function(_Pp){return new T1(0,_Pj(_Pp));},_Pq=new T(function(){var _Pr=u_towupper(45);if(_Pr>>>0>1114111){return _bg(_Pr);}else{return _Pr;}}),_Ps=function(_Pt){var _Pu=function(_Pv){var _Pw=E(_Pv);return ((_Pw-48|0)>>>0>9)?new T0(2):new T1(1,_uX(_NZ,function(_Px){return C > 19 ? new F(function(){return A1(_Pt,new T2(1,45,new T2(1,_Pw,_Px)));}) : (++C,A1(_Pt,new T2(1,45,new T2(1,_Pw,_Px))));}));};return function(_Py){var _Pz=u_towupper(E(_Py));if(_Pz>>>0>1114111){return _bg(_Pz);}else{return (E(_Pq)!=_Pz)?new T0(2):E(new T1(0,_Pu));}};},_PA=function(_PB){return new T1(0,_Ps(_PB));},_PC=function(_PD){return new T1(1,_ux(_PA,_Po,_PD));},_PE=function(_PF){return (_PF<=55)?new T2(1,function(_PG){return new T1(1,_NB(new T2(1,_PF,__Z),_PG));},new T(function(){return _PE(_PF+1|0);})):__Z;},_PH=new T(function(){return _xw(new T(function(){return _PE(49);}));}),_PI=function(_PJ){return (_PJ<=54)?new T2(1,function(_PK){return new T1(1,_NB(new T2(1,_PJ,__Z),_PK));},new T(function(){return _PI(_PJ+1|0);})):__Z;},_PL=new T(function(){return _xw(new T(function(){return _PI(48);}));}),_PM=function(_PN,_PO){return new T1(1,_NB(new T(function(){return E(E(_PN).b);}),_PO));},_PP=function(_PQ,_PR){return new T1(1,_NB(new T(function(){return E(E(_PQ).a);}),_PR));},_PS=function(_PT){return new T0(2);},_PU=function(_PV,_PW){var _PX=E(_PW);if(!_PX._){return _NT;}else{var _PY=_PX.b,_PZ=E(_PX.a);switch(_PZ._){case 0:var _Q0=_PZ.a,_Q1=_PZ.b,_Q2=new T(function(){return _PU(_PV,_PY);}),_Q3=new T(function(){switch(E(_Q1)){case 65:return _xw(_hg(_PP,E(_PV).a));break;case 66:return _xw(_hg(_PP,E(_PV).b));break;case 67:return function(_Q4){var _Q5=E(_Q0);if(!_Q5._){return _Ph(_Q4);}else{switch(E(_Q5.a)){case 0:return _P6(_Q4);case 1:return _Ph(_Q4);default:return C > 19 ? new F(function(){return _Np(2,_NV,_Q4);}) : (++C,_Np(2,_NV,_Q4));}}};break;case 71:return function(_Q6){var _Q7=E(_Q0);if(!_Q7._){return _Ph(_Q6);}else{switch(E(_Q7.a)){case 0:return _P6(_Q6);case 1:return _Ph(_Q6);default:return C > 19 ? new F(function(){return _Np(4,_NV,_Q6);}) : (++C,_Np(4,_NV,_Q6));}}};break;case 72:return function(_Q8){var _Q9=E(_Q0);if(!_Q9._){return C > 19 ? new F(function(){return _Np(2,_NV,_Q8);}) : (++C,_Np(2,_NV,_Q8));}else{switch(E(_Q9.a)){case 0:return _P6(_Q8);case 1:return _Ph(_Q8);default:return C > 19 ? new F(function(){return _Np(2,_NV,_Q8);}) : (++C,_Np(2,_NV,_Q8));}}};break;case 73:return function(_Qa){var _Qb=E(_Q0);if(!_Qb._){return C > 19 ? new F(function(){return _Np(2,_NV,_Qa);}) : (++C,_Np(2,_NV,_Qa));}else{switch(E(_Qb.a)){case 0:return _P6(_Qa);case 1:return _Ph(_Qa);default:return C > 19 ? new F(function(){return _Np(2,_NV,_Qa);}) : (++C,_Np(2,_NV,_Qa));}}};break;case 77:return function(_Qc){var _Qd=E(_Q0);if(!_Qd._){return C > 19 ? new F(function(){return _Np(2,_NV,_Qc);}) : (++C,_Np(2,_NV,_Qc));}else{switch(E(_Qd.a)){case 0:return _P6(_Qc);case 1:return _Ph(_Qc);default:return C > 19 ? new F(function(){return _Np(2,_NV,_Qc);}) : (++C,_Np(2,_NV,_Qc));}}};break;case 80:var _Qe=new T(function(){return E(E(_PV).c);}),_Qf=new T(function(){return E(E(_Qe).b);}),_Qg=new T(function(){return E(E(_Qe).a);});return _xw(new T2(1,function(_Qh){return new T1(1,_NB(_Qg,_Qh));},new T2(1,function(_Qi){return new T1(1,_NB(_Qf,_Qi));},__Z)));break;case 81:return _Od;break;case 83:return function(_Qj){var _Qk=E(_Q0);if(!_Qk._){return C > 19 ? new F(function(){return _Np(2,_NV,_Qj);}) : (++C,_Np(2,_NV,_Qj));}else{switch(E(_Qk.a)){case 0:return _P6(_Qj);case 1:return _Ph(_Qj);default:return C > 19 ? new F(function(){return _Np(2,_NV,_Qj);}) : (++C,_Np(2,_NV,_Qj));}}};break;case 85:return function(_Ql){var _Qm=E(_Q0);if(!_Qm._){return C > 19 ? new F(function(){return _Np(2,_NV,_Ql);}) : (++C,_Np(2,_NV,_Ql));}else{switch(E(_Qm.a)){case 0:return _P6(_Ql);case 1:return _Ph(_Ql);default:return C > 19 ? new F(function(){return _Np(2,_NV,_Ql);}) : (++C,_Np(2,_NV,_Ql));}}};break;case 86:return function(_Qn){var _Qo=E(_Q0);if(!_Qo._){return C > 19 ? new F(function(){return _Np(2,_NV,_Qn);}) : (++C,_Np(2,_NV,_Qn));}else{switch(E(_Qo.a)){case 0:return _P6(_Qn);case 1:return _Ph(_Qn);default:return C > 19 ? new F(function(){return _Np(2,_NV,_Qn);}) : (++C,_Np(2,_NV,_Qn));}}};break;case 87:return function(_Qp){var _Qq=E(_Q0);if(!_Qq._){return C > 19 ? new F(function(){return _Np(2,_NV,_Qp);}) : (++C,_Np(2,_NV,_Qp));}else{switch(E(_Qq.a)){case 0:return _P6(_Qp);case 1:return _Ph(_Qp);default:return C > 19 ? new F(function(){return _Np(2,_NV,_Qp);}) : (++C,_Np(2,_NV,_Qp));}}};break;case 89:return function(_Qr){var _Qs=E(_Q0);if(!_Qs._){return _Ph(_Qr);}else{switch(E(_Qs.a)){case 0:return _P6(_Qr);case 1:return _Ph(_Qr);default:return C > 19 ? new F(function(){return _Np(4,_NV,_Qr);}) : (++C,_Np(4,_NV,_Qr));}}};break;case 90:return _OS;break;case 97:return _xw(_hg(_PM,E(_PV).a));break;case 98:return _xw(_hg(_PM,E(_PV).b));break;case 100:return function(_Qt){var _Qu=E(_Q0);if(!_Qu._){return C > 19 ? new F(function(){return _Np(2,_NV,_Qt);}) : (++C,_Np(2,_NV,_Qt));}else{switch(E(_Qu.a)){case 0:return _P6(_Qt);case 1:return _Ph(_Qt);default:return C > 19 ? new F(function(){return _Np(2,_NV,_Qt);}) : (++C,_Np(2,_NV,_Qt));}}};break;case 101:return function(_Qv){var _Qw=E(_Q0);if(!_Qw._){return _Ph(_Qv);}else{switch(E(_Qw.a)){case 0:return _P6(_Qv);case 1:return _Ph(_Qv);default:return C > 19 ? new F(function(){return _Np(2,_NV,_Qv);}) : (++C,_Np(2,_NV,_Qv));}}};break;case 102:return function(_Qx){var _Qy=E(_Q0);if(!_Qy._){return _Ph(_Qx);}else{switch(E(_Qy.a)){case 0:return _P6(_Qx);case 1:return _Ph(_Qx);default:return C > 19 ? new F(function(){return _Np(2,_NV,_Qx);}) : (++C,_Np(2,_NV,_Qx));}}};break;case 103:return function(_Qz){var _QA=E(_Q0);if(!_QA._){return C > 19 ? new F(function(){return _Np(2,_NV,_Qz);}) : (++C,_Np(2,_NV,_Qz));}else{switch(E(_QA.a)){case 0:return _P6(_Qz);case 1:return _Ph(_Qz);default:return C > 19 ? new F(function(){return _Np(2,_NV,_Qz);}) : (++C,_Np(2,_NV,_Qz));}}};break;case 106:return function(_QB){var _QC=E(_Q0);if(!_QC._){return C > 19 ? new F(function(){return _Np(3,_NV,_QB);}) : (++C,_Np(3,_NV,_QB));}else{switch(E(_QC.a)){case 0:return _P6(_QB);case 1:return _Ph(_QB);default:return C > 19 ? new F(function(){return _Np(3,_NV,_QB);}) : (++C,_Np(3,_NV,_QB));}}};break;case 107:return function(_QD){var _QE=E(_Q0);if(!_QE._){return _Ph(_QD);}else{switch(E(_QE.a)){case 0:return _P6(_QD);case 1:return _Ph(_QD);default:return C > 19 ? new F(function(){return _Np(2,_NV,_QD);}) : (++C,_Np(2,_NV,_QD));}}};break;case 108:return function(_QF){var _QG=E(_Q0);if(!_QG._){return _Ph(_QF);}else{switch(E(_QG.a)){case 0:return _P6(_QF);case 1:return _Ph(_QF);default:return C > 19 ? new F(function(){return _Np(2,_NV,_QF);}) : (++C,_Np(2,_NV,_QF));}}};break;case 109:return function(_QH){var _QI=E(_Q0);if(!_QI._){return C > 19 ? new F(function(){return _Np(2,_NV,_QH);}) : (++C,_Np(2,_NV,_QH));}else{switch(E(_QI.a)){case 0:return _P6(_QH);case 1:return _Ph(_QH);default:return C > 19 ? new F(function(){return _Np(2,_NV,_QH);}) : (++C,_Np(2,_NV,_QH));}}};break;case 112:var _QJ=new T(function(){return E(E(_PV).c);}),_QK=new T(function(){return E(E(_QJ).b);}),_QL=new T(function(){return E(E(_QJ).a);});return _xw(new T2(1,function(_QM){return new T1(1,_NB(_QL,_QM));},new T2(1,function(_QN){return new T1(1,_NB(_QK,_QN));},__Z)));break;case 113:return function(_QO){var _QP=E(_Q0);if(!_QP._){return C > 19 ? new F(function(){return _Np(12,_NV,_QO);}) : (++C,_Np(12,_NV,_QO));}else{switch(E(_QP.a)){case 0:return _P6(_QO);case 1:return _Ph(_QO);default:return C > 19 ? new F(function(){return _Np(12,_NV,_QO);}) : (++C,_Np(12,_NV,_QO));}}};break;case 115:return _PC;break;case 117:return E(_PH);break;case 119:return E(_PL);break;case 121:return function(_QQ){var _QR=E(_Q0);if(!_QR._){return C > 19 ? new F(function(){return _Np(2,_NV,_QQ);}) : (++C,_Np(2,_NV,_QQ));}else{switch(E(_QR.a)){case 0:return _P6(_QQ);case 1:return _Ph(_QQ);default:return C > 19 ? new F(function(){return _Np(2,_NV,_QQ);}) : (++C,_Np(2,_NV,_QQ));}}};break;case 122:return _OC;break;default:return _PS;}}),_QS=function(_QT){var _QU=function(_QV){return C > 19 ? new F(function(){return A1(_Q2,function(_QW){return C > 19 ? new F(function(){return A1(_QT,new T2(1,new T2(0,_Q1,_QV),_QW));}) : (++C,A1(_QT,new T2(1,new T2(0,_Q1,_QV),_QW)));});}) : (++C,A1(_Q2,function(_QW){return C > 19 ? new F(function(){return A1(_QT,new T2(1,new T2(0,_Q1,_QV),_QW));}) : (++C,A1(_QT,new T2(1,new T2(0,_Q1,_QV),_QW)));}));};return C > 19 ? new F(function(){return A1(_Q3,_QU);}) : (++C,A1(_Q3,_QU));};return _QS;case 1:var _QX=new T(function(){return _PU(_PV,_PY);}),_QY=function(_QZ){var _R0=new T(function(){return B(A1(_QX,_QZ));}),_R1=function(_R2){return E(_R0);},_R3=new T(function(){var _R4=E(_PY);if(!_R4._){return new T1(1,function(_R5){return C > 19 ? new F(function(){return A2(_Bs,_R5,_R1);}) : (++C,A2(_Bs,_R5,_R1));});}else{if(E(_R4.a)._==1){return E(_R0);}else{return new T1(1,function(_R6){return C > 19 ? new F(function(){return A2(_Bs,_R6,_R1);}) : (++C,A2(_Bs,_R6,_R1));});}}});return new T1(0,function(_R7){var _R8=E(_R7),_R9=_R8>>>0;if(_R9>887){var _Ra=u_iswspace(_R8);return (E(_Ra)==0)?new T0(2):E(_R3);}else{return (_R9==32)?E(_R3):(_R9-9>>>0>4)?(_R9==160)?E(_R3):new T0(2):E(_R3);}});};return _QY;default:var _Rb=new T(function(){return _PU(_PV,_PY);}),_Rc=new T(function(){var _Rd=u_towupper(E(_PZ.a));if(_Rd>>>0>1114111){return _bg(_Rd);}else{return _Rd;}}),_Re=function(_Rf){var _Rg=new T(function(){return B(A1(_Rb,_Rf));});return new T1(0,function(_Rh){var _Ri=u_towupper(E(_Rh));if(_Ri>>>0>1114111){return _bg(_Ri);}else{return (E(_Rc)!=_Ri)?new T0(2):E(_Rg);}});};return _Re;}}},_Rj=function(_Rk){return E(E(_Rk).g);},_Rl=function(_Rm){return E(E(_Rm).f);},_Rn=function(_Ro,_Rp,_Rq){var _Rr=new T(function(){return B(A1(_Ro,_Rp));}),_Rs=new T(function(){var _Rt=new T(function(){return _Ru(_Nn);}),_Rv=new T(function(){return _Ru(_Ne);}),_Rw=new T(function(){return _Ru(_Nm);}),_Rx=new T(function(){return _Ru(_Nl);}),_Ry=new T(function(){return _Ru(_Rl(_Rp));}),_Rz=new T(function(){return _Ru(_Ni(_Rp));}),_RA=new T(function(){return _Ru(_Nk);}),_RB=new T(function(){return _Ru(_Rj(_Rp));}),_RC=new T(function(){return _Ru(_Ng(_Rp));}),_RD=function(_RE,_RF){var _RG=E(_RF);switch(_RG){case 37:return E(_No);case 68:return E(_Rt);case 70:return E(_Rv);case 82:return E(_Rw);case 84:return E(_Rx);case 88:return E(_Ry);case 99:return E(_Rz);case 104:return E(_RA);case 114:return E(_RB);case 120:return E(_RC);default:return new T2(1,new T2(0,_RE,_RG),__Z);}},_RH=new T(function(){return _Ru(__Z);}),_Ru=function(_RI){var _RJ=E(_RI);if(!_RJ._){return __Z;}else{var _RK=_RJ.b,_RL=E(_RJ.a),_RM=function(_RN){var _RO=_RL>>>0;if(_RO>887){var _RP=u_iswspace(_RL);return (E(_RP)==0)?new T2(1,new T1(2,_RL),new T(function(){return _Ru(_RK);})):new T2(1,_Nf,new T(function(){return _Ru(_RK);}));}else{return (_RO==32)?new T2(1,_Nf,new T(function(){return _Ru(_RK);})):(_RO-9>>>0>4)?(_RO==160)?new T2(1,_Nf,new T(function(){return _Ru(_RK);})):new T2(1,new T1(2,_RL),new T(function(){return _Ru(_RK);})):new T2(1,_Nf,new T(function(){return _Ru(_RK);}));}};if(_RL==37){var _RQ=E(_RK);if(!_RQ._){return _RM(_);}else{var _RR=_RQ.b,_RS=E(_RQ.a);switch(_RS){case 37:return _x(_No,new T(function(){return _Ru(_RR);},1));case 45:var _RT=E(_RR);if(!_RT._){return _x(new T2(1,new T2(0,__Z,_RS),__Z),_RH);}else{return _x(_RD(new T1(1,0),E(_RT.a)),new T(function(){return _Ru(_RT.b);},1));}break;case 48:var _RU=E(_RR);if(!_RU._){return _x(new T2(1,new T2(0,__Z,_RS),__Z),_RH);}else{return _x(_RD(new T1(1,2),E(_RU.a)),new T(function(){return _Ru(_RU.b);},1));}break;case 68:return _x(_Rt,new T(function(){return _Ru(_RR);},1));case 70:return _x(_Rv,new T(function(){return _Ru(_RR);},1));case 82:return _x(_Rw,new T(function(){return _Ru(_RR);},1));case 84:return _x(_Rx,new T(function(){return _Ru(_RR);},1));case 88:return _x(_Ry,new T(function(){return _Ru(_RR);},1));case 95:var _RV=E(_RR);if(!_RV._){return _x(new T2(1,new T2(0,__Z,_RS),__Z),_RH);}else{return _x(_RD(new T1(1,1),E(_RV.a)),new T(function(){return _Ru(_RV.b);},1));}break;case 99:return _x(_Rz,new T(function(){return _Ru(_RR);},1));case 104:return _x(_RA,new T(function(){return _Ru(_RR);},1));case 114:return _x(_RB,new T(function(){return _Ru(_RR);},1));case 120:return _x(_RC,new T(function(){return _Ru(_RR);},1));default:return _x(new T2(1,new T2(0,__Z,_RS),__Z),new T(function(){return _Ru(_RR);},1));}}}else{return _RM(_);}}};return _PU(_Rp,_Ru(_Rq));}),_RW=function(_RX){var _RY=function(_RZ){return C > 19 ? new F(function(){return A1(_RX,new T(function(){return B(A1(_Rr,_RZ));}));}) : (++C,A1(_RX,new T(function(){return B(A1(_Rr,_RZ));})));};return C > 19 ? new F(function(){return A1(_Rs,_RY);}) : (++C,A1(_Rs,_RY));};return _RW;},_S0=function(_S1,_S2,_S3,_S4,_S5){if(!E(_S2)){return _N7(_tk(B(A(_Rn,[_S1,_S3,_S4,_up])),_S5));}else{var _S6=function(_S7){var _S8=new T(function(){return B(A1(_Rn(_S1,_S3,_S4),_S7));}),_S9=function(_Sa){return E(_S8);};return new T1(1,function(_Sb){return C > 19 ? new F(function(){return A2(_Bs,_Sb,_S9);}) : (++C,A2(_Bs,_Sb,_S9));});};return _N0(_tk(new T1(1,_ux(_S6,new T(function(){return _Rn(_S1,_S3,_S4);}),_up)),_S5));}},_Sc=new T2(1,34,__Z),_Sd=new T(function(){return unCStr("ACK");}),_Se=new T(function(){return unCStr("BEL");}),_Sf=new T(function(){return unCStr("BS");}),_Sg=new T(function(){return unCStr("SP");}),_Sh=new T(function(){return unCStr("US");}),_Si=new T(function(){return unCStr("RS");}),_Sj=new T(function(){return unCStr("GS");}),_Sk=new T(function(){return unCStr("FS");}),_Sl=new T(function(){return unCStr("ESC");}),_Sm=new T(function(){return unCStr("SUB");}),_Sn=new T(function(){return unCStr("EM");}),_So=new T(function(){return unCStr("CAN");}),_Sp=new T(function(){return unCStr("ETB");}),_Sq=new T(function(){return unCStr("SYN");}),_Sr=new T(function(){return unCStr("NAK");}),_Ss=new T(function(){return unCStr("DC4");}),_St=new T(function(){return unCStr("DC3");}),_Su=new T(function(){return unCStr("DC2");}),_Sv=new T(function(){return unCStr("DC1");}),_Sw=new T(function(){return unCStr("DLE");}),_Sx=new T(function(){return unCStr("SI");}),_Sy=new T(function(){return unCStr("SO");}),_Sz=new T(function(){return unCStr("CR");}),_SA=new T(function(){return unCStr("FF");}),_SB=new T(function(){return unCStr("VT");}),_SC=new T(function(){return unCStr("LF");}),_SD=new T(function(){return unCStr("HT");}),_SE=new T(function(){return unCStr("ENQ");}),_SF=new T(function(){return unCStr("EOT");}),_SG=new T(function(){return unCStr("ETX");}),_SH=new T(function(){return unCStr("STX");}),_SI=new T(function(){return unCStr("SOH");}),_SJ=new T(function(){return unCStr("NUL");}),_SK=new T(function(){return unCStr("\\DEL");}),_SL=new T(function(){return unCStr("\\a");}),_SM=new T(function(){return unCStr("\\\\");}),_SN=new T(function(){return unCStr("\\SO");}),_SO=new T(function(){return unCStr("\\r");}),_SP=new T(function(){return unCStr("\\f");}),_SQ=new T(function(){return unCStr("\\v");}),_SR=new T(function(){return unCStr("\\n");}),_SS=new T(function(){return unCStr("\\t");}),_ST=new T(function(){return unCStr("\\b");}),_SU=function(_SV,_SW){if(_SV<=127){var _SX=E(_SV);switch(_SX){case 92:return _x(_SM,_SW);case 127:return _x(_SK,_SW);default:if(_SX<32){switch(_SX){case 7:return _x(_SL,_SW);case 8:return _x(_ST,_SW);case 9:return _x(_SS,_SW);case 10:return _x(_SR,_SW);case 11:return _x(_SQ,_SW);case 12:return _x(_SP,_SW);case 13:return _x(_SO,_SW);case 14:return _x(_SN,new T(function(){var _SY=E(_SW);if(!_SY._){return __Z;}else{if(E(_SY.a)==72){return unAppCStr("\\&",_SY);}else{return _SY;}}},1));default:return _x(new T2(1,92,new T(function(){return _7g(new T2(1,_SJ,new T2(1,_SI,new T2(1,_SH,new T2(1,_SG,new T2(1,_SF,new T2(1,_SE,new T2(1,_Sd,new T2(1,_Se,new T2(1,_Sf,new T2(1,_SD,new T2(1,_SC,new T2(1,_SB,new T2(1,_SA,new T2(1,_Sz,new T2(1,_Sy,new T2(1,_Sx,new T2(1,_Sw,new T2(1,_Sv,new T2(1,_Su,new T2(1,_St,new T2(1,_Ss,new T2(1,_Sr,new T2(1,_Sq,new T2(1,_Sp,new T2(1,_So,new T2(1,_Sn,new T2(1,_Sm,new T2(1,_Sl,new T2(1,_Sk,new T2(1,_Sj,new T2(1,_Si,new T2(1,_Sh,new T2(1,_Sg,__Z))))))))))))))))))))))))))))))))),_SX);})),_SW);}}else{return new T2(1,_SX,_SW);}}}else{var _SZ=new T(function(){var _T0=jsShowI(_SV);return _x(fromJSStr(_T0),new T(function(){var _T1=E(_SW);if(!_T1._){return __Z;}else{var _T2=E(_T1.a);if(_T2<48){return _T1;}else{if(_T2>57){return _T1;}else{return unAppCStr("\\&",_T1);}}}},1));});return new T2(1,92,_SZ);}},_T3=new T(function(){return unCStr("\\\"");}),_T4=function(_T5,_T6){var _T7=E(_T5);if(!_T7._){return E(_T6);}else{var _T8=_T7.b,_T9=E(_T7.a);if(_T9==34){return _x(_T3,new T(function(){return _T4(_T8,_T6);},1));}else{return _SU(_T9,new T(function(){return _T4(_T8,_T6);}));}}},_Ta=function(_Tb,_Tc,_Td,_Te,_Tf,_Tg){var _Th=_S0(_Tc,_Td,_Te,_Tf,_Tg);if(!_Th._){var _Ti=new T(function(){return unAppCStr("parseTimeM: no parse of ",new T2(1,34,new T(function(){return _T4(_Tg,_Sc);})));});return C > 19 ? new F(function(){return A2(_MR,_Tb,_Ti);}) : (++C,A2(_MR,_Tb,_Ti));}else{if(!E(_Th.b)._){return C > 19 ? new F(function(){return A2(_Mn,_Tb,_Th.a);}) : (++C,A2(_Mn,_Tb,_Th.a));}else{var _Tj=new T(function(){return unAppCStr("parseTimeM: multiple parses of ",new T2(1,34,new T(function(){return _T4(_Tg,_Sc);})));});return C > 19 ? new F(function(){return A2(_MR,_Tb,_Tj);}) : (++C,A2(_MR,_Tb,_Tj));}}},_Tk=new T(function(){return err(_st);}),_Tl=new T(function(){return err(_sr);}),_Tm=new T(function(){return B(A3(_Ei,_ED,0,_Ea));}),_Tn=function(_To){var _Tp=E(_To);return _mM(_Tp.a,_Tp.b);},_Tq=function(_Tr,_){var _Ts=E(_Tr);if(!_Ts._){return E(_LX);}else{var _Tt=_Ts.a,_Tu=E(_Ts.b);if(!_Tu._){return E(_LX);}else{var _Tv=_Tu.a,_Tw=E(_Tu.b);if(!_Tw._){return E(_LX);}else{var _Tx=_Tw.a,_Ty=E(_Tw.b);if(!_Ty._){return E(_LX);}else{var _Tz=_Ty.a,_TA=E(_Ty.b);if(!_TA._){return E(_LX);}else{var _TB=_TA.a;if(!E(_TA.b)._){var _TC=function(_){var _TD=_LV(E(_Tx),"value"),_TE=_LV(E(_Tv),"value"),_TF=_LV(E(_Tz),"value"),_TG=toJSStr(E(_LZ)),_TH=new T(function(){var _TI=_EP(_tk(_Tm,new T(function(){var _TJ=String(_TD);return fromJSStr(_TJ);})));if(!_TI._){return E(_Tl);}else{if(!E(_TI.b)._){var _TK=_EP(_tk(_Tm,new T(function(){var _TL=String(_TE);return fromJSStr(_TL);})));if(!_TK._){return E(_Tl);}else{if(!E(_TK.b)._){var _TM=_EP(_tk(_Tm,new T(function(){var _TN=String(_TF);return fromJSStr(_TN);})));if(!_TM._){return E(_Tl);}else{if(!E(_TM.b)._){return _41(_4b(_4b(_Kn,_41(_TI.a,_4b(_4b(_TK.a,_TM.a),_Kl))),_dt),_Kg);}else{return E(_Tk);}}}else{return E(_Tk);}}}else{return E(_Tk);}}}),_TO=_J1(_TH),_TP=_TO.a,_TQ=_TO.b,_TR=_fz(_mM(_TP,_TQ),_29,_dt,_29),_TS=_LW(E(_Tt),_TG,toJSStr(_8H(0,_JY(_lK,_TR.a,_TR.b),__Z))),_TT=_LW(E(_TB),_TG,toJSStr(_KJ(_qr,_KI,_M0,new T2(0,_TP,_TQ))));return _qt(_);},_TU=B(A(_Mp,[_qw,_qu,_2j,_Tx,1,function(_TV,_){return _TC(_);},_])),_TW=B(A(_Mp,[_qw,_qu,_2j,_Tv,1,function(_TX,_){return _TC(_);},_])),_TY=function(_TZ,_){var _U0=_LV(E(_Tt),"value"),_U1=_LV(E(_Tz),"value"),_U2=new T(function(){var _U3=_EP(_tk(_Tm,new T(function(){var _U4=String(_U1);return fromJSStr(_U4);})));if(!_U3._){return E(_Tl);}else{if(!E(_U3.b)._){return E(_U3.a);}else{return E(_Tk);}}}),_U5=new T(function(){var _U6=_EP(_tk(_Tm,new T(function(){var _U7=String(_U0);return fromJSStr(_U7);})));if(!_U6._){return E(_Tl);}else{if(!E(_U6.b)._){return _4b(_U6.a,_dt);}else{return E(_Tk);}}}),_U8=_J1(_U5),_U9=_U8.a,_Ua=_U8.b,_Ub=function(_Uc){var _Ud=toJSStr(E(_LZ)),_Ue=_LW(E(_Tv),_Ud,toJSStr(_8H(0,_Ko(_U9,_Ua,_U2),__Z))),_Uf=_LW(E(_Tx),_Ud,toJSStr(_8H(0,_Ku(_U9,_Ua,_U2),__Z)));return _qt(_);};switch(_80(_U9,_Ke)){case 0:return 0;case 1:if(!_80(_Ua,_Kf)){return 0;}else{return _Ub(_);}break;default:return _Ub(_);}},_Ug=B(A(_Mp,[_qw,_qu,_2j,_Tt,1,_TY,_])),_Uh=function(_Ui,_){var _Uj=_LV(E(_TB),"value"),_Uk=_LV(E(_Tz),"value"),_Ul=new T(function(){var _Um=_EP(_tk(_Tm,new T(function(){var _Un=String(_Uk);return fromJSStr(_Un);})));if(!_Um._){return E(_Tl);}else{if(!E(_Um.b)._){return E(_Um.a);}else{return E(_Tk);}}}),_Uo=B(_Ta(new T5(0,new T5(0,new T2(0,_qE,_qM),_qP,_qI,_qx,_qA),_qR,_qx,_qP,_qV),_Jy,true,_KI,_M0,new T(function(){var _Up=String(_Uj);return fromJSStr(_Up);})));if(!_Uo._){return 0;}else{var _Uq=_Uo.a,_Ur=toJSStr(E(_LZ)),_Us=_LW(E(_Tv),_Ur,toJSStr(_8H(0,_Kz(_Uq,_Ul),__Z))),_Ut=_LW(E(_Tx),_Ur,toJSStr(_8H(0,_KD(_Uq,_Ul),__Z))),_Uu=_fz(_Tn(_Uq),_29,_dt,_29),_Uv=_LW(E(_Tt),_Ur,toJSStr(_8H(0,_JY(_lK,_Uu.a,_Uu.b),__Z)));return _qt(_);}},_Uw=B(A(_Mp,[_qw,_qu,_2j,_TB,1,_Uh,_]));return 0;}else{return E(_LX);}}}}}}},_Ux=(function(id){return document.getElementById(id);}),_Uy=function(_Uz){var _UA=E(_Uz);return (_UA._==0)?E(_rk):E(_UA.a);},_UB=function(_UC,_UD){while(1){var _UE=(function(_UF,_UG){var _UH=E(_UF);if(!_UH._){return __Z;}else{var _UI=_UH.b,_UJ=E(_UG);if(!_UJ._){return __Z;}else{var _UK=_UJ.b;if(!E(_UJ.a)._){return new T2(1,_UH.a,new T(function(){return _UB(_UI,_UK);}));}else{_UC=_UI;_UD=_UK;return __continue;}}}})(_UC,_UD);if(_UE!=__continue){return _UE;}}},_UL=new T(function(){return unAppCStr("[]",__Z);}),_UM=function(_UN){var _UO=E(_UN);if(!_UO._){return E(new T2(1,93,__Z));}else{var _UP=new T(function(){return _x(fromJSStr(E(_UO.a)),new T(function(){return _UM(_UO.b);},1));});return new T2(1,44,_UP);}},_UQ=function(_UR,_US){var _UT=new T(function(){var _UU=_UB(_UR,_US);if(!_UU._){return E(_UL);}else{var _UV=new T(function(){return _x(fromJSStr(E(_UU.a)),new T(function(){return _UM(_UU.b);},1));});return new T2(1,91,_UV);}});return err(unAppCStr("Elements with the following IDs could not be found: ",_UT));},_UW=function(_UX){while(1){var _UY=E(_UX);if(!_UY._){return false;}else{if(!E(_UY.a)._){return true;}else{_UX=_UY.b;continue;}}}},_UZ=function(_V0,_V1,_V2){var _V3=_M3(_V0),_V4=function(_V5){if(!_UW(_V5)){return C > 19 ? new F(function(){return A1(_V2,new T(function(){return _hg(_Uy,_V5);}));}) : (++C,A1(_V2,new T(function(){return _hg(_Uy,_V5);})));}else{return _UQ(_V1,_V5);}},_V6=new T(function(){var _V7=new T(function(){return B(A2(_Mn,_V3,__Z));}),_V8=function(_V9){var _Va=E(_V9);if(!_Va._){return E(_V7);}else{var _Vb=new T(function(){return B(_V8(_Va.b));}),_Vc=function(_Vd){return C > 19 ? new F(function(){return A3(_M5,_V3,_Vb,function(_Ve){return C > 19 ? new F(function(){return A2(_Mn,_V3,new T2(1,_Vd,_Ve));}) : (++C,A2(_Mn,_V3,new T2(1,_Vd,_Ve)));});}) : (++C,A3(_M5,_V3,_Vb,function(_Ve){return C > 19 ? new F(function(){return A2(_Mn,_V3,new T2(1,_Vd,_Ve));}) : (++C,A2(_Mn,_V3,new T2(1,_Vd,_Ve)));}));},_Vf=new T(function(){return B(A2(_Mj,_V0,function(_){var _Vg=_Ux(E(_Va.a)),_Vh=__eq(_Vg,E(_Mi));return (E(_Vh)==0)?new T1(1,_Vg):__Z;}));});return C > 19 ? new F(function(){return A3(_M5,_V3,_Vf,_Vc);}) : (++C,A3(_M5,_V3,_Vf,_Vc));}};return B(_V8(_V1));});return C > 19 ? new F(function(){return A3(_M5,_V3,_V6,_V4);}) : (++C,A3(_M5,_V3,_V6,_V4));},_Vi=new T(function(){return B(_UZ(_1X,new T(function(){return _hg(function(_Vj){return toJSStr(E(_Vj));},new T2(1,new T(function(){return unCStr("dt");}),new T2(1,new T(function(){return unCStr("epoch");}),new T2(1,new T(function(){return unCStr("slot");}),new T2(1,new T(function(){return unCStr("k");}),new T2(1,new T(function(){return unCStr("ts");}),__Z))))));}),_Tq));});
var hasteMain = function() {B(A(_Vi, [0]));};window.onload = hasteMain;