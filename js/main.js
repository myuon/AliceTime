"use strict";
// This object will hold all exports.
var Haste = {};

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

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

/* Generic apply.
   Applies a function *or* a partial application object to a list of arguments.
   See https://ghc.haskell.org/trac/ghc/wiki/Commentary/Rts/HaskellExecution/FunctionCalls
   for more information.
*/
function A(f, args) {
    while(true) {
        f = E(f);
        if(f instanceof F) {
            f = E(B(f));
        }
        if(f instanceof PAP) {
            // f is a partial application
            if(args.length == f.arity) {
                // Saturated application
                return f.f.apply(null, f.args.concat(args));
            } else if(args.length < f.arity) {
                // Application is still unsaturated
                return new PAP(f.f, f.args.concat(args));
            } else {
                // Application is oversaturated; 
                var f2 = f.f.apply(null, f.args.concat(args.slice(0, f.arity)));
                args = args.slice(f.arity);
                f = B(f2);
            }
        } else if(f instanceof Function) {
            if(args.length == f.length) {
                return f.apply(null, args);
            } else if(args.length < f.length) {
                return new PAP(f, args);
            } else {
                var f2 = f.apply(null, args.slice(0, f.length));
                args = args.slice(f.length);
                f = B(f2);
            }
        } else {
            return f;
        }
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
        return t.x;
    } else {
        return t;
    }
}

/* Bounce
   Bounce on a trampoline for as long as we get a function back.
*/
function B(f) {
    while(f instanceof F) {
        var fun = f.f;
        f.f = __blackhole;
        f = fun();
    }
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
    return [0, (a-a%b)/b, a%b];
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
    return [0, x & 0xffffffff, x > 0x7fffffff];
}

function subC(a, b) {
    var x = a-b;
    return [0, x & 0xffffffff, x < -2147483648];
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
function unCStr(str) {return unAppCStr(str, [0]);}

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
        return [1,str.charCodeAt(i),new T(function() {
            return unAppCStr(str,chrs,i+1);
        })];
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str[0] == 1; str = E(str[2])) {
        s += String.fromCharCode(E(str[1]));
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
    mv.x = x[1];
    return x[2];
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

function jsCatch(act, handler) {
    try {
        return B(A(act,[0]));
    } catch(e) {
        return B(A(handler,[e, 0]));
    }
}

/* Haste represents constructors internally using 1 for the first constructor,
   2 for the second, etc.
   However, dataToTag should use 0, 1, 2, etc. Also, booleans might be unboxed.
 */
function dataToTag(x) {
    if(x instanceof Array) {
        return x[0];
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
    return popCnt(I_getBits(i,0)) + popCnt(I_getBits(i,1));
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
        return [0,1,0,0,0];
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
    return [0, sign*man, exp];
}

function decodeDouble(x) {
    if(x === 0) {
        // GHC 7.10+ *really* doesn't like 0 to be represented as anything
        // but zeroes all the way.
        return [0,1,0,0,0];
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
    return [0, sign, manHigh, manLow, exp];
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
    while(strs[0]) {
        strs = E(strs);
        arr.push(E(strs[1]));
        strs = E(strs[2]);
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
        return [0];
    }
    return [1,hs];
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return [0, jsRead(obj)];
    case 'string':
        return [1, obj];
    case 'boolean':
        return [2, obj]; // Booleans are special wrt constructor tags!
    case 'object':
        if(obj instanceof Array) {
            return [3, arr2lst_json(obj, 0)];
        } else if (obj == null) {
            return [5];
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
                xs = [1, [0, ks[i], toHS(obj[ks[i]])], xs];
            }
            return [4, xs];
        }
    }
}

function arr2lst_json(arr, elem) {
    if(elem >= arr.length) {
        return [0];
    }
    return [1, toHS(arr[elem]), new T(function() {return arr2lst_json(arr,elem+1);}),true]
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

// MVar implementation.
// Since Haste isn't concurrent, takeMVar and putMVar don't block on empty
// and full MVars respectively, but terminate the program since they would
// otherwise be blocking forever.

function newMVar() {
    return ({empty: true});
}

function tryTakeMVar(mv) {
    if(mv.empty) {
        return [0, 0, undefined];
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return [0, 1, val];
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

var Integer = function(bits, sign) {
  this.bits_ = [];
  this.sign_ = sign;

  var top = true;
  for (var i = bits.length - 1; i >= 0; i--) {
    var val = bits[i] | 0;
    if (!top || val != sign) {
      this.bits_[i] = val;
      top = false;
    }
  }
};

Integer.IntCache_ = {};

var I_fromInt = function(value) {
  if (-128 <= value && value < 128) {
    var cachedObj = Integer.IntCache_[value];
    if (cachedObj) {
      return cachedObj;
    }
  }

  var obj = new Integer([value | 0], value < 0 ? -1 : 0);
  if (-128 <= value && value < 128) {
    Integer.IntCache_[value] = obj;
  }
  return obj;
};

var I_fromNumber = function(value) {
  if (isNaN(value) || !isFinite(value)) {
    return Integer.ZERO;
  } else if (value < 0) {
    return I_negate(I_fromNumber(-value));
  } else {
    var bits = [];
    var pow = 1;
    for (var i = 0; value >= pow; i++) {
      bits[i] = (value / pow) | 0;
      pow *= Integer.TWO_PWR_32_DBL_;
    }
    return new Integer(bits, 0);
  }
};

var I_fromBits = function(bits) {
  var high = bits[bits.length - 1];
  return new Integer(bits, high & (1 << 31) ? -1 : 0);
};

var I_fromString = function(str, opt_radix) {
  if (str.length == 0) {
    throw Error('number format error: empty string');
  }

  var radix = opt_radix || 10;
  if (radix < 2 || 36 < radix) {
    throw Error('radix out of range: ' + radix);
  }

  if (str.charAt(0) == '-') {
    return I_negate(I_fromString(str.substring(1), radix));
  } else if (str.indexOf('-') >= 0) {
    throw Error('number format error: interior "-" character');
  }

  var radixToPower = I_fromNumber(Math.pow(radix, 8));

  var result = Integer.ZERO;
  for (var i = 0; i < str.length; i += 8) {
    var size = Math.min(8, str.length - i);
    var value = parseInt(str.substring(i, i + size), radix);
    if (size < 8) {
      var power = I_fromNumber(Math.pow(radix, size));
      result = I_add(I_mul(result, power), I_fromNumber(value));
    } else {
      result = I_mul(result, radixToPower);
      result = I_add(result, I_fromNumber(value));
    }
  }
  return result;
};


Integer.TWO_PWR_32_DBL_ = (1 << 16) * (1 << 16);
Integer.ZERO = I_fromInt(0);
Integer.ONE = I_fromInt(1);
Integer.TWO_PWR_24_ = I_fromInt(1 << 24);

var I_toInt = function(self) {
  return self.bits_.length > 0 ? self.bits_[0] : self.sign_;
};

var I_toWord = function(self) {
  return I_toInt(self) >>> 0;
};

var I_toNumber = function(self) {
  if (isNegative(self)) {
    return -I_toNumber(I_negate(self));
  } else {
    var val = 0;
    var pow = 1;
    for (var i = 0; i < self.bits_.length; i++) {
      val += I_getBitsUnsigned(self, i) * pow;
      pow *= Integer.TWO_PWR_32_DBL_;
    }
    return val;
  }
};

var I_getBits = function(self, index) {
  if (index < 0) {
    return 0;
  } else if (index < self.bits_.length) {
    return self.bits_[index];
  } else {
    return self.sign_;
  }
};

var I_getBitsUnsigned = function(self, index) {
  var val = I_getBits(self, index);
  return val >= 0 ? val : Integer.TWO_PWR_32_DBL_ + val;
};

var getSign = function(self) {
  return self.sign_;
};

var isZero = function(self) {
  if (self.sign_ != 0) {
    return false;
  }
  for (var i = 0; i < self.bits_.length; i++) {
    if (self.bits_[i] != 0) {
      return false;
    }
  }
  return true;
};

var isNegative = function(self) {
  return self.sign_ == -1;
};

var isOdd = function(self) {
  return (self.bits_.length == 0) && (self.sign_ == -1) ||
         (self.bits_.length > 0) && ((self.bits_[0] & 1) != 0);
};

var I_equals = function(self, other) {
  if (self.sign_ != other.sign_) {
    return false;
  }
  var len = Math.max(self.bits_.length, other.bits_.length);
  for (var i = 0; i < len; i++) {
    if (I_getBits(self, i) != I_getBits(other, i)) {
      return false;
    }
  }
  return true;
};

var I_notEquals = function(self, other) {
  return !I_equals(self, other);
};

var I_greaterThan = function(self, other) {
  return I_compare(self, other) > 0;
};

var I_greaterThanOrEqual = function(self, other) {
  return I_compare(self, other) >= 0;
};

var I_lessThan = function(self, other) {
  return I_compare(self, other) < 0;
};

var I_lessThanOrEqual = function(self, other) {
  return I_compare(self, other) <= 0;
};

var I_compare = function(self, other) {
  var diff = I_sub(self, other);
  if (isNegative(diff)) {
    return -1;
  } else if (isZero(diff)) {
    return 0;
  } else {
    return +1;
  }
};

var I_compareInt = function(self, other) {
  return I_compare(self, I_fromInt(other));
}

var shorten = function(self, numBits) {
  var arr_index = (numBits - 1) >> 5;
  var bit_index = (numBits - 1) % 32;
  var bits = [];
  for (var i = 0; i < arr_index; i++) {
    bits[i] = I_getBits(self, i);
  }
  var sigBits = bit_index == 31 ? 0xFFFFFFFF : (1 << (bit_index + 1)) - 1;
  var val = I_getBits(self, arr_index) & sigBits;
  if (val & (1 << bit_index)) {
    val |= 0xFFFFFFFF - sigBits;
    bits[arr_index] = val;
    return new Integer(bits, -1);
  } else {
    bits[arr_index] = val;
    return new Integer(bits, 0);
  }
};

var I_negate = function(self) {
  return I_add(not(self), Integer.ONE);
};

var I_add = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  var carry = 0;

  for (var i = 0; i <= len; i++) {
    var a1 = I_getBits(self, i) >>> 16;
    var a0 = I_getBits(self, i) & 0xFFFF;

    var b1 = I_getBits(other, i) >>> 16;
    var b0 = I_getBits(other, i) & 0xFFFF;

    var c0 = carry + a0 + b0;
    var c1 = (c0 >>> 16) + a1 + b1;
    carry = c1 >>> 16;
    c0 &= 0xFFFF;
    c1 &= 0xFFFF;
    arr[i] = (c1 << 16) | c0;
  }
  return I_fromBits(arr);
};

var I_sub = function(self, other) {
  return I_add(self, I_negate(other));
};

var I_mul = function(self, other) {
  if (isZero(self)) {
    return Integer.ZERO;
  } else if (isZero(other)) {
    return Integer.ZERO;
  }

  if (isNegative(self)) {
    if (isNegative(other)) {
      return I_mul(I_negate(self), I_negate(other));
    } else {
      return I_negate(I_mul(I_negate(self), other));
    }
  } else if (isNegative(other)) {
    return I_negate(I_mul(self, I_negate(other)));
  }

  if (I_lessThan(self, Integer.TWO_PWR_24_) &&
      I_lessThan(other, Integer.TWO_PWR_24_)) {
    return I_fromNumber(I_toNumber(self) * I_toNumber(other));
  }

  var len = self.bits_.length + other.bits_.length;
  var arr = [];
  for (var i = 0; i < 2 * len; i++) {
    arr[i] = 0;
  }
  for (var i = 0; i < self.bits_.length; i++) {
    for (var j = 0; j < other.bits_.length; j++) {
      var a1 = I_getBits(self, i) >>> 16;
      var a0 = I_getBits(self, i) & 0xFFFF;

      var b1 = I_getBits(other, j) >>> 16;
      var b0 = I_getBits(other, j) & 0xFFFF;

      arr[2 * i + 2 * j] += a0 * b0;
      Integer.carry16_(arr, 2 * i + 2 * j);
      arr[2 * i + 2 * j + 1] += a1 * b0;
      Integer.carry16_(arr, 2 * i + 2 * j + 1);
      arr[2 * i + 2 * j + 1] += a0 * b1;
      Integer.carry16_(arr, 2 * i + 2 * j + 1);
      arr[2 * i + 2 * j + 2] += a1 * b1;
      Integer.carry16_(arr, 2 * i + 2 * j + 2);
    }
  }

  for (var i = 0; i < len; i++) {
    arr[i] = (arr[2 * i + 1] << 16) | arr[2 * i];
  }
  for (var i = len; i < 2 * len; i++) {
    arr[i] = 0;
  }
  return new Integer(arr, 0);
};

Integer.carry16_ = function(bits, index) {
  while ((bits[index] & 0xFFFF) != bits[index]) {
    bits[index + 1] += bits[index] >>> 16;
    bits[index] &= 0xFFFF;
  }
};

var I_mod = function(self, other) {
  return I_rem(I_add(other, I_rem(self, other)), other);
}

var I_div = function(self, other) {
  if(I_greaterThan(self, Integer.ZERO) != I_greaterThan(other, Integer.ZERO)) {
    if(I_rem(self, other) != Integer.ZERO) {
      return I_sub(I_quot(self, other), Integer.ONE);
    }
  }
  return I_quot(self, other);
}

var I_quotRem = function(self, other) {
  return [0, I_quot(self, other), I_rem(self, other)];
}

var I_divMod = function(self, other) {
  return [0, I_div(self, other), I_mod(self, other)];
}

var I_quot = function(self, other) {
  if (isZero(other)) {
    throw Error('division by zero');
  } else if (isZero(self)) {
    return Integer.ZERO;
  }

  if (isNegative(self)) {
    if (isNegative(other)) {
      return I_quot(I_negate(self), I_negate(other));
    } else {
      return I_negate(I_quot(I_negate(self), other));
    }
  } else if (isNegative(other)) {
    return I_negate(I_quot(self, I_negate(other)));
  }

  var res = Integer.ZERO;
  var rem = self;
  while (I_greaterThanOrEqual(rem, other)) {
    var approx = Math.max(1, Math.floor(I_toNumber(rem) / I_toNumber(other)));
    var log2 = Math.ceil(Math.log(approx) / Math.LN2);
    var delta = (log2 <= 48) ? 1 : Math.pow(2, log2 - 48);
    var approxRes = I_fromNumber(approx);
    var approxRem = I_mul(approxRes, other);
    while (isNegative(approxRem) || I_greaterThan(approxRem, rem)) {
      approx -= delta;
      approxRes = I_fromNumber(approx);
      approxRem = I_mul(approxRes, other);
    }

    if (isZero(approxRes)) {
      approxRes = Integer.ONE;
    }

    res = I_add(res, approxRes);
    rem = I_sub(rem, approxRem);
  }
  return res;
};

var I_rem = function(self, other) {
  return I_sub(self, I_mul(I_quot(self, other), other));
};

var not = function(self) {
  var len = self.bits_.length;
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = ~self.bits_[i];
  }
  return new Integer(arr, ~self.sign_);
};

var I_and = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = I_getBits(self, i) & I_getBits(other, i);
  }
  return new Integer(arr, self.sign_ & other.sign_);
};

var I_or = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = I_getBits(self, i) | I_getBits(other, i);
  }
  return new Integer(arr, self.sign_ | other.sign_);
};

var I_xor = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = I_getBits(self, i) ^ I_getBits(other, i);
  }
  return new Integer(arr, self.sign_ ^ other.sign_);
};

var I_shiftLeft = function(self, numBits) {
  var arr_delta = numBits >> 5;
  var bit_delta = numBits % 32;
  var len = self.bits_.length + arr_delta + (bit_delta > 0 ? 1 : 0);
  var arr = [];
  for (var i = 0; i < len; i++) {
    if (bit_delta > 0) {
      arr[i] = (I_getBits(self, i - arr_delta) << bit_delta) |
               (I_getBits(self, i - arr_delta - 1) >>> (32 - bit_delta));
    } else {
      arr[i] = I_getBits(self, i - arr_delta);
    }
  }
  return new Integer(arr, self.sign_);
};

var I_shiftRight = function(self, numBits) {
  var arr_delta = numBits >> 5;
  var bit_delta = numBits % 32;
  var len = self.bits_.length - arr_delta;
  var arr = [];
  for (var i = 0; i < len; i++) {
    if (bit_delta > 0) {
      arr[i] = (I_getBits(self, i + arr_delta) >>> bit_delta) |
               (I_getBits(self, i + arr_delta + 1) << (32 - bit_delta));
    } else {
      arr[i] = I_getBits(self, i + arr_delta);
    }
  }
  return new Integer(arr, self.sign_);
};

var I_signum = function(self) {
  var cmp = I_compare(self, Integer.ZERO);
  if(cmp > 0) {
    return Integer.ONE
  }
  if(cmp < 0) {
    return I_sub(Integer.ZERO, Integer.ONE);
  }
  return Integer.ZERO;
};

var I_abs = function(self) {
  if(I_compare(self, Integer.ZERO) < 0) {
    return I_sub(Integer.ZERO, self);
  }
  return self;
};

var I_decodeDouble = function(x) {
  var dec = decodeDouble(x);
  var mantissa = I_fromBits([dec[3], dec[2]]);
  if(dec[1] < 0) {
    mantissa = I_negate(mantissa);
  }
  return [0, dec[4], mantissa];
}

var I_toString = function(self) {
  var radix = 10;

  if (isZero(self)) {
    return '0';
  } else if (isNegative(self)) {
    return '-' + I_toString(I_negate(self));
  }

  var radixToPower = I_fromNumber(Math.pow(radix, 6));

  var rem = self;
  var result = '';
  while (true) {
    var remDiv = I_div(rem, radixToPower);
    var intval = I_toInt(I_sub(rem, I_mul(remDiv, radixToPower)));
    var digits = intval.toString();

    rem = remDiv;
    if (isZero(rem)) {
      return digits + result;
    } else {
      while (digits.length < 6) {
        digits = '0' + digits;
      }
      result = '' + digits + result;
    }
  }
};

var I_fromRat = function(a, b) {
    return I_toNumber(a) / I_toNumber(b);
}

function I_fromInt64(x) {
    return I_fromBits([x.getLowBits(), x.getHighBits()]);
}

function I_toInt64(x) {
    return Long.fromBits(I_getBits(x, 0), I_getBits(x, 1));
}

function I_fromWord64(x) {
    return x;
}

function I_toWord64(x) {
    return I_rem(I_add(__w64_max, x), __w64_max);
}

// Copyright 2009 The Closure Library Authors. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS-IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

var Long = function(low, high) {
  this.low_ = low | 0;
  this.high_ = high | 0;
};

Long.IntCache_ = {};

Long.fromInt = function(value) {
  if (-128 <= value && value < 128) {
    var cachedObj = Long.IntCache_[value];
    if (cachedObj) {
      return cachedObj;
    }
  }

  var obj = new Long(value | 0, value < 0 ? -1 : 0);
  if (-128 <= value && value < 128) {
    Long.IntCache_[value] = obj;
  }
  return obj;
};

Long.fromNumber = function(value) {
  if (isNaN(value) || !isFinite(value)) {
    return Long.ZERO;
  } else if (value <= -Long.TWO_PWR_63_DBL_) {
    return Long.MIN_VALUE;
  } else if (value + 1 >= Long.TWO_PWR_63_DBL_) {
    return Long.MAX_VALUE;
  } else if (value < 0) {
    return Long.fromNumber(-value).negate();
  } else {
    return new Long(
        (value % Long.TWO_PWR_32_DBL_) | 0,
        (value / Long.TWO_PWR_32_DBL_) | 0);
  }
};

Long.fromBits = function(lowBits, highBits) {
  return new Long(lowBits, highBits);
};

Long.TWO_PWR_16_DBL_ = 1 << 16;
Long.TWO_PWR_24_DBL_ = 1 << 24;
Long.TWO_PWR_32_DBL_ =
    Long.TWO_PWR_16_DBL_ * Long.TWO_PWR_16_DBL_;
Long.TWO_PWR_31_DBL_ =
    Long.TWO_PWR_32_DBL_ / 2;
Long.TWO_PWR_48_DBL_ =
    Long.TWO_PWR_32_DBL_ * Long.TWO_PWR_16_DBL_;
Long.TWO_PWR_64_DBL_ =
    Long.TWO_PWR_32_DBL_ * Long.TWO_PWR_32_DBL_;
Long.TWO_PWR_63_DBL_ =
    Long.TWO_PWR_64_DBL_ / 2;
Long.ZERO = Long.fromInt(0);
Long.ONE = Long.fromInt(1);
Long.NEG_ONE = Long.fromInt(-1);
Long.MAX_VALUE =
    Long.fromBits(0xFFFFFFFF | 0, 0x7FFFFFFF | 0);
Long.MIN_VALUE = Long.fromBits(0, 0x80000000 | 0);
Long.TWO_PWR_24_ = Long.fromInt(1 << 24);

Long.prototype.toInt = function() {
  return this.low_;
};

Long.prototype.toNumber = function() {
  return this.high_ * Long.TWO_PWR_32_DBL_ +
         this.getLowBitsUnsigned();
};

Long.prototype.getHighBits = function() {
  return this.high_;
};

Long.prototype.getLowBits = function() {
  return this.low_;
};

Long.prototype.getLowBitsUnsigned = function() {
  return (this.low_ >= 0) ?
      this.low_ : Long.TWO_PWR_32_DBL_ + this.low_;
};

Long.prototype.isZero = function() {
  return this.high_ == 0 && this.low_ == 0;
};

Long.prototype.isNegative = function() {
  return this.high_ < 0;
};

Long.prototype.isOdd = function() {
  return (this.low_ & 1) == 1;
};

Long.prototype.equals = function(other) {
  return (this.high_ == other.high_) && (this.low_ == other.low_);
};

Long.prototype.notEquals = function(other) {
  return (this.high_ != other.high_) || (this.low_ != other.low_);
};

Long.prototype.lessThan = function(other) {
  return this.compare(other) < 0;
};

Long.prototype.lessThanOrEqual = function(other) {
  return this.compare(other) <= 0;
};

Long.prototype.greaterThan = function(other) {
  return this.compare(other) > 0;
};

Long.prototype.greaterThanOrEqual = function(other) {
  return this.compare(other) >= 0;
};

Long.prototype.compare = function(other) {
  if (this.equals(other)) {
    return 0;
  }

  var thisNeg = this.isNegative();
  var otherNeg = other.isNegative();
  if (thisNeg && !otherNeg) {
    return -1;
  }
  if (!thisNeg && otherNeg) {
    return 1;
  }

  if (this.subtract(other).isNegative()) {
    return -1;
  } else {
    return 1;
  }
};

Long.prototype.negate = function() {
  if (this.equals(Long.MIN_VALUE)) {
    return Long.MIN_VALUE;
  } else {
    return this.not().add(Long.ONE);
  }
};

Long.prototype.add = function(other) {
  var a48 = this.high_ >>> 16;
  var a32 = this.high_ & 0xFFFF;
  var a16 = this.low_ >>> 16;
  var a00 = this.low_ & 0xFFFF;

  var b48 = other.high_ >>> 16;
  var b32 = other.high_ & 0xFFFF;
  var b16 = other.low_ >>> 16;
  var b00 = other.low_ & 0xFFFF;

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
  return Long.fromBits((c16 << 16) | c00, (c48 << 16) | c32);
};

Long.prototype.subtract = function(other) {
  return this.add(other.negate());
};

Long.prototype.multiply = function(other) {
  if (this.isZero()) {
    return Long.ZERO;
  } else if (other.isZero()) {
    return Long.ZERO;
  }

  if (this.equals(Long.MIN_VALUE)) {
    return other.isOdd() ? Long.MIN_VALUE : Long.ZERO;
  } else if (other.equals(Long.MIN_VALUE)) {
    return this.isOdd() ? Long.MIN_VALUE : Long.ZERO;
  }

  if (this.isNegative()) {
    if (other.isNegative()) {
      return this.negate().multiply(other.negate());
    } else {
      return this.negate().multiply(other).negate();
    }
  } else if (other.isNegative()) {
    return this.multiply(other.negate()).negate();
  }

  if (this.lessThan(Long.TWO_PWR_24_) &&
      other.lessThan(Long.TWO_PWR_24_)) {
    return Long.fromNumber(this.toNumber() * other.toNumber());
  }

  var a48 = this.high_ >>> 16;
  var a32 = this.high_ & 0xFFFF;
  var a16 = this.low_ >>> 16;
  var a00 = this.low_ & 0xFFFF;

  var b48 = other.high_ >>> 16;
  var b32 = other.high_ & 0xFFFF;
  var b16 = other.low_ >>> 16;
  var b00 = other.low_ & 0xFFFF;

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
  return Long.fromBits((c16 << 16) | c00, (c48 << 16) | c32);
};

Long.prototype.div = function(other) {
  if (other.isZero()) {
    throw Error('division by zero');
  } else if (this.isZero()) {
    return Long.ZERO;
  }

  if (this.equals(Long.MIN_VALUE)) {
    if (other.equals(Long.ONE) ||
        other.equals(Long.NEG_ONE)) {
      return Long.MIN_VALUE;
    } else if (other.equals(Long.MIN_VALUE)) {
      return Long.ONE;
    } else {
      var halfThis = this.shiftRight(1);
      var approx = halfThis.div(other).shiftLeft(1);
      if (approx.equals(Long.ZERO)) {
        return other.isNegative() ? Long.ONE : Long.NEG_ONE;
      } else {
        var rem = this.subtract(other.multiply(approx));
        var result = approx.add(rem.div(other));
        return result;
      }
    }
  } else if (other.equals(Long.MIN_VALUE)) {
    return Long.ZERO;
  }

  if (this.isNegative()) {
    if (other.isNegative()) {
      return this.negate().div(other.negate());
    } else {
      return this.negate().div(other).negate();
    }
  } else if (other.isNegative()) {
    return this.div(other.negate()).negate();
  }

  var res = Long.ZERO;
  var rem = this;
  while (rem.greaterThanOrEqual(other)) {
    var approx = Math.max(1, Math.floor(rem.toNumber() / other.toNumber()));

    var log2 = Math.ceil(Math.log(approx) / Math.LN2);
    var delta = (log2 <= 48) ? 1 : Math.pow(2, log2 - 48);

    var approxRes = Long.fromNumber(approx);
    var approxRem = approxRes.multiply(other);
    while (approxRem.isNegative() || approxRem.greaterThan(rem)) {
      approx -= delta;
      approxRes = Long.fromNumber(approx);
      approxRem = approxRes.multiply(other);
    }

    if (approxRes.isZero()) {
      approxRes = Long.ONE;
    }

    res = res.add(approxRes);
    rem = rem.subtract(approxRem);
  }
  return res;
};

Long.prototype.modulo = function(other) {
  return this.subtract(this.div(other).multiply(other));
};

Long.prototype.not = function() {
  return Long.fromBits(~this.low_, ~this.high_);
};

Long.prototype.and = function(other) {
  return Long.fromBits(this.low_ & other.low_,
                                 this.high_ & other.high_);
};

Long.prototype.or = function(other) {
  return Long.fromBits(this.low_ | other.low_,
                                 this.high_ | other.high_);
};

Long.prototype.xor = function(other) {
  return Long.fromBits(this.low_ ^ other.low_,
                                 this.high_ ^ other.high_);
};

Long.prototype.shiftLeft = function(numBits) {
  numBits &= 63;
  if (numBits == 0) {
    return this;
  } else {
    var low = this.low_;
    if (numBits < 32) {
      var high = this.high_;
      return Long.fromBits(
          low << numBits,
          (high << numBits) | (low >>> (32 - numBits)));
    } else {
      return Long.fromBits(0, low << (numBits - 32));
    }
  }
};

Long.prototype.shiftRight = function(numBits) {
  numBits &= 63;
  if (numBits == 0) {
    return this;
  } else {
    var high = this.high_;
    if (numBits < 32) {
      var low = this.low_;
      return Long.fromBits(
          (low >>> numBits) | (high << (32 - numBits)),
          high >> numBits);
    } else {
      return Long.fromBits(
          high >> (numBits - 32),
          high >= 0 ? 0 : -1);
    }
  }
};

Long.prototype.shiftRightUnsigned = function(numBits) {
  numBits &= 63;
  if (numBits == 0) {
    return this;
  } else {
    var high = this.high_;
    if (numBits < 32) {
      var low = this.low_;
      return Long.fromBits(
          (low >>> numBits) | (high << (32 - numBits)),
          high >>> numBits);
    } else if (numBits == 32) {
      return Long.fromBits(high, 0);
    } else {
      return Long.fromBits(high >>> (numBits - 32), 0);
    }
  }
};



// Int64
function hs_eqInt64(x, y) {return x.equals(y);}
function hs_neInt64(x, y) {return !x.equals(y);}
function hs_ltInt64(x, y) {return x.compare(y) < 0;}
function hs_leInt64(x, y) {return x.compare(y) <= 0;}
function hs_gtInt64(x, y) {return x.compare(y) > 0;}
function hs_geInt64(x, y) {return x.compare(y) >= 0;}
function hs_quotInt64(x, y) {return x.div(y);}
function hs_remInt64(x, y) {return x.modulo(y);}
function hs_plusInt64(x, y) {return x.add(y);}
function hs_minusInt64(x, y) {return x.subtract(y);}
function hs_timesInt64(x, y) {return x.multiply(y);}
function hs_negateInt64(x) {return x.negate();}
function hs_uncheckedIShiftL64(x, bits) {return x.shiftLeft(bits);}
function hs_uncheckedIShiftRA64(x, bits) {return x.shiftRight(bits);}
function hs_uncheckedIShiftRL64(x, bits) {return x.shiftRightUnsigned(bits);}
function hs_intToInt64(x) {return new Long(x, 0);}
function hs_int64ToInt(x) {return x.toInt();}



// Word64
function hs_wordToWord64(x) {
    return I_fromInt(x);
}
function hs_word64ToWord(x) {
    return I_toInt(x);
}
function hs_mkWord64(low, high) {
    return I_fromBits([low, high]);
}

var hs_and64 = I_and;
var hs_or64 = I_or;
var hs_xor64 = I_xor;
var __i64_all_ones = I_fromBits([0xffffffff, 0xffffffff]);
function hs_not64(x) {
    return I_xor(x, __i64_all_ones);
}
var hs_eqWord64 = I_equals;
var hs_neWord64 = I_notEquals;
var hs_ltWord64 = I_lessThan;
var hs_leWord64 = I_lessThanOrEqual;
var hs_gtWord64 = I_greaterThan;
var hs_geWord64 = I_greaterThanOrEqual;
var hs_quotWord64 = I_quot;
var hs_remWord64 = I_rem;
var __w64_max = I_fromBits([0,0,1]);
function hs_uncheckedShiftL64(x, bits) {
    return I_rem(I_shiftLeft(x, bits), __w64_max);
}
var hs_uncheckedShiftRL64 = I_shiftRight;
function hs_int64ToWord64(x) {
    var tmp = I_add(__w64_max, I_fromBits([x.getLowBits(), x.getHighBits()]));
    return I_rem(tmp, __w64_max);
}
function hs_word64ToInt64(x) {
    return Long.fromBits(I_getBits(x, 0), I_getBits(x, 1));
}

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
    var arr = {};
    var buffer = new ArrayBuffer(n);
    var views = {};
    views['i8']  = new Int8Array(buffer);
    views['i16'] = new Int16Array(buffer);
    views['i32'] = new Int32Array(buffer);
    views['w8']  = new Uint8Array(buffer);
    views['w16'] = new Uint16Array(buffer);
    views['w32'] = new Uint32Array(buffer);
    views['f32'] = new Float32Array(buffer);
    views['f64'] = new Float64Array(buffer);
    arr['b'] = buffer;
    arr['v'] = views;
    // ByteArray and Addr are the same thing, so keep an offset if we get
    // casted.
    arr['off'] = 0;
    return arr;
}
window['newByteArr'] = newByteArr;

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

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
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
    return [0, 1, E(w).val];
}

function finalizeWeak(w) {
    return [0, B(A(E(w).fin, [0]))];
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
    for(; as[0] === 1; as = as[2]) {
        arr.push(as[1]);
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
        return [0];
    }
    return [1, arr[elem],new T(function(){return __arr2lst(elem+1,arr);})]
}

function __lst2arr(xs) {
    var arr = [];
    xs = E(xs);
    for(;xs[0] === 1; xs = E(xs[2])) {
        arr.push(E(xs[1]));
    }
    return arr;
}

var __new = function() {return ({});}
var __set = function(o,k,v) {o[k]=v;}
var __get = function(o,k) {return o[k];}
var __has = function(o,k) {return o[k]!==undefined;}

var _0=[0,_],_1="deltaZ",_2="deltaY",_3="deltaX",_4=function(_5,_6){var _7=E(_5);return (_7[0]==0)?E(_6):[1,_7[1],new T(function(){return B(_4(_7[2],_6));})];},_8=function(_9,_a){var _b=jsShowI(_9);return new F(function(){return _4(fromJSStr(_b),_a);});},_c=41,_d=40,_e=function(_f,_g,_h){if(_g>=0){return new F(function(){return _8(_g,_h);});}else{if(_f<=6){return new F(function(){return _8(_g,_h);});}else{return [1,_d,new T(function(){var _i=jsShowI(_g);return B(_4(fromJSStr(_i),[1,_c,_h]));})];}}},_j=new T(function(){return B(unCStr(")"));}),_k=new T(function(){return B(_e(0,2,_j));}),_l=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_k));}),_m=function(_n){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_e(0,_n,_l));}))));});},_o=function(_p,_){return new T(function(){var _q=Number(E(_p)),_r=jsTrunc(_q);if(_r<0){return B(_m(_r));}else{if(_r>2){return B(_m(_r));}else{return _r;}}});},_s=0,_t=[0,_s,_s,_s],_u="button",_v=new T(function(){return jsGetMouseCoords;}),_w=[0],_x=function(_y,_){var _z=E(_y);if(!_z[0]){return _w;}else{var _A=B(_x(_z[2],_));return [1,new T(function(){var _B=Number(E(_z[1]));return jsTrunc(_B);}),_A];}},_C=function(_D,_){var _E=__arr2lst(0,_D);return new F(function(){return _x(_E,_);});},_F=function(_G,_){return new F(function(){return _C(E(_G),_);});},_H=function(_I,_){return new T(function(){var _J=Number(E(_I));return jsTrunc(_J);});},_K=[0,_H,_F],_L=function(_M,_){var _N=E(_M);if(!_N[0]){return _w;}else{var _O=B(_L(_N[2],_));return [1,_N[1],_O];}},_P=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_Q=new T(function(){return B(unCStr("base"));}),_R=new T(function(){return B(unCStr("IOException"));}),_S=new T(function(){var _T=hs_wordToWord64(4053623282),_U=hs_wordToWord64(3693590983);return [0,_T,_U,[0,_T,_U,_Q,_P,_R],_w,_w];}),_V=function(_W){return E(_S);},_X=function(_Y){return E(E(_Y)[1]);},_Z=function(_10,_11,_12){var _13=B(A(_10,[_])),_14=B(A(_11,[_])),_15=hs_eqWord64(_13[1],_14[1]);if(!_15){return [0];}else{var _16=hs_eqWord64(_13[2],_14[2]);return (!_16)?[0]:[1,_12];}},_17=function(_18){var _19=E(_18);return new F(function(){return _Z(B(_X(_19[1])),_V,_19[2]);});},_1a=new T(function(){return B(unCStr(": "));}),_1b=new T(function(){return B(unCStr(")"));}),_1c=new T(function(){return B(unCStr(" ("));}),_1d=new T(function(){return B(unCStr("interrupted"));}),_1e=new T(function(){return B(unCStr("system error"));}),_1f=new T(function(){return B(unCStr("unsatisified constraints"));}),_1g=new T(function(){return B(unCStr("user error"));}),_1h=new T(function(){return B(unCStr("permission denied"));}),_1i=new T(function(){return B(unCStr("illegal operation"));}),_1j=new T(function(){return B(unCStr("end of file"));}),_1k=new T(function(){return B(unCStr("resource exhausted"));}),_1l=new T(function(){return B(unCStr("resource busy"));}),_1m=new T(function(){return B(unCStr("does not exist"));}),_1n=new T(function(){return B(unCStr("already exists"));}),_1o=new T(function(){return B(unCStr("resource vanished"));}),_1p=new T(function(){return B(unCStr("timeout"));}),_1q=new T(function(){return B(unCStr("unsupported operation"));}),_1r=new T(function(){return B(unCStr("hardware fault"));}),_1s=new T(function(){return B(unCStr("inappropriate type"));}),_1t=new T(function(){return B(unCStr("invalid argument"));}),_1u=new T(function(){return B(unCStr("failed"));}),_1v=new T(function(){return B(unCStr("protocol error"));}),_1w=function(_1x,_1y){switch(E(_1x)){case 0:return new F(function(){return _4(_1n,_1y);});break;case 1:return new F(function(){return _4(_1m,_1y);});break;case 2:return new F(function(){return _4(_1l,_1y);});break;case 3:return new F(function(){return _4(_1k,_1y);});break;case 4:return new F(function(){return _4(_1j,_1y);});break;case 5:return new F(function(){return _4(_1i,_1y);});break;case 6:return new F(function(){return _4(_1h,_1y);});break;case 7:return new F(function(){return _4(_1g,_1y);});break;case 8:return new F(function(){return _4(_1f,_1y);});break;case 9:return new F(function(){return _4(_1e,_1y);});break;case 10:return new F(function(){return _4(_1v,_1y);});break;case 11:return new F(function(){return _4(_1u,_1y);});break;case 12:return new F(function(){return _4(_1t,_1y);});break;case 13:return new F(function(){return _4(_1s,_1y);});break;case 14:return new F(function(){return _4(_1r,_1y);});break;case 15:return new F(function(){return _4(_1q,_1y);});break;case 16:return new F(function(){return _4(_1p,_1y);});break;case 17:return new F(function(){return _4(_1o,_1y);});break;default:return new F(function(){return _4(_1d,_1y);});}},_1z=new T(function(){return B(unCStr("}"));}),_1A=new T(function(){return B(unCStr("{handle: "));}),_1B=function(_1C,_1D,_1E,_1F,_1G,_1H){var _1I=new T(function(){var _1J=new T(function(){var _1K=new T(function(){var _1L=E(_1F);if(!_1L[0]){return E(_1H);}else{var _1M=new T(function(){return B(_4(_1L,new T(function(){return B(_4(_1b,_1H));},1)));},1);return B(_4(_1c,_1M));}},1);return B(_1w(_1D,_1K));}),_1N=E(_1E);if(!_1N[0]){return E(_1J);}else{return B(_4(_1N,new T(function(){return B(_4(_1a,_1J));},1)));}}),_1O=E(_1G);if(!_1O[0]){var _1P=E(_1C);if(!_1P[0]){return E(_1I);}else{var _1Q=E(_1P[1]);if(!_1Q[0]){var _1R=new T(function(){var _1S=new T(function(){return B(_4(_1z,new T(function(){return B(_4(_1a,_1I));},1)));},1);return B(_4(_1Q[1],_1S));},1);return new F(function(){return _4(_1A,_1R);});}else{var _1T=new T(function(){var _1U=new T(function(){return B(_4(_1z,new T(function(){return B(_4(_1a,_1I));},1)));},1);return B(_4(_1Q[1],_1U));},1);return new F(function(){return _4(_1A,_1T);});}}}else{return new F(function(){return _4(_1O[1],new T(function(){return B(_4(_1a,_1I));},1));});}},_1V=function(_1W){var _1X=E(_1W);return new F(function(){return _1B(_1X[1],_1X[2],_1X[3],_1X[4],_1X[6],_w);});},_1Y=function(_1Z,_20,_21){var _22=E(_20);return new F(function(){return _1B(_22[1],_22[2],_22[3],_22[4],_22[6],_21);});},_23=function(_24,_25){var _26=E(_24);return new F(function(){return _1B(_26[1],_26[2],_26[3],_26[4],_26[6],_25);});},_27=44,_28=93,_29=91,_2a=function(_2b,_2c,_2d){var _2e=E(_2c);if(!_2e[0]){return new F(function(){return unAppCStr("[]",_2d);});}else{var _2f=new T(function(){var _2g=new T(function(){var _2h=function(_2i){var _2j=E(_2i);if(!_2j[0]){return [1,_28,_2d];}else{var _2k=new T(function(){return B(A(_2b,[_2j[1],new T(function(){return B(_2h(_2j[2]));})]));});return [1,_27,_2k];}};return B(_2h(_2e[2]));});return B(A(_2b,[_2e[1],_2g]));});return [1,_29,_2f];}},_2l=function(_2m,_2n){return new F(function(){return _2a(_23,_2m,_2n);});},_2o=[0,_1Y,_1V,_2l],_2p=new T(function(){return [0,_V,_2o,_2q,_17,_1V];}),_2q=function(_2r){return [0,_2p,_2r];},_2s=[0],_2t=7,_2u=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:272:5-9"));}),_2v=[0,_2s,_2t,_w,_2u,_2s,_2s],_2w=new T(function(){return B(_2q(_2v));}),_2x=function(_){return new F(function(){return die(_2w);});},_2y=function(_2z){return E(E(_2z)[1]);},_2A=function(_2B,_2C,_2D,_){var _2E=__arr2lst(0,_2D),_2F=B(_L(_2E,_)),_2G=E(_2F);if(!_2G[0]){return new F(function(){return _2x(_);});}else{var _2H=E(_2G[2]);if(!_2H[0]){return new F(function(){return _2x(_);});}else{if(!E(_2H[2])[0]){var _2I=B(A(_2y,[_2B,_2G[1],_])),_2J=B(A(_2y,[_2C,_2H[1],_]));return [0,_2I,_2J];}else{return new F(function(){return _2x(_);});}}}},_2K=function(_){return new F(function(){return __jsNull();});},_2L=function(_2M){var _2N=B(A(_2M,[_]));return E(_2N);},_2O=new T(function(){return B(_2L(_2K));}),_2P=new T(function(){return E(_2O);}),_2Q=function(_2R,_2S,_){if(E(_2R)==7){var _2T=E(_v)(_2S),_2U=B(_2A(_K,_K,_2T,_)),_2V=_2S[E(_3)],_2W=_2S[E(_2)],_2X=_2S[E(_1)];return new T(function(){return [0,E(_2U),E(_2s),[0,_2V,_2W,_2X]];});}else{var _2Y=E(_v)(_2S),_2Z=B(_2A(_K,_K,_2Y,_)),_30=_2S[E(_u)],_31=__eq(_30,E(_2P));if(!E(_31)){var _32=B(_o(_30,_));return new T(function(){return [0,E(_2Z),[1,_32],E(_t)];});}else{return new T(function(){return [0,E(_2Z),E(_2s),E(_t)];});}}},_33=function(_34,_35,_){return new F(function(){return _2Q(_34,E(_35),_);});},_36="mouseout",_37="mouseover",_38="mousemove",_39="mouseup",_3a="mousedown",_3b="dblclick",_3c="click",_3d="wheel",_3e=function(_3f){switch(E(_3f)){case 0:return E(_3c);case 1:return E(_3b);case 2:return E(_3a);case 3:return E(_39);case 4:return E(_38);case 5:return E(_37);case 6:return E(_36);default:return E(_3d);}},_3g=[0,_3e,_33],_3h=[1,I_fromBits([3567587328,232])],_3i=function(_3j){return E(_3h);},_3k=function(_3l,_){return [1,_3l];},_3m=function(_3n){return E(_3n);},_3o=[0,_3m,_3k],_3p=function(_3q,_3r,_){var _3s=B(A(_3q,[_])),_3t=B(A(_3r,[_]));return _3s;},_3u=function(_3v,_3w,_){var _3x=B(A(_3v,[_])),_3y=B(A(_3w,[_]));return new T(function(){return B(A(_3x,[_3y]));});},_3z=function(_3A,_3B,_){var _3C=B(A(_3B,[_]));return _3A;},_3D=function(_3E,_3F,_){var _3G=B(A(_3F,[_]));return new T(function(){return B(A(_3E,[_3G]));});},_3H=[0,_3D,_3z],_3I=function(_3J,_){return _3J;},_3K=function(_3L,_3M,_){var _3N=B(A(_3L,[_]));return new F(function(){return A(_3M,[_]);});},_3O=[0,_3H,_3I,_3u,_3K,_3p],_3P=function(_3Q,_3R,_){var _3S=B(A(_3Q,[_]));return new F(function(){return A(_3R,[_3S,_]);});},_3T=function(_3U){return [0,_2s,_2t,_w,_3U,_2s,_2s];},_3V=function(_3W,_){var _3X=new T(function(){return B(_2q(new T(function(){return B(_3T(_3W));})));});return new F(function(){return die(_3X);});},_3Y=[0,_3O,_3P,_3K,_3I,_3V],_3Z=[0,_3Y,_3m],_40=[0,_3Z,_3I],_41=function(_42,_43){while(1){var _44=E(_42);if(!_44[0]){return (E(_43)[0]==0)?1:0;}else{var _45=E(_43);if(!_45[0]){return 2;}else{var _46=E(_44[1]),_47=E(_45[1]);if(_46!=_47){return (_46>_47)?2:0;}else{_42=_44[2];_43=_45[2];continue;}}}}},_48=new T(function(){return B(unCStr("Map.!: given key is not an element in the map"));}),_49=new T(function(){return B(err(_48));}),_4a=function(_4b,_4c){while(1){var _4d=E(_4c);if(!_4d[0]){switch(B(_41(_4b,_4d[2]))){case 0:_4c=_4d[4];continue;case 1:return E(_4d[3]);default:_4c=_4d[5];continue;}}else{return E(_49);}}},_4e=[1],_4f=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_4g=function(_4h){return new F(function(){return err(_4f);});},_4i=new T(function(){return B(_4g(_));}),_4j=function(_4k,_4l,_4m,_4n){var _4o=E(_4n);if(!_4o[0]){var _4p=_4o[1],_4q=E(_4m);if(!_4q[0]){var _4r=_4q[1],_4s=_4q[2],_4t=_4q[3];if(_4r<=(imul(3,_4p)|0)){return [0,(1+_4r|0)+_4p|0,E(_4k),_4l,E(_4q),E(_4o)];}else{var _4u=E(_4q[4]);if(!_4u[0]){var _4v=_4u[1],_4w=E(_4q[5]);if(!_4w[0]){var _4x=_4w[1],_4y=_4w[2],_4z=_4w[3],_4A=_4w[4];if(_4x>=(imul(2,_4v)|0)){var _4B=function(_4C){var _4D=E(_4w[5]);return (_4D[0]==0)?[0,(1+_4r|0)+_4p|0,E(_4y),_4z,[0,(1+_4v|0)+_4C|0,E(_4s),_4t,E(_4u),E(_4A)],[0,(1+_4p|0)+_4D[1]|0,E(_4k),_4l,E(_4D),E(_4o)]]:[0,(1+_4r|0)+_4p|0,E(_4y),_4z,[0,(1+_4v|0)+_4C|0,E(_4s),_4t,E(_4u),E(_4A)],[0,1+_4p|0,E(_4k),_4l,E(_4e),E(_4o)]];},_4E=E(_4A);if(!_4E[0]){return new F(function(){return _4B(_4E[1]);});}else{return new F(function(){return _4B(0);});}}else{return [0,(1+_4r|0)+_4p|0,E(_4s),_4t,E(_4u),[0,(1+_4p|0)+_4x|0,E(_4k),_4l,E(_4w),E(_4o)]];}}else{return E(_4i);}}else{return E(_4i);}}}else{return [0,1+_4p|0,E(_4k),_4l,E(_4e),E(_4o)];}}else{var _4F=E(_4m);if(!_4F[0]){var _4G=_4F[1],_4H=_4F[2],_4I=_4F[3],_4J=_4F[5],_4K=E(_4F[4]);if(!_4K[0]){var _4L=_4K[1],_4M=E(_4J);if(!_4M[0]){var _4N=_4M[1],_4O=_4M[2],_4P=_4M[3],_4Q=_4M[4];if(_4N>=(imul(2,_4L)|0)){var _4R=function(_4S){var _4T=E(_4M[5]);return (_4T[0]==0)?[0,1+_4G|0,E(_4O),_4P,[0,(1+_4L|0)+_4S|0,E(_4H),_4I,E(_4K),E(_4Q)],[0,1+_4T[1]|0,E(_4k),_4l,E(_4T),E(_4e)]]:[0,1+_4G|0,E(_4O),_4P,[0,(1+_4L|0)+_4S|0,E(_4H),_4I,E(_4K),E(_4Q)],[0,1,E(_4k),_4l,E(_4e),E(_4e)]];},_4U=E(_4Q);if(!_4U[0]){return new F(function(){return _4R(_4U[1]);});}else{return new F(function(){return _4R(0);});}}else{return [0,1+_4G|0,E(_4H),_4I,E(_4K),[0,1+_4N|0,E(_4k),_4l,E(_4M),E(_4e)]];}}else{return [0,3,E(_4H),_4I,E(_4K),[0,1,E(_4k),_4l,E(_4e),E(_4e)]];}}else{var _4V=E(_4J);return (_4V[0]==0)?[0,3,E(_4V[2]),_4V[3],[0,1,E(_4H),_4I,E(_4e),E(_4e)],[0,1,E(_4k),_4l,E(_4e),E(_4e)]]:[0,2,E(_4k),_4l,E(_4F),E(_4e)];}}else{return [0,1,E(_4k),_4l,E(_4e),E(_4e)];}}},_4W=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_4X=function(_4Y){return new F(function(){return err(_4W);});},_4Z=new T(function(){return B(_4X(_));}),_50=function(_51,_52,_53,_54){var _55=E(_53);if(!_55[0]){var _56=_55[1],_57=E(_54);if(!_57[0]){var _58=_57[1],_59=_57[2],_5a=_57[3];if(_58<=(imul(3,_56)|0)){return [0,(1+_56|0)+_58|0,E(_51),_52,E(_55),E(_57)];}else{var _5b=E(_57[4]);if(!_5b[0]){var _5c=_5b[1],_5d=_5b[2],_5e=_5b[3],_5f=_5b[4],_5g=E(_57[5]);if(!_5g[0]){var _5h=_5g[1];if(_5c>=(imul(2,_5h)|0)){var _5i=function(_5j){var _5k=E(_51),_5l=E(_5b[5]);return (_5l[0]==0)?[0,(1+_56|0)+_58|0,E(_5d),_5e,[0,(1+_56|0)+_5j|0,E(_5k),_52,E(_55),E(_5f)],[0,(1+_5h|0)+_5l[1]|0,E(_59),_5a,E(_5l),E(_5g)]]:[0,(1+_56|0)+_58|0,E(_5d),_5e,[0,(1+_56|0)+_5j|0,E(_5k),_52,E(_55),E(_5f)],[0,1+_5h|0,E(_59),_5a,E(_4e),E(_5g)]];},_5m=E(_5f);if(!_5m[0]){return new F(function(){return _5i(_5m[1]);});}else{return new F(function(){return _5i(0);});}}else{return [0,(1+_56|0)+_58|0,E(_59),_5a,[0,(1+_56|0)+_5c|0,E(_51),_52,E(_55),E(_5b)],E(_5g)];}}else{return E(_4Z);}}else{return E(_4Z);}}}else{return [0,1+_56|0,E(_51),_52,E(_55),E(_4e)];}}else{var _5n=E(_54);if(!_5n[0]){var _5o=_5n[1],_5p=_5n[2],_5q=_5n[3],_5r=_5n[5],_5s=E(_5n[4]);if(!_5s[0]){var _5t=_5s[1],_5u=_5s[2],_5v=_5s[3],_5w=_5s[4],_5x=E(_5r);if(!_5x[0]){var _5y=_5x[1];if(_5t>=(imul(2,_5y)|0)){var _5z=function(_5A){var _5B=E(_51),_5C=E(_5s[5]);return (_5C[0]==0)?[0,1+_5o|0,E(_5u),_5v,[0,1+_5A|0,E(_5B),_52,E(_4e),E(_5w)],[0,(1+_5y|0)+_5C[1]|0,E(_5p),_5q,E(_5C),E(_5x)]]:[0,1+_5o|0,E(_5u),_5v,[0,1+_5A|0,E(_5B),_52,E(_4e),E(_5w)],[0,1+_5y|0,E(_5p),_5q,E(_4e),E(_5x)]];},_5D=E(_5w);if(!_5D[0]){return new F(function(){return _5z(_5D[1]);});}else{return new F(function(){return _5z(0);});}}else{return [0,1+_5o|0,E(_5p),_5q,[0,1+_5t|0,E(_51),_52,E(_4e),E(_5s)],E(_5x)];}}else{return [0,3,E(_5u),_5v,[0,1,E(_51),_52,E(_4e),E(_4e)],[0,1,E(_5p),_5q,E(_4e),E(_4e)]];}}else{var _5E=E(_5r);return (_5E[0]==0)?[0,3,E(_5p),_5q,[0,1,E(_51),_52,E(_4e),E(_4e)],E(_5E)]:[0,2,E(_51),_52,E(_4e),E(_5n)];}}else{return [0,1,E(_51),_52,E(_4e),E(_4e)];}}},_5F=function(_5G,_5H,_5I){var _5J=E(_5G),_5K=E(_5I);if(!_5K[0]){var _5L=_5K[2],_5M=_5K[3],_5N=_5K[4],_5O=_5K[5];switch(B(_41(_5J,_5L))){case 0:return new F(function(){return _4j(_5L,_5M,B(_5F(_5J,_5H,_5N)),_5O);});break;case 1:return [0,_5K[1],E(_5J),_5H,E(_5N),E(_5O)];default:return new F(function(){return _50(_5L,_5M,_5N,B(_5F(_5J,_5H,_5O)));});}}else{return [0,1,E(_5J),_5H,E(_4e),E(_4e)];}},_5P=function(_5Q,_5R){while(1){var _5S=E(_5Q),_5T=E(_5R);if(!_5T[0]){switch(B(_41(_5S,_5T[2]))){case 0:_5Q=_5S;_5R=_5T[4];continue;case 1:return true;default:_5Q=_5S;_5R=_5T[5];continue;}}else{return false;}}},_5U=[0,0],_5V=function(_5W,_5X){if(_5W<=0){if(_5W>=0){return new F(function(){return quot(_5W,_5X);});}else{if(_5X<=0){return new F(function(){return quot(_5W,_5X);});}else{return quot(_5W+1|0,_5X)-1|0;}}}else{if(_5X>=0){if(_5W>=0){return new F(function(){return quot(_5W,_5X);});}else{if(_5X<=0){return new F(function(){return quot(_5W,_5X);});}else{return quot(_5W+1|0,_5X)-1|0;}}}else{return quot(_5W-1|0,_5X)-1|0;}}},_5Y=function(_5Z,_60){while(1){var _61=E(_5Z);if(!_61[0]){var _62=E(_61[1]);if(_62==(-2147483648)){_5Z=[1,I_fromInt(-2147483648)];continue;}else{var _63=E(_60);if(!_63[0]){return [0,B(_5V(_62,_63[1]))];}else{_5Z=[1,I_fromInt(_62)];_60=_63;continue;}}}else{var _64=_61[1],_65=E(_60);return (_65[0]==0)?[1,I_div(_64,I_fromInt(_65[1]))]:[1,I_div(_64,_65[1])];}}},_66=new T(function(){return B(unCStr("GHC.Exception"));}),_67=new T(function(){return B(unCStr("base"));}),_68=new T(function(){return B(unCStr("ArithException"));}),_69=new T(function(){var _6a=hs_wordToWord64(4194982440),_6b=hs_wordToWord64(3110813675);return [0,_6a,_6b,[0,_6a,_6b,_67,_66,_68],_w,_w];}),_6c=function(_6d){return E(_69);},_6e=function(_6f){var _6g=E(_6f);return new F(function(){return _Z(B(_X(_6g[1])),_6c,_6g[2]);});},_6h=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_6i=new T(function(){return B(unCStr("denormal"));}),_6j=new T(function(){return B(unCStr("divide by zero"));}),_6k=new T(function(){return B(unCStr("loss of precision"));}),_6l=new T(function(){return B(unCStr("arithmetic underflow"));}),_6m=new T(function(){return B(unCStr("arithmetic overflow"));}),_6n=function(_6o,_6p){switch(E(_6o)){case 0:return new F(function(){return _4(_6m,_6p);});break;case 1:return new F(function(){return _4(_6l,_6p);});break;case 2:return new F(function(){return _4(_6k,_6p);});break;case 3:return new F(function(){return _4(_6j,_6p);});break;case 4:return new F(function(){return _4(_6i,_6p);});break;default:return new F(function(){return _4(_6h,_6p);});}},_6q=function(_6r){return new F(function(){return _6n(_6r,_w);});},_6s=function(_6t,_6u,_6v){return new F(function(){return _6n(_6u,_6v);});},_6w=function(_6x,_6y){return new F(function(){return _2a(_6n,_6x,_6y);});},_6z=[0,_6s,_6q,_6w],_6A=new T(function(){return [0,_6c,_6z,_6B,_6e,_6q];}),_6B=function(_6C){return [0,_6A,_6C];},_6D=3,_6E=new T(function(){return B(_6B(_6D));}),_6F=new T(function(){return die(_6E);}),_6G=function(_6H,_6I){var _6J=E(_6H);if(!_6J[0]){var _6K=_6J[1],_6L=E(_6I);return (_6L[0]==0)?_6K==_6L[1]:(I_compareInt(_6L[1],_6K)==0)?true:false;}else{var _6M=_6J[1],_6N=E(_6I);return (_6N[0]==0)?(I_compareInt(_6M,_6N[1])==0)?true:false:(I_compare(_6M,_6N[1])==0)?true:false;}},_6O=function(_6P,_6Q){while(1){var _6R=E(_6P);if(!_6R[0]){var _6S=_6R[1],_6T=E(_6Q);if(!_6T[0]){var _6U=_6T[1];if(!(imul(_6S,_6U)|0)){return [0,imul(_6S,_6U)|0];}else{_6P=[1,I_fromInt(_6S)];_6Q=[1,I_fromInt(_6U)];continue;}}else{_6P=[1,I_fromInt(_6S)];_6Q=_6T;continue;}}else{var _6V=E(_6Q);if(!_6V[0]){_6P=_6R;_6Q=[1,I_fromInt(_6V[1])];continue;}else{return [1,I_mul(_6R[1],_6V[1])];}}}},_6W=function(_6X,_6Y,_6Z){if(!B(_6G(_6Z,_5U))){return new F(function(){return _5Y(B(_6O(_6Y,B(A(_6X,[_6Y])))),_6Z);});}else{return E(_6F);}},_70=0,_71=function(_){return _70;},_72=(function(e,p,v){e[p] = v;}),_73=new T(function(){return B(unCStr("innerHTML"));}),_74=function(_75,_76,_){var _77=E(_72)(_75,toJSStr(E(_73)),toJSStr(E(_76)));return new F(function(){return _71(_);});},_78=function(_79){return (E(_79)==46)?false:true;},_7a=new T(function(){return B(unCStr("!!: negative index"));}),_7b=new T(function(){return B(unCStr("Prelude."));}),_7c=new T(function(){return B(_4(_7b,_7a));}),_7d=new T(function(){return B(err(_7c));}),_7e=new T(function(){return B(unCStr("!!: index too large"));}),_7f=new T(function(){return B(_4(_7b,_7e));}),_7g=new T(function(){return B(err(_7f));}),_7h=function(_7i,_7j){while(1){var _7k=E(_7i);if(!_7k[0]){return E(_7g);}else{var _7l=E(_7j);if(!_7l){return E(_7k[1]);}else{_7i=_7k[2];_7j=_7l-1|0;continue;}}}},_7m=function(_7n,_7o){if(_7o>=0){return new F(function(){return _7h(_7n,_7o);});}else{return E(_7d);}},_7p=[0,1],_7q=[0,365],_7r=function(_7s){var _7t=E(_7s);if(!_7t[0]){return E(_7t[1]);}else{return new F(function(){return I_toInt(_7t[1]);});}},_7u=[0,100],_7v=[0,400],_7w=[0,4],_7x=function(_7y,_7z){var _7A=E(_7y);if(!_7A[0]){var _7B=_7A[1],_7C=E(_7z);return (_7C[0]==0)?_7B<=_7C[1]:I_compareInt(_7C[1],_7B)>=0;}else{var _7D=_7A[1],_7E=E(_7z);return (_7E[0]==0)?I_compareInt(_7D,_7E[1])<=0:I_compare(_7D,_7E[1])<=0;}},_7F=[0,678575],_7G=[0,146097],_7H=[0,36524],_7I=[0,1461],_7J=[0,0],_7K=new T(function(){return B(_6G(_7G,_7J));}),_7L=new T(function(){return B(_6G(_7H,_7J));}),_7M=new T(function(){return B(_6G(_7I,_7J));}),_7N=new T(function(){return B(_6G(_7q,_7J));}),_7O=function(_7P,_7Q){while(1){var _7R=E(_7P);if(!_7R[0]){var _7S=_7R[1],_7T=E(_7Q);if(!_7T[0]){var _7U=_7T[1],_7V=subC(_7S,_7U);if(!E(_7V[2])){return [0,_7V[1]];}else{_7P=[1,I_fromInt(_7S)];_7Q=[1,I_fromInt(_7U)];continue;}}else{_7P=[1,I_fromInt(_7S)];_7Q=_7T;continue;}}else{var _7W=E(_7Q);if(!_7W[0]){_7P=_7R;_7Q=[1,I_fromInt(_7W[1])];continue;}else{return [1,I_sub(_7R[1],_7W[1])];}}}},_7X=function(_7Y,_7Z){var _80=_7Y%_7Z;if(_7Y<=0){if(_7Y>=0){return E(_80);}else{if(_7Z<=0){return E(_80);}else{var _81=E(_80);return (_81==0)?0:_81+_7Z|0;}}}else{if(_7Z>=0){if(_7Y>=0){return E(_80);}else{if(_7Z<=0){return E(_80);}else{var _82=E(_80);return (_82==0)?0:_82+_7Z|0;}}}else{var _83=E(_80);return (_83==0)?0:_83+_7Z|0;}}},_84=function(_85,_86){while(1){var _87=E(_85);if(!_87[0]){var _88=E(_87[1]);if(_88==(-2147483648)){_85=[1,I_fromInt(-2147483648)];continue;}else{var _89=E(_86);if(!_89[0]){return [0,B(_7X(_88,_89[1]))];}else{_85=[1,I_fromInt(_88)];_86=_89;continue;}}}else{var _8a=_87[1],_8b=E(_86);return (_8b[0]==0)?[1,I_mod(_8a,I_fromInt(_8b[1]))]:[1,I_mod(_8a,_8b[1])];}}},_8c=function(_8d,_8e){while(1){var _8f=E(_8d);if(!_8f[0]){var _8g=_8f[1],_8h=E(_8e);if(!_8h[0]){var _8i=_8h[1],_8j=addC(_8g,_8i);if(!E(_8j[2])){return [0,_8j[1]];}else{_8d=[1,I_fromInt(_8g)];_8e=[1,I_fromInt(_8i)];continue;}}else{_8d=[1,I_fromInt(_8g)];_8e=_8h;continue;}}else{var _8k=E(_8e);if(!_8k[0]){_8d=_8f;_8e=[1,I_fromInt(_8k[1])];continue;}else{return [1,I_add(_8f[1],_8k[1])];}}}},_8l=[0,3],_8m=function(_8n){var _8o=new T(function(){return B(_8c(_8n,_7F));}),_8p=new T(function(){if(!E(_7K)){return B(_84(_8o,_7G));}else{return E(_6F);}}),_8q=new T(function(){if(!E(_7L)){var _8r=B(_5Y(_8p,_7H));if(!B(_7x(_8r,_8l))){return E(_8l);}else{return E(_8r);}}else{return E(_6F);}}),_8s=new T(function(){return B(_7O(_8p,B(_6O(_8q,_7H))));}),_8t=new T(function(){if(!E(_7M)){return B(_84(_8s,_7I));}else{return E(_6F);}}),_8u=new T(function(){if(!E(_7N)){var _8v=B(_5Y(_8t,_7q));if(!B(_7x(_8v,_8l))){return E(_8l);}else{return E(_8v);}}else{return E(_6F);}});return [0,new T(function(){if(!E(_7K)){if(!E(_7M)){return B(_8c(B(_8c(B(_8c(B(_8c(B(_6O(B(_5Y(_8o,_7G)),_7v)),B(_6O(_8q,_7u)))),B(_6O(B(_5Y(_8s,_7I)),_7w)))),_8u)),_7p));}else{return E(_6F);}}else{return E(_6F);}}),new T(function(){return B(_7r(B(_8c(B(_7O(_8t,B(_6O(_8u,_7q)))),_7p))));})];},_8w=[0,7],_8x=new T(function(){return B(_6G(_8w,_7J));}),_8y=function(_8z){return [0,_8z];},_8A=function(_8B){var _8C=new T(function(){return B(_8c(_8B,_8l));});return [0,new T(function(){if(!E(_8x)){return B(_7r(B(_7O(B(_5Y(_8C,_8w)),B(_5Y(B(_7O(_8C,B(_8y(E(B(_8m(_8B))[2]))))),_8w))))));}else{return E(_6F);}}),new T(function(){if(!E(_8x)){return B(_7r(B(_84(_8C,_8w))));}else{return E(_6F);}})];},_8D=function(_8E){return E(E(_8E)[1]);},_8F=function(_8G){return E(E(_8G)[1]);},_8H=function(_8I,_8J,_8K){return E(B(_7m(B(_8F(_8I)),E(B(_8A(new T(function(){return B(_8D(_8K));})))[2])))[2]);},_8L=function(_8M,_8N,_8O){return E(B(_7m(B(_8F(_8M)),E(B(_8A(new T(function(){return B(_8D(_8O));})))[2])))[1]);},_8P=new T(function(){return B(unCStr("%H:%M:%S"));}),_8Q=new T(function(){return B(unCStr("%H:%M"));}),_8R=new T(function(){return B(unCStr("%Y-%m-%d"));}),_8S=new T(function(){return B(unCStr("%m/%d/%y"));}),_8T=function(_8U,_8V){while(1){var _8W=E(_8V);if(!_8W[0]){return [0];}else{var _8X=_8W[2],_8Y=E(_8U);if(_8Y==1){return E(_8X);}else{_8U=_8Y-1|0;_8V=_8X;continue;}}}},_8Z=false,_90=function(_91,_92){while(1){var _93=E(_92);if(!_93[0]){return [0];}else{if(!B(A(_91,[_93[1]]))){return E(_93);}else{_92=_93[2];continue;}}}},_94=[0,1],_95=[0,1],_96=[0,10],_97=function(_98){while(1){var _99=E(_98);if(!_99[0]){_98=[1,I_fromInt(_99[1])];continue;}else{return new F(function(){return I_toString(_99[1]);});}}},_9a=function(_9b,_9c){return new F(function(){return _4(fromJSStr(B(_97(_9b))),_9c);});},_9d=function(_9e,_9f){var _9g=E(_9e);if(!_9g[0]){var _9h=_9g[1],_9i=E(_9f);return (_9i[0]==0)?_9h<_9i[1]:I_compareInt(_9i[1],_9h)>0;}else{var _9j=_9g[1],_9k=E(_9f);return (_9k[0]==0)?I_compareInt(_9j,_9k[1])<0:I_compare(_9j,_9k[1])<0;}},_9l=[0,0],_9m=function(_9n,_9o,_9p){if(_9n<=6){return new F(function(){return _9a(_9o,_9p);});}else{if(!B(_9d(_9o,_9l))){return new F(function(){return _9a(_9o,_9p);});}else{return [1,_d,new T(function(){return B(_4(fromJSStr(B(_97(_9o))),[1,_c,_9p]));})];}}},_9q=function(_9r,_9s,_9t){while(1){if(!(_9s%2)){var _9u=B(_6O(_9r,_9r)),_9v=quot(_9s,2);_9r=_9u;_9s=_9v;continue;}else{var _9w=E(_9s);if(_9w==1){return new F(function(){return _6O(_9r,_9t);});}else{var _9u=B(_6O(_9r,_9r)),_9x=B(_6O(_9r,_9t));_9r=_9u;_9s=quot(_9w-1|0,2);_9t=_9x;continue;}}}},_9y=function(_9z,_9A){while(1){if(!(_9A%2)){var _9B=B(_6O(_9z,_9z)),_9C=quot(_9A,2);_9z=_9B;_9A=_9C;continue;}else{var _9D=E(_9A);if(_9D==1){return E(_9z);}else{return new F(function(){return _9q(B(_6O(_9z,_9z)),quot(_9D-1|0,2),_9z);});}}}},_9E=function(_9F,_9G){while(1){var _9H=E(_9F);if(!_9H[0]){return E(_9G);}else{var _9I=_9G+1|0;_9F=_9H[2];_9G=_9I;continue;}}},_9J=new T(function(){return B(unCStr("Negative exponent"));}),_9K=new T(function(){return B(err(_9J));}),_9L=function(_9M){return new F(function(){return _9m(0,_9M,_w);});},_9N=new T(function(){return B(_6G(_96,_5U));}),_9O=function(_9P){while(1){if(!B(_6G(_9P,_5U))){if(!E(_9N)){if(!B(_6G(B(_84(_9P,_96)),_5U))){return new F(function(){return _9L(_9P);});}else{var _9Q=B(_5Y(_9P,_96));_9P=_9Q;continue;}}else{return E(_6F);}}else{return [0];}}},_9R=function(_9S,_9T){while(1){var _9U=E(_9S);if(!_9U[0]){var _9V=E(_9U[1]);if(_9V==(-2147483648)){_9S=[1,I_fromInt(-2147483648)];continue;}else{var _9W=E(_9T);if(!_9W[0]){var _9X=_9W[1];return [0,[0,B(_5V(_9V,_9X))],[0,B(_7X(_9V,_9X))]];}else{_9S=[1,I_fromInt(_9V)];_9T=_9W;continue;}}}else{var _9Y=E(_9T);if(!_9Y[0]){_9S=_9U;_9T=[1,I_fromInt(_9Y[1])];continue;}else{var _9Z=I_divMod(_9U[1],_9Y[1]);return [0,[1,_9Z[1]],[1,_9Z[2]]];}}}},_a0=function(_a1){var _a2=E(_a1);if(!_a2[0]){return _a2[1];}else{return new F(function(){return I_toNumber(_a2[1]);});}},_a3=46,_a4=48,_a5=[0,1],_a6=[0,2147483647],_a7=new T(function(){return B(_8c(_a6,_a5));}),_a8=function(_a9){var _aa=E(_a9);if(!_aa[0]){var _ab=E(_aa[1]);return (_ab==(-2147483648))?E(_a7):[0, -_ab];}else{return [1,I_negate(_aa[1])];}},_ac=function(_ad,_ae,_af){if(!B(_9d(_af,_5U))){var _ag=B(A(_ad,[_af]));if(!B(_6G(_ag,_5U))){var _ah=B(_9R(_af,_ag)),_ai=_ah[2],_aj=new T(function(){var _ak=Math.log(B(_a0(_ag)))/Math.log(10),_al=_ak&4294967295,_am=function(_an){if(_an>=0){var _ao=E(_an);if(!_ao){var _ap=B(_5Y(B(_7O(B(_8c(B(_6O(_ai,_95)),_ag)),_94)),_ag));}else{var _ap=B(_5Y(B(_7O(B(_8c(B(_6O(_ai,B(_9y(_96,_ao)))),_ag)),_94)),_ag));}var _aq=function(_ar){var _as=B(_9m(0,_ap,_w)),_at=_an-B(_9E(_as,0))|0;if(0>=_at){if(!E(_ae)){return E(_as);}else{return new F(function(){return _9O(_ap);});}}else{var _au=new T(function(){if(!E(_ae)){return E(_as);}else{return B(_9O(_ap));}}),_av=function(_aw){var _ax=E(_aw);return (_ax==1)?[1,_a4,_au]:[1,_a4,new T(function(){return B(_av(_ax-1|0));})];};return new F(function(){return _av(_at);});}};if(!E(_ae)){var _ay=B(_aq(_));return (_ay[0]==0)?[0]:[1,_a3,_ay];}else{if(!B(_6G(_ap,_5U))){var _az=B(_aq(_));return (_az[0]==0)?[0]:[1,_a3,_az];}else{return [0];}}}else{return E(_9K);}};if(_al>=_ak){return B(_am(_al));}else{return B(_am(_al+1|0));}},1);return new F(function(){return _4(B(_9m(0,_ah[1],_w)),_aj);});}else{return E(_6F);}}else{return new F(function(){return unAppCStr("-",new T(function(){return B(_ac(_ad,_ae,B(_a8(_af))));}));});}},_aA=function(_aB){return new F(function(){return _8T(1,B(_90(_78,B(_ac(_3i,_8Z,_aB)))));});},_aC=function(_aD,_aE,_aF){return new F(function(){return _aA(E(_aF)[3]);});},_aG=function(_aH,_aI,_aJ){return (E(E(_aJ)[1])>=12)?E(E(E(_aH)[3])[2]):E(E(E(_aH)[3])[1]);},_aK=32,_aL=[1,_aK],_aM=function(_aN,_aO){return imul(E(_aN),E(_aO))|0;},_aP=function(_aQ,_aR){return E(_aQ)+E(_aR)|0;},_aS=function(_aT,_aU){return E(_aT)-E(_aU)|0;},_aV=function(_aW){var _aX=E(_aW);return (_aX<0)? -_aX:E(_aX);},_aY=function(_aZ){return new F(function(){return _7r(_aZ);});},_b0=function(_b1){return  -E(_b1);},_b2=-1,_b3=0,_b4=1,_b5=function(_b6){var _b7=E(_b6);return (_b7>=0)?(E(_b7)==0)?E(_b3):E(_b4):E(_b2);},_b8=[0,_aP,_aS,_aM,_b0,_aV,_b5,_aY],_b9=function(_ba,_bb){return E(_ba)==E(_bb);},_bc=function(_bd,_be){return E(_bd)!=E(_be);},_bf=[0,_b9,_bc],_bg=function(_bh,_bi){var _bj=E(_bh),_bk=E(_bi);return (_bj>_bk)?E(_bj):E(_bk);},_bl=function(_bm,_bn){var _bo=E(_bm),_bp=E(_bn);return (_bo>_bp)?E(_bp):E(_bo);},_bq=function(_br,_bs){return (_br>=_bs)?(_br!=_bs)?2:1:0;},_bt=function(_bu,_bv){return new F(function(){return _bq(E(_bu),E(_bv));});},_bw=function(_bx,_by){return E(_bx)>=E(_by);},_bz=function(_bA,_bB){return E(_bA)>E(_bB);},_bC=function(_bD,_bE){return E(_bD)<=E(_bE);},_bF=function(_bG,_bH){return E(_bG)<E(_bH);},_bI=[0,_bf,_bt,_bF,_bC,_bz,_bw,_bg,_bl],_bJ=function(_bK){return new F(function(){return _e(0,E(_bK),_w);});},_bL=function(_bM,_bN,_bO){return new F(function(){return _e(E(_bM),E(_bN),_bO);});},_bP=function(_bQ,_bR){return new F(function(){return _e(0,E(_bQ),_bR);});},_bS=function(_bT,_bU){return new F(function(){return _2a(_bP,_bT,_bU);});},_bV=[0,_bL,_bJ,_bS],_bW=2,_bX=function(_bY,_bZ,_c0){if(_bY>0){if(0>=_bY){return E(_c0);}else{var _c1=function(_c2){var _c3=E(_c2);return (_c3==1)?[1,_bZ,_c0]:[1,_bZ,new T(function(){return B(_c1(_c3-1|0));})];};return new F(function(){return _c1(_bY);});}}else{return E(_c0);}},_c4=function(_c5){return E(E(_c5)[3]);},_c6=function(_c7){return E(E(_c7)[7]);},_c8=45,_c9=[0,0],_ca=function(_cb){return E(E(_cb)[4]);},_cc=function(_cd){return E(E(_cd)[2]);},_ce=function(_cf,_cg,_ch,_ci,_cj,_ck){var _cl=E(_cj);if(!_cl[0]){return new F(function(){return A(_cc,[_ch,_ck]);});}else{if(!B(A(_c4,[_cg,_ck,new T(function(){return B(A(_c6,[_cf,_c9]));})]))){var _cm=B(A(_cc,[_ch,_ck]));return new F(function(){return _bX(E(_ci)-B(_9E(_cm,0))|0,_cl[1],_cm);});}else{var _cn=new T(function(){return B(_ce(_cf,_cg,_ch,_ci,_cl,new T(function(){return B(A(_ca,[_cf,_ck]));})));});return [1,_c8,_cn];}}},_co=function(_cp,_cq){var _cr=new T(function(){return B(_7X(E(E(_cq)[1])-1|0,12))+1|0;}),_cs=E(_cp);if(!_cs[0]){return new F(function(){return _ce(_b8,_bI,_bV,_bW,_aL,_cr);});}else{return new F(function(){return _ce(_b8,_bI,_bV,_bW,_cs[1],_cr);});}},_ct=function(_cu,_cv,_cw){return new F(function(){return _co(_cv,_cw);});},_cx=function(_cy,_cz){var _cA=E(_cy);if(!_cA[0]){return new F(function(){return _ce(_b8,_bI,_bV,_bW,_aL,new T(function(){return E(E(_cz)[1]);}));});}else{return new F(function(){return _ce(_b8,_bI,_bV,_bW,_cA[1],new T(function(){return E(E(_cz)[1]);}));});}},_cB=function(_cC,_cD,_cE){return new F(function(){return _cx(_cD,_cE);});},_cF=function(_cG,_cH,_cI){var _cJ=E(_cG);return new F(function(){return _cK(_cJ,_cJ[6],_cI);});},_cL=function(_cM,_cN,_cO){return new F(function(){return _cK(_cM,_8P,_cO);});},_cP=48,_cQ=[1,_cP],_cR=function(_cS,_cT){if(_cS<=_cT){var _cU=function(_cV){return [1,_cV,new T(function(){if(_cV!=_cT){return B(_cU(_cV+1|0));}else{return [0];}})];};return new F(function(){return _cU(_cS);});}else{return [0];}},_cW=function(_cX){return new F(function(){return _cR(E(_cX),2147483647);});},_cY=function(_cZ,_d0,_d1){if(_d1<=_d0){var _d2=new T(function(){var _d3=_d0-_cZ|0,_d4=function(_d5){return (_d5>=(_d1-_d3|0))?[1,_d5,new T(function(){return B(_d4(_d5+_d3|0));})]:[1,_d5,_w];};return B(_d4(_d0));});return [1,_cZ,_d2];}else{return (_d1<=_cZ)?[1,_cZ,_w]:[0];}},_d6=function(_d7,_d8,_d9){if(_d9>=_d8){var _da=new T(function(){var _db=_d8-_d7|0,_dc=function(_dd){return (_dd<=(_d9-_db|0))?[1,_dd,new T(function(){return B(_dc(_dd+_db|0));})]:[1,_dd,_w];};return B(_dc(_d8));});return [1,_d7,_da];}else{return (_d9>=_d7)?[1,_d7,_w]:[0];}},_de=function(_df,_dg){if(_dg<_df){return new F(function(){return _cY(_df,_dg,-2147483648);});}else{return new F(function(){return _d6(_df,_dg,2147483647);});}},_dh=function(_di,_dj){return new F(function(){return _de(E(_di),E(_dj));});},_dk=function(_dl,_dm,_dn){if(_dm<_dl){return new F(function(){return _cY(_dl,_dm,_dn);});}else{return new F(function(){return _d6(_dl,_dm,_dn);});}},_do=function(_dp,_dq,_dr){return new F(function(){return _dk(E(_dp),E(_dq),E(_dr));});},_ds=function(_dt,_du){return new F(function(){return _cR(E(_dt),E(_du));});},_dv=function(_dw){return E(_dw);},_dx=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_dy=new T(function(){return B(err(_dx));}),_dz=function(_dA){var _dB=E(_dA);return (_dB==(-2147483648))?E(_dy):_dB-1|0;},_dC=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_dD=new T(function(){return B(err(_dC));}),_dE=function(_dF){var _dG=E(_dF);return (_dG==2147483647)?E(_dD):_dG+1|0;},_dH=[0,_dE,_dz,_dv,_dv,_cW,_dh,_ds,_do],_dI=0,_dJ=new T(function(){return B(_6B(_dI));}),_dK=new T(function(){return die(_dJ);}),_dL=function(_dM,_dN){var _dO=E(_dN);switch(_dO){case -1:var _dP=E(_dM);if(_dP==(-2147483648)){return E(_dK);}else{return new F(function(){return _5V(_dP,-1);});}break;case 0:return E(_6F);default:return new F(function(){return _5V(_dM,_dO);});}},_dQ=function(_dR,_dS){return new F(function(){return _dL(E(_dR),E(_dS));});},_dT=0,_dU=[0,_dK,_dT],_dV=function(_dW,_dX){var _dY=E(_dW),_dZ=E(_dX);switch(_dZ){case -1:var _e0=E(_dY);if(_e0==(-2147483648)){return E(_dU);}else{if(_e0<=0){if(_e0>=0){var _e1=quotRemI(_e0,-1);return [0,_e1[1],_e1[2]];}else{var _e2=quotRemI(_e0,-1);return [0,_e2[1],_e2[2]];}}else{var _e3=quotRemI(_e0-1|0,-1);return [0,_e3[1]-1|0,(_e3[2]+(-1)|0)+1|0];}}break;case 0:return E(_6F);default:if(_dY<=0){if(_dY>=0){var _e4=quotRemI(_dY,_dZ);return [0,_e4[1],_e4[2]];}else{if(_dZ<=0){var _e5=quotRemI(_dY,_dZ);return [0,_e5[1],_e5[2]];}else{var _e6=quotRemI(_dY+1|0,_dZ);return [0,_e6[1]-1|0,(_e6[2]+_dZ|0)-1|0];}}}else{if(_dZ>=0){if(_dY>=0){var _e7=quotRemI(_dY,_dZ);return [0,_e7[1],_e7[2]];}else{if(_dZ<=0){var _e8=quotRemI(_dY,_dZ);return [0,_e8[1],_e8[2]];}else{var _e9=quotRemI(_dY+1|0,_dZ);return [0,_e9[1]-1|0,(_e9[2]+_dZ|0)-1|0];}}}else{var _ea=quotRemI(_dY-1|0,_dZ);return [0,_ea[1]-1|0,(_ea[2]+_dZ|0)+1|0];}}}},_eb=function(_ec,_ed){var _ee=E(_ed);switch(_ee){case -1:return E(_dT);case 0:return E(_6F);default:return new F(function(){return _7X(E(_ec),_ee);});}},_ef=function(_eg,_eh){var _ei=E(_eg),_ej=E(_eh);switch(_ej){case -1:var _ek=E(_ei);if(_ek==(-2147483648)){return E(_dK);}else{return new F(function(){return quot(_ek,-1);});}break;case 0:return E(_6F);default:return new F(function(){return quot(_ei,_ej);});}},_el=function(_em,_en){var _eo=E(_em),_ep=E(_en);switch(_ep){case -1:var _eq=E(_eo);if(_eq==(-2147483648)){return E(_dU);}else{var _er=quotRemI(_eq,-1);return [0,_er[1],_er[2]];}break;case 0:return E(_6F);default:var _es=quotRemI(_eo,_ep);return [0,_es[1],_es[2]];}},_et=function(_eu,_ev){var _ew=E(_ev);switch(_ew){case -1:return E(_dT);case 0:return E(_6F);default:return E(_eu)%_ew;}},_ex=function(_ey){return new F(function(){return _8y(E(_ey));});},_ez=function(_eA){return [0,E(B(_8y(E(_eA)))),E(_95)];},_eB=[0,_b8,_bI,_ez],_eC=[0,_eB,_dH,_ef,_et,_dQ,_eb,_el,_dV,_ex],_eD=[0,0],_eE=function(_eF,_eG){while(1){var _eH=E(_eF);if(!_eH[0]){var _eI=E(_eH[1]);if(_eI==(-2147483648)){_eF=[1,I_fromInt(-2147483648)];continue;}else{var _eJ=E(_eG);if(!_eJ[0]){return [0,_eI%_eJ[1]];}else{_eF=[1,I_fromInt(_eI)];_eG=_eJ;continue;}}}else{var _eK=_eH[1],_eL=E(_eG);return (_eL[0]==0)?[1,I_rem(_eK,I_fromInt(_eL[1]))]:[1,I_rem(_eK,_eL[1])];}}},_eM=function(_eN,_eO){if(!B(_6G(_eO,_eD))){return new F(function(){return _eE(_eN,_eO);});}else{return E(_6F);}},_eP=function(_eQ,_eR){while(1){if(!B(_6G(_eR,_eD))){var _eS=_eR,_eT=B(_eM(_eQ,_eR));_eQ=_eS;_eR=_eT;continue;}else{return E(_eQ);}}},_eU=function(_eV){var _eW=E(_eV);if(!_eW[0]){var _eX=E(_eW[1]);return (_eX==(-2147483648))?E(_a7):(_eX<0)?[0, -_eX]:E(_eW);}else{var _eY=_eW[1];return (I_compareInt(_eY,0)>=0)?E(_eW):[1,I_negate(_eY)];}},_eZ=function(_f0,_f1){while(1){var _f2=E(_f0);if(!_f2[0]){var _f3=E(_f2[1]);if(_f3==(-2147483648)){_f0=[1,I_fromInt(-2147483648)];continue;}else{var _f4=E(_f1);if(!_f4[0]){return [0,quot(_f3,_f4[1])];}else{_f0=[1,I_fromInt(_f3)];_f1=_f4;continue;}}}else{var _f5=_f2[1],_f6=E(_f1);return (_f6[0]==0)?[0,I_toInt(I_quot(_f5,I_fromInt(_f6[1])))]:[1,I_quot(_f5,_f6[1])];}}},_f7=5,_f8=new T(function(){return B(_6B(_f7));}),_f9=new T(function(){return die(_f8);}),_fa=function(_fb,_fc){if(!B(_6G(_fc,_eD))){var _fd=B(_eP(B(_eU(_fb)),B(_eU(_fc))));return (!B(_6G(_fd,_eD)))?[0,B(_eZ(_fb,_fd)),B(_eZ(_fc,_fd))]:E(_6F);}else{return E(_f9);}},_fe=[0,0],_ff=[0,-1],_fg=function(_fh){var _fi=E(_fh);if(!_fi[0]){var _fj=_fi[1];return (_fj>=0)?(E(_fj)==0)?E(_fe):E(_a5):E(_ff);}else{var _fk=I_compareInt(_fi[1],0);return (_fk<=0)?(E(_fk)==0)?E(_fe):E(_ff):E(_a5);}},_fl=function(_fm,_fn,_fo,_fp){var _fq=B(_6O(_fn,_fo));return new F(function(){return _fa(B(_6O(B(_6O(_fm,_fp)),B(_fg(_fq)))),B(_eU(_fq)));});},_fr=function(_fs){return E(E(_fs)[1]);},_ft=function(_fu){return E(E(_fu)[1]);},_fv=function(_fw,_fx){while(1){var _fy=E(_fw);if(!_fy[0]){var _fz=E(_fy[1]);if(_fz==(-2147483648)){_fw=[1,I_fromInt(-2147483648)];continue;}else{var _fA=E(_fx);if(!_fA[0]){var _fB=_fA[1];return [0,[0,quot(_fz,_fB)],[0,_fz%_fB]];}else{_fw=[1,I_fromInt(_fz)];_fx=_fA;continue;}}}else{var _fC=E(_fx);if(!_fC[0]){_fw=_fy;_fx=[1,I_fromInt(_fC[1])];continue;}else{var _fD=I_quotRem(_fy[1],_fC[1]);return [0,[1,_fD[1]],[1,_fD[2]]];}}}},_fE=function(_fF,_fG,_fH){var _fI=new T(function(){if(!B(_6G(_fH,_eD))){var _fJ=B(_fv(_fG,_fH));return [0,_fJ[1],_fJ[2]];}else{return E(_6F);}}),_fK=new T(function(){return B(A(_c6,[B(_ft(B(_fr(_fF)))),new T(function(){return E(E(_fI)[1]);})]));});return [0,_fK,new T(function(){return [0,E(E(_fI)[2]),E(_fH)];})];},_fL=function(_fM,_fN){var _fO=new T(function(){var _fP=B(_fl(E(_fN)[3],_95,_3h,_95));return E(B(_fE(_eC,_fP[1],_fP[2]))[1]);}),_fQ=E(_fM);if(!_fQ[0]){return new F(function(){return _ce(_b8,_bI,_bV,_bW,_cQ,_fO);});}else{return new F(function(){return _ce(_b8,_bI,_bV,_bW,_fQ[1],_fO);});}},_fR=function(_fS,_fT,_fU){return new F(function(){return _fL(_fT,_fU);});},_fV=function(_fW,_fX,_cO){return new F(function(){return _cK(_fW,_8Q,_cO);});},_fY=true,_fZ=function(_g0){return E(E(_g0)[3]);},_g1=function(_g2,_g3,_g4){return new F(function(){return _90(_78,B(_ac(_3i,_fY,B(_fZ(_g4)))));});},_g5=function(_g6,_g7){var _g8=E(_g7);return (_g8[0]==0)?[0]:[1,new T(function(){return B(A(_g6,[_g8[1]]));}),new T(function(){return B(_g5(_g6,_g8[2]));})];},_g9=function(_ga){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_e(9,_ga,_w));}))));});},_gb=function(_gc){var _gd=u_towlower(E(_gc));if(_gd>>>0>1114111){return new F(function(){return _g9(_gd);});}else{return _gd;}},_ge=function(_gf,_gg,_gh){if(_gh>=12){return new F(function(){return _g5(_gb,_gg);});}else{return new F(function(){return _g5(_gb,_gf);});}},_gi=function(_gj,_gk,_gl){var _gm=E(E(_gj)[3]);return new F(function(){return _ge(_gm[1],_gm[2],E(E(_gl)[1]));});},_gn=function(_go,_gp){var _gq=E(_go);if(!_gq[0]){return new F(function(){return _ce(_b8,_bI,_bV,_bW,_cQ,new T(function(){return E(E(_gp)[2]);}));});}else{return new F(function(){return _ce(_b8,_bI,_bV,_bW,_gq[1],new T(function(){return E(E(_gp)[2]);}));});}},_gr=function(_gs,_gt,_gu){return new F(function(){return _gn(_gt,_gu);});},_gv=function(_gw,_gx){var _gy=new T(function(){return B(_7X(E(E(_gx)[1])-1|0,12))+1|0;}),_gz=E(_gw);if(!_gz[0]){return new F(function(){return _ce(_b8,_bI,_bV,_bW,_cQ,_gy);});}else{return new F(function(){return _ce(_b8,_bI,_bV,_bW,_gz[1],_gy);});}},_gA=function(_gB,_gC,_gD){return new F(function(){return _gv(_gC,_gD);});},_gE=function(_gF,_gG){var _gH=E(_gF);if(!_gH[0]){return new F(function(){return _ce(_b8,_bI,_bV,_bW,_cQ,new T(function(){return E(E(_gG)[1]);}));});}else{return new F(function(){return _ce(_b8,_bI,_bV,_bW,_gH[1],new T(function(){return E(E(_gG)[1]);}));});}},_gI=function(_gJ,_gK,_gL){return new F(function(){return _gE(_gK,_gL);});},_gM=function(_gN,_gO,_gP){var _gQ=E(_gN);return new F(function(){return _cK(_gQ,_gQ[7],_gP);});},_gR=new T(function(){return B(unCStr("	"));}),_gS=new T(function(){return B(unCStr("\n"));}),_gT=new T(function(){return B(unCStr("%"));}),_gU=[1,_aL],_gV=[1,_cQ],_gW=[1,_2s],_gX=function(_gY){var _gZ=u_towupper(E(_gY));if(_gZ>>>0>1114111){return new F(function(){return _g9(_gZ);});}else{return _gZ;}},_cK=function(_h0,_h1,_h2){while(1){var _h3=B((function(_h4,_h5,_h6){var _h7=E(_h5);if(!_h7[0]){return [0];}else{var _h8=_h7[2],_h9=E(_h7[1]);if(E(_h9)==37){var _ha=E(_h8);if(!_ha[0]){return [1,_h9,new T(function(){return B(_cK(_h4,_w,_h6));})];}else{var _hb=_ha[2],_hc=E(_ha[1]),_hd=function(_he){switch(E(_hc)){case 37:return new F(function(){return _4(_gT,new T(function(){return B(_cK(_h4,_hb,_h6));},1));});break;case 72:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_bW,_cQ,new T(function(){return E(E(_h6)[1]);}))),new T(function(){return B(_cK(_h4,_hb,_h6));},1));});break;case 73:return new F(function(){return _4(B(_gv(_2s,_h6)),new T(function(){return B(_cK(_h4,_hb,_h6));},1));});break;case 77:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_bW,_cQ,new T(function(){return E(E(_h6)[2]);}))),new T(function(){return B(_cK(_h4,_hb,_h6));},1));});break;case 80:var _hf=E(_h4),_hg=E(_hf[3]),_hh=E(_h6);if(E(_hh[1])>=12){return new F(function(){return _4(B(_g5(_gb,_hg[2])),new T(function(){return B(_cK(_hf,_hb,_hh));},1));});}else{return new F(function(){return _4(B(_g5(_gb,_hg[1])),new T(function(){return B(_cK(_hf,_hb,_hh));},1));});}break;case 81:var _hi=E(_h6);return new F(function(){return _4(B(_90(_78,B(_ac(_3i,_fY,_hi[3])))),new T(function(){return B(_cK(_h4,_hb,_hi));},1));});break;case 82:return new F(function(){return _4(B(_cK(_h4,_8Q,_h6)),new T(function(){return B(_cK(_h4,_hb,_h6));},1));});break;case 83:return new F(function(){return _4(B(_fL(_2s,_h6)),new T(function(){return B(_cK(_h4,_hb,_h6));},1));});break;case 84:return new F(function(){return _4(B(_cK(_h4,_8P,_h6)),new T(function(){return B(_cK(_h4,_hb,_h6));},1));});break;case 88:var _hj=E(_h4);return new F(function(){return _4(B(_cK(_hj,_hj[6],_h6)),new T(function(){return B(_cK(_hj,_hb,_h6));},1));});break;case 107:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_bW,_aL,new T(function(){return E(E(_h6)[1]);}))),new T(function(){return B(_cK(_h4,_hb,_h6));},1));});break;case 108:return new F(function(){return _4(B(_co(_2s,_h6)),new T(function(){return B(_cK(_h4,_hb,_h6));},1));});break;case 110:return new F(function(){return _4(_gS,new T(function(){return B(_cK(_h4,_hb,_h6));},1));});break;case 112:var _hk=E(_h6);if(E(_hk[1])>=12){var _hl=E(_h4);return new F(function(){return _4(E(_hl[3])[2],new T(function(){return B(_cK(_hl,_hb,_hk));},1));});}else{var _hm=E(_h4);return new F(function(){return _4(E(_hm[3])[1],new T(function(){return B(_cK(_hm,_hb,_hk));},1));});}break;case 113:var _hn=E(_h6);return new F(function(){return _4(B(_aA(_hn[3])),new T(function(){return B(_cK(_h4,_hb,_hn));},1));});break;case 114:var _ho=E(_h4);return new F(function(){return _4(B(_cK(_ho,_ho[7],_h6)),new T(function(){return B(_cK(_ho,_hb,_h6));},1));});break;case 116:return new F(function(){return _4(_gR,new T(function(){return B(_cK(_h4,_hb,_h6));},1));});break;default:return new F(function(){return _cK(_h4,_hb,_h6);});}};switch(E(_hc)){case 35:var _hp=E(_hb);if(!_hp[0]){return new F(function(){return _hd(_);});}else{var _hq=_hp[2],_hr=E(_hp[1]);switch(_hr){case 37:var _hs=new T(function(){return B(_cK(_h4,_hq,_h6));}),_ht=function(_hu){var _hv=E(_hu);return (_hv[0]==0)?E(_hs):[1,new T(function(){return B(_gb(_hv[1]));}),new T(function(){return B(_ht(_hv[2]));})];};return new F(function(){return _ht(_gT);});break;case 110:var _hw=new T(function(){return B(_cK(_h4,_hq,_h6));}),_hx=function(_hy){var _hz=E(_hy);return (_hz[0]==0)?E(_hw):[1,new T(function(){return B(_gb(_hz[1]));}),new T(function(){return B(_hx(_hz[2]));})];};return new F(function(){return _hx(_gS);});break;case 116:var _hA=new T(function(){return B(_cK(_h4,_hq,_h6));}),_hB=function(_hC){var _hD=E(_hC);return (_hD[0]==0)?E(_hA):[1,new T(function(){return B(_gb(_hD[1]));}),new T(function(){return B(_hB(_hD[2]));})];};return new F(function(){return _hB(_gR);});break;default:var _hE=function(_hF){var _hG=new T(function(){return B(_cK(_h4,_hq,_h6));}),_hH=function(_hI){var _hJ=E(_hI);return (_hJ[0]==0)?E(_hG):[1,new T(function(){return B(_gb(_hJ[1]));}),new T(function(){return B(_hH(_hJ[2]));})];};return new F(function(){return _hH(B(A(_hF,[_h4,_2s,_h6])));});};switch(E(_hr)){case 72:return new F(function(){return _hE(_gI);});break;case 73:return new F(function(){return _hE(_gA);});break;case 77:return new F(function(){return _hE(_gr);});break;case 80:return new F(function(){return _hE(_gi);});break;case 81:return new F(function(){return _hE(_g1);});break;case 82:return new F(function(){return _hE(_fV);});break;case 83:return new F(function(){return _hE(_fR);});break;case 84:return new F(function(){return _hE(_cL);});break;case 88:return new F(function(){return _hE(_cF);});break;case 107:return new F(function(){return _hE(_cB);});break;case 108:return new F(function(){return _hE(_ct);});break;case 112:return new F(function(){return _hE(_aG);});break;case 113:return new F(function(){return _hE(_aC);});break;case 114:return new F(function(){return _hE(_gM);});break;default:var _hK=_h4,_hL=_h6;_h0=_hK;_h1=_hq;_h2=_hL;return null;}}}break;case 45:var _hM=E(_hb);if(!_hM[0]){return new F(function(){return _hd(_);});}else{var _hN=_hM[2];switch(E(_hM[1])){case 37:return new F(function(){return _4(_gT,new T(function(){return B(_cK(_h4,_hN,_h6));},1));});break;case 72:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_bW,_2s,new T(function(){return E(E(_h6)[1]);}))),new T(function(){return B(_cK(_h4,_hN,_h6));},1));});break;case 73:return new F(function(){return _4(B(_gv(_gW,_h6)),new T(function(){return B(_cK(_h4,_hN,_h6));},1));});break;case 77:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_bW,_2s,new T(function(){return E(E(_h6)[2]);}))),new T(function(){return B(_cK(_h4,_hN,_h6));},1));});break;case 80:var _hO=E(_h4),_hP=E(_hO[3]),_hQ=E(_h6);if(E(_hQ[1])>=12){return new F(function(){return _4(B(_g5(_gb,_hP[2])),new T(function(){return B(_cK(_hO,_hN,_hQ));},1));});}else{return new F(function(){return _4(B(_g5(_gb,_hP[1])),new T(function(){return B(_cK(_hO,_hN,_hQ));},1));});}break;case 81:var _hR=E(_h6);return new F(function(){return _4(B(_90(_78,B(_ac(_3i,_fY,_hR[3])))),new T(function(){return B(_cK(_h4,_hN,_hR));},1));});break;case 82:return new F(function(){return _4(B(_cK(_h4,_8Q,_h6)),new T(function(){return B(_cK(_h4,_hN,_h6));},1));});break;case 83:return new F(function(){return _4(B(_fL(_gW,_h6)),new T(function(){return B(_cK(_h4,_hN,_h6));},1));});break;case 84:return new F(function(){return _4(B(_cK(_h4,_8P,_h6)),new T(function(){return B(_cK(_h4,_hN,_h6));},1));});break;case 88:var _hS=E(_h4);return new F(function(){return _4(B(_cK(_hS,_hS[6],_h6)),new T(function(){return B(_cK(_hS,_hN,_h6));},1));});break;case 107:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_bW,_2s,new T(function(){return E(E(_h6)[1]);}))),new T(function(){return B(_cK(_h4,_hN,_h6));},1));});break;case 108:return new F(function(){return _4(B(_co(_gW,_h6)),new T(function(){return B(_cK(_h4,_hN,_h6));},1));});break;case 110:return new F(function(){return _4(_gS,new T(function(){return B(_cK(_h4,_hN,_h6));},1));});break;case 112:var _hT=E(_h6);if(E(_hT[1])>=12){var _hU=E(_h4);return new F(function(){return _4(E(_hU[3])[2],new T(function(){return B(_cK(_hU,_hN,_hT));},1));});}else{var _hV=E(_h4);return new F(function(){return _4(E(_hV[3])[1],new T(function(){return B(_cK(_hV,_hN,_hT));},1));});}break;case 113:var _hW=E(_h6);return new F(function(){return _4(B(_aA(_hW[3])),new T(function(){return B(_cK(_h4,_hN,_hW));},1));});break;case 114:var _hX=E(_h4);return new F(function(){return _4(B(_cK(_hX,_hX[7],_h6)),new T(function(){return B(_cK(_hX,_hN,_h6));},1));});break;case 116:return new F(function(){return _4(_gR,new T(function(){return B(_cK(_h4,_hN,_h6));},1));});break;default:var _hK=_h4,_hL=_h6;_h0=_hK;_h1=_hN;_h2=_hL;return null;}}break;case 48:var _hY=E(_hb);if(!_hY[0]){return new F(function(){return _hd(_);});}else{var _hZ=_hY[2];switch(E(_hY[1])){case 37:return new F(function(){return _4(_gT,new T(function(){return B(_cK(_h4,_hZ,_h6));},1));});break;case 72:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_bW,_cQ,new T(function(){return E(E(_h6)[1]);}))),new T(function(){return B(_cK(_h4,_hZ,_h6));},1));});break;case 73:return new F(function(){return _4(B(_gv(_gV,_h6)),new T(function(){return B(_cK(_h4,_hZ,_h6));},1));});break;case 77:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_bW,_cQ,new T(function(){return E(E(_h6)[2]);}))),new T(function(){return B(_cK(_h4,_hZ,_h6));},1));});break;case 80:var _i0=E(_h4),_i1=E(_i0[3]),_i2=E(_h6);if(E(_i2[1])>=12){return new F(function(){return _4(B(_g5(_gb,_i1[2])),new T(function(){return B(_cK(_i0,_hZ,_i2));},1));});}else{return new F(function(){return _4(B(_g5(_gb,_i1[1])),new T(function(){return B(_cK(_i0,_hZ,_i2));},1));});}break;case 81:var _i3=E(_h6);return new F(function(){return _4(B(_90(_78,B(_ac(_3i,_fY,_i3[3])))),new T(function(){return B(_cK(_h4,_hZ,_i3));},1));});break;case 82:return new F(function(){return _4(B(_cK(_h4,_8Q,_h6)),new T(function(){return B(_cK(_h4,_hZ,_h6));},1));});break;case 83:return new F(function(){return _4(B(_fL(_gV,_h6)),new T(function(){return B(_cK(_h4,_hZ,_h6));},1));});break;case 84:return new F(function(){return _4(B(_cK(_h4,_8P,_h6)),new T(function(){return B(_cK(_h4,_hZ,_h6));},1));});break;case 88:var _i4=E(_h4);return new F(function(){return _4(B(_cK(_i4,_i4[6],_h6)),new T(function(){return B(_cK(_i4,_hZ,_h6));},1));});break;case 107:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_bW,_cQ,new T(function(){return E(E(_h6)[1]);}))),new T(function(){return B(_cK(_h4,_hZ,_h6));},1));});break;case 108:return new F(function(){return _4(B(_co(_gV,_h6)),new T(function(){return B(_cK(_h4,_hZ,_h6));},1));});break;case 110:return new F(function(){return _4(_gS,new T(function(){return B(_cK(_h4,_hZ,_h6));},1));});break;case 112:var _i5=E(_h6);if(E(_i5[1])>=12){var _i6=E(_h4);return new F(function(){return _4(E(_i6[3])[2],new T(function(){return B(_cK(_i6,_hZ,_i5));},1));});}else{var _i7=E(_h4);return new F(function(){return _4(E(_i7[3])[1],new T(function(){return B(_cK(_i7,_hZ,_i5));},1));});}break;case 113:var _i8=E(_h6);return new F(function(){return _4(B(_aA(_i8[3])),new T(function(){return B(_cK(_h4,_hZ,_i8));},1));});break;case 114:var _i9=E(_h4);return new F(function(){return _4(B(_cK(_i9,_i9[7],_h6)),new T(function(){return B(_cK(_i9,_hZ,_h6));},1));});break;case 116:return new F(function(){return _4(_gR,new T(function(){return B(_cK(_h4,_hZ,_h6));},1));});break;default:var _hK=_h4,_hL=_h6;_h0=_hK;_h1=_hZ;_h2=_hL;return null;}}break;case 94:var _ia=E(_hb);if(!_ia[0]){return new F(function(){return _hd(_);});}else{var _ib=_ia[2],_ic=E(_ia[1]);switch(_ic){case 37:var _id=new T(function(){return B(_cK(_h4,_ib,_h6));}),_ie=function(_if){var _ig=E(_if);return (_ig[0]==0)?E(_id):[1,new T(function(){return B(_gX(_ig[1]));}),new T(function(){return B(_ie(_ig[2]));})];};return new F(function(){return _ie(_gT);});break;case 110:var _ih=new T(function(){return B(_cK(_h4,_ib,_h6));}),_ii=function(_ij){var _ik=E(_ij);return (_ik[0]==0)?E(_ih):[1,new T(function(){return B(_gX(_ik[1]));}),new T(function(){return B(_ii(_ik[2]));})];};return new F(function(){return _ii(_gS);});break;case 116:var _il=new T(function(){return B(_cK(_h4,_ib,_h6));}),_im=function(_in){var _io=E(_in);return (_io[0]==0)?E(_il):[1,new T(function(){return B(_gX(_io[1]));}),new T(function(){return B(_im(_io[2]));})];};return new F(function(){return _im(_gR);});break;default:var _ip=function(_iq){var _ir=new T(function(){return B(_cK(_h4,_ib,_h6));}),_is=function(_it){var _iu=E(_it);return (_iu[0]==0)?E(_ir):[1,new T(function(){return B(_gX(_iu[1]));}),new T(function(){return B(_is(_iu[2]));})];};return new F(function(){return _is(B(A(_iq,[_h4,_2s,_h6])));});};switch(E(_ic)){case 72:return new F(function(){return _ip(_gI);});break;case 73:return new F(function(){return _ip(_gA);});break;case 77:return new F(function(){return _ip(_gr);});break;case 80:return new F(function(){return _ip(_gi);});break;case 81:return new F(function(){return _ip(_g1);});break;case 82:return new F(function(){return _ip(_fV);});break;case 83:return new F(function(){return _ip(_fR);});break;case 84:return new F(function(){return _ip(_cL);});break;case 88:return new F(function(){return _ip(_cF);});break;case 107:return new F(function(){return _ip(_cB);});break;case 108:return new F(function(){return _ip(_ct);});break;case 112:return new F(function(){return _ip(_aG);});break;case 113:return new F(function(){return _ip(_aC);});break;case 114:return new F(function(){return _ip(_gM);});break;default:var _hK=_h4,_hL=_h6;_h0=_hK;_h1=_ib;_h2=_hL;return null;}}}break;case 95:var _iv=E(_hb);if(!_iv[0]){return new F(function(){return _hd(_);});}else{var _iw=_iv[2];switch(E(_iv[1])){case 37:return new F(function(){return _4(_gT,new T(function(){return B(_cK(_h4,_iw,_h6));},1));});break;case 72:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_bW,_aL,new T(function(){return E(E(_h6)[1]);}))),new T(function(){return B(_cK(_h4,_iw,_h6));},1));});break;case 73:return new F(function(){return _4(B(_gv(_gU,_h6)),new T(function(){return B(_cK(_h4,_iw,_h6));},1));});break;case 77:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_bW,_aL,new T(function(){return E(E(_h6)[2]);}))),new T(function(){return B(_cK(_h4,_iw,_h6));},1));});break;case 80:var _ix=E(_h4),_iy=E(_ix[3]),_iz=E(_h6);if(E(_iz[1])>=12){return new F(function(){return _4(B(_g5(_gb,_iy[2])),new T(function(){return B(_cK(_ix,_iw,_iz));},1));});}else{return new F(function(){return _4(B(_g5(_gb,_iy[1])),new T(function(){return B(_cK(_ix,_iw,_iz));},1));});}break;case 81:var _iA=E(_h6);return new F(function(){return _4(B(_90(_78,B(_ac(_3i,_fY,_iA[3])))),new T(function(){return B(_cK(_h4,_iw,_iA));},1));});break;case 82:return new F(function(){return _4(B(_cK(_h4,_8Q,_h6)),new T(function(){return B(_cK(_h4,_iw,_h6));},1));});break;case 83:return new F(function(){return _4(B(_fL(_gU,_h6)),new T(function(){return B(_cK(_h4,_iw,_h6));},1));});break;case 84:return new F(function(){return _4(B(_cK(_h4,_8P,_h6)),new T(function(){return B(_cK(_h4,_iw,_h6));},1));});break;case 88:var _iB=E(_h4);return new F(function(){return _4(B(_cK(_iB,_iB[6],_h6)),new T(function(){return B(_cK(_iB,_iw,_h6));},1));});break;case 107:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_bW,_aL,new T(function(){return E(E(_h6)[1]);}))),new T(function(){return B(_cK(_h4,_iw,_h6));},1));});break;case 108:return new F(function(){return _4(B(_co(_gU,_h6)),new T(function(){return B(_cK(_h4,_iw,_h6));},1));});break;case 110:return new F(function(){return _4(_gS,new T(function(){return B(_cK(_h4,_iw,_h6));},1));});break;case 112:var _iC=E(_h6);if(E(_iC[1])>=12){var _iD=E(_h4);return new F(function(){return _4(E(_iD[3])[2],new T(function(){return B(_cK(_iD,_iw,_iC));},1));});}else{var _iE=E(_h4);return new F(function(){return _4(E(_iE[3])[1],new T(function(){return B(_cK(_iE,_iw,_iC));},1));});}break;case 113:var _iF=E(_h6);return new F(function(){return _4(B(_aA(_iF[3])),new T(function(){return B(_cK(_h4,_iw,_iF));},1));});break;case 114:var _iG=E(_h4);return new F(function(){return _4(B(_cK(_iG,_iG[7],_h6)),new T(function(){return B(_cK(_iG,_iw,_h6));},1));});break;case 116:return new F(function(){return _4(_gR,new T(function(){return B(_cK(_h4,_iw,_h6));},1));});break;default:var _hK=_h4,_hL=_h6;_h0=_hK;_h1=_iw;_h2=_hL;return null;}}break;default:return new F(function(){return _hd(_);});}}}else{return [1,_h9,new T(function(){return B(_cK(_h4,_h8,_h6));})];}}})(_h0,_h1,_h2));if(_h3!=null){return _h3;}}},_iH=[0,0],_iI=[0,100],_iJ=new T(function(){return B(_6G(_iI,_iH));}),_iK=function(_iL){return E(_iL);},_iM=[0,_8c,_7O,_6O,_a8,_eU,_fg,_iK],_iN=function(_iO,_iP){var _iQ=E(_iO);if(!_iQ[0]){var _iR=_iQ[1],_iS=E(_iP);return (_iS[0]==0)?_iR!=_iS[1]:(I_compareInt(_iS[1],_iR)==0)?false:true;}else{var _iT=_iQ[1],_iU=E(_iP);return (_iU[0]==0)?(I_compareInt(_iT,_iU[1])==0)?false:true:(I_compare(_iT,_iU[1])==0)?false:true;}},_iV=[0,_6G,_iN],_iW=function(_iX,_iY){return (!B(_7x(_iX,_iY)))?E(_iX):E(_iY);},_iZ=function(_j0,_j1){return (!B(_7x(_j0,_j1)))?E(_j1):E(_j0);},_j2=function(_j3,_j4){var _j5=E(_j3);if(!_j5[0]){var _j6=_j5[1],_j7=E(_j4);if(!_j7[0]){var _j8=_j7[1];return (_j6!=_j8)?(_j6>_j8)?2:0:1;}else{var _j9=I_compareInt(_j7[1],_j6);return (_j9<=0)?(_j9>=0)?1:2:0;}}else{var _ja=_j5[1],_jb=E(_j4);if(!_jb[0]){var _jc=I_compareInt(_ja,_jb[1]);return (_jc>=0)?(_jc<=0)?1:2:0;}else{var _jd=I_compare(_ja,_jb[1]);return (_jd>=0)?(_jd<=0)?1:2:0;}}},_je=function(_jf,_jg){var _jh=E(_jf);if(!_jh[0]){var _ji=_jh[1],_jj=E(_jg);return (_jj[0]==0)?_ji>=_jj[1]:I_compareInt(_jj[1],_ji)<=0;}else{var _jk=_jh[1],_jl=E(_jg);return (_jl[0]==0)?I_compareInt(_jk,_jl[1])>=0:I_compare(_jk,_jl[1])>=0;}},_jm=function(_jn,_jo){var _jp=E(_jn);if(!_jp[0]){var _jq=_jp[1],_jr=E(_jo);return (_jr[0]==0)?_jq>_jr[1]:I_compareInt(_jr[1],_jq)<0;}else{var _js=_jp[1],_jt=E(_jo);return (_jt[0]==0)?I_compareInt(_js,_jt[1])>0:I_compare(_js,_jt[1])>0;}},_ju=[0,_iV,_j2,_9d,_7x,_jm,_je,_iW,_iZ],_jv=function(_jw,_jx){var _jy=E(_jw);if(!_jy[0]){return new F(function(){return unAppCStr("[]",_jx);});}else{var _jz=new T(function(){var _jA=new T(function(){var _jB=function(_jC){var _jD=E(_jC);if(!_jD[0]){return [1,_28,_jx];}else{var _jE=new T(function(){return B(_9m(0,_jD[1],new T(function(){return B(_jB(_jD[2]));})));});return [1,_27,_jE];}};return B(_jB(_jy[2]));});return B(_9m(0,_jy[1],_jA));});return [1,_29,_jz];}},_jF=function(_jG,_jH,_jI){return new F(function(){return _9m(E(_jG),_jH,_jI);});},_jJ=[0,_jF,_9L,_jv],_jK=function(_jL,_jM){var _jN=new T(function(){if(!E(_iJ)){return B(_84(B(_8m(_jM))[1],_iI));}else{return E(_6F);}}),_jO=E(_jL);if(!_jO[0]){return new F(function(){return _ce(_iM,_ju,_jJ,_bW,_cQ,_jN);});}else{return new F(function(){return _ce(_iM,_ju,_jJ,_bW,_jO[1],_jN);});}},_jP=function(_jQ,_jR,_jS){return new F(function(){return _jK(_jR,_jS);});},_jT=function(_jU,_jV,_jW){var _jX=E(_jU);return new F(function(){return _jY(_jX,_jX[5],_jW);});},_jZ=function(_k0,_k1,_k2){return new F(function(){return _e(0,E(B(_8A(_k2))[2]),_w);});},_k3=[0,366],_k4=[0,678576],_k5=new T(function(){return B(_6G(_7u,_7J));}),_k6=new T(function(){return B(_6G(_7v,_7J));}),_k7=new T(function(){return B(_6G(_7w,_7J));}),_k8=function(_k9){return (!E(_k7))?(!B(_6G(B(_84(_k9,_7w)),_7J)))?false:(!E(_k6))?(!B(_6G(B(_84(_k9,_7v)),_7J)))?(!E(_k5))?(!B(_6G(B(_84(_k9,_7u)),_7J)))?true:false:E(_6F):true:E(_6F):E(_6F);},_ka=function(_kb,_kc){if(!E(_k7)){if(!E(_k5)){if(!E(_k6)){var _kd=B(_7O(_kb,_7p));if(_kc>=1){if(!B(_k8(_kb))){if(_kc<=365){return new F(function(){return _7O(B(_8c(B(_7O(B(_8c(B(_8c(B(_8y(_kc)),B(_6O(_7q,_kd)))),B(_5Y(_kd,_7w)))),B(_5Y(_kd,_7u)))),B(_5Y(_kd,_7v)))),_k4);});}else{return new F(function(){return _7O(B(_8c(B(_7O(B(_8c(B(_8c(_7q,B(_6O(_7q,_kd)))),B(_5Y(_kd,_7w)))),B(_5Y(_kd,_7u)))),B(_5Y(_kd,_7v)))),_k4);});}}else{if(_kc<=366){return new F(function(){return _7O(B(_8c(B(_7O(B(_8c(B(_8c(B(_8y(_kc)),B(_6O(_7q,_kd)))),B(_5Y(_kd,_7w)))),B(_5Y(_kd,_7u)))),B(_5Y(_kd,_7v)))),_k4);});}else{return new F(function(){return _7O(B(_8c(B(_7O(B(_8c(B(_8c(_k3,B(_6O(_7q,_kd)))),B(_5Y(_kd,_7w)))),B(_5Y(_kd,_7u)))),B(_5Y(_kd,_7v)))),_k4);});}}}else{return new F(function(){return _7O(B(_8c(B(_7O(B(_8c(B(_8c(_7p,B(_6O(_7q,_kd)))),B(_5Y(_kd,_7w)))),B(_5Y(_kd,_7u)))),B(_5Y(_kd,_7v)))),_k4);});}}else{return E(_6F);}}else{return E(_6F);}}else{return E(_6F);}},_ke=[0,7],_kf=[0,0],_kg=new T(function(){return B(_6G(_ke,_kf));}),_kh=[0,2],_ki=[0,4],_kj=[0,52],_kk=[0,1],_kl=[0,-1],_km=function(_kn){var _ko=new T(function(){return B(_8c(_kn,_kh));}),_kp=new T(function(){if(!E(_kg)){var _kq=B(_9R(_ko,_ke));return [0,_kq[1],_kq[2]];}else{return E(_6F);}}),_kr=new T(function(){var _ks=E(_kp)[1],_kt=B(_8m(_kn)),_ku=_kt[1];if(!E(_kg)){var _kv=B(_7O(_ks,B(_5Y(B(_8c(B(_7O(_ko,B(_8y(E(_kt[2]))))),_ki)),_ke))));}else{var _kv=E(_6F);}if(!B(_6G(_kv,_kl))){if(!B(_6G(_kv,_kj))){return [0,_ku,_kv];}else{if(!E(_kg)){if(!B(_6G(B(_7O(_ks,B(_5Y(B(_ka(B(_8c(_ku,_kk)),6)),_ke)))),_kf))){return [0,_ku,_kj];}else{return [0,new T(function(){return B(_8c(_ku,_kk));}),_kf];}}else{return E(_6F);}}}else{return [0,new T(function(){return B(_7O(_ku,_kk));}),new T(function(){if(!E(_kg)){return B(_7O(_ks,B(_5Y(B(_ka(B(_7O(_ku,_kk)),6)),_ke))));}else{return E(_6F);}})];}});return [0,new T(function(){return E(E(_kr)[1]);}),new T(function(){return B(_7r(B(_8c(E(_kr)[2],_kk))));}),new T(function(){return B(_7r(E(_kp)[2]))+1|0;})];},_kw=function(_kx,_ky,_kz){return new F(function(){return _e(0,E(B(_km(_kz))[3]),_w);});},_kA=1,_kB=function(_kC,_kD){var _kE=E(_kC);if(!_kE[0]){return [0,_kA,_kD];}else{var _kF=E(_kD),_kG=E(_kE[1]);if(_kF<=_kG){return [0,_kA,_kF];}else{var _kH=B(_kB(_kE[2],_kF-_kG|0));return [0,new T(function(){return E(_kH[1])+1|0;}),_kH[2]];}}},_kI=366,_kJ=365,_kK=31,_kL=29,_kM=28,_kN=30,_kO=[1,_kK,_w],_kP=[1,_kN,_kO],_kQ=[1,_kK,_kP],_kR=[1,_kN,_kQ],_kS=[1,_kK,_kR],_kT=[1,_kK,_kS],_kU=[1,_kN,_kT],_kV=[1,_kK,_kU],_kW=[1,_kN,_kV],_kX=[1,_kK,_kW],_kY=function(_kZ){return [1,_kK,[1,new T(function(){if(!E(_kZ)){return E(_kM);}else{return E(_kL);}}),_kX]];},_l0=function(_l1,_l2){return new F(function(){return _kB(B(_kY(_l1)),new T(function(){var _l3=E(_l2);if(_l3>=1){if(!E(_l1)){if(_l3<=365){return E(_l3);}else{return E(_kJ);}}else{if(_l3<=366){return E(_l3);}else{return E(_kI);}}}else{return E(_kA);}}));});},_l4=function(_l5){var _l6=new T(function(){var _l7=B(_8m(_l5));return [0,_l7[1],_l7[2]];}),_l8=new T(function(){return E(E(_l6)[1]);}),_l9=new T(function(){var _la=B(_l0(new T(function(){return B(_k8(_l8));}),new T(function(){return E(E(_l6)[2]);},1)));return [0,_la[1],_la[2]];});return [0,_l8,new T(function(){return E(E(_l9)[1]);}),new T(function(){return E(E(_l9)[2]);})];},_lb=function(_lc,_ld){var _le=E(_lc);if(!_le[0]){return new F(function(){return _ce(_b8,_bI,_bV,_bW,_cQ,new T(function(){return E(B(_l4(_ld))[2]);}));});}else{return new F(function(){return _ce(_b8,_bI,_bV,_bW,_le[1],new T(function(){return E(B(_l4(_ld))[2]);}));});}},_lf=function(_lg,_lh,_li){return new F(function(){return _lb(_lh,_li);});},_lj=3,_lk=function(_ll,_lm){var _ln=E(_ll);if(!_ln[0]){return new F(function(){return _ce(_b8,_bI,_bV,_lj,_cQ,new T(function(){return E(B(_8m(_lm))[2]);}));});}else{return new F(function(){return _ce(_b8,_bI,_bV,_lj,_ln[1],new T(function(){return E(B(_8m(_lm))[2]);}));});}},_lo=function(_lp,_lq,_lr){return new F(function(){return _lk(_lq,_lr);});},_ls=function(_lt,_lu){return E(B(_7m(_lt,E(B(_l4(_lu))[2])-1|0))[2]);},_lv=function(_lw,_lx,_ly){return new F(function(){return _ls(E(_lw)[2],_ly);});},_lz=function(_lA,_lB){var _lC=new T(function(){if(!E(_iJ)){return B(_84(B(_km(_lB))[1],_iI));}else{return E(_6F);}}),_lD=E(_lA);if(!_lD[0]){return new F(function(){return _ce(_iM,_ju,_jJ,_bW,_cQ,_lC);});}else{return new F(function(){return _ce(_iM,_ju,_jJ,_bW,_lD[1],_lC);});}},_lE=function(_lF,_lG,_lH){return new F(function(){return _lz(_lG,_lH);});},_lI=function(_lJ,_lK){var _lL=new T(function(){if(!E(_iJ)){return B(_5Y(B(_km(_lK))[1],_iI));}else{return E(_6F);}}),_lM=E(_lJ);if(!_lM[0]){return new F(function(){return _ce(_iM,_ju,_jJ,_bW,_2s,_lL);});}else{return new F(function(){return _ce(_iM,_ju,_jJ,_bW,_lM[1],_lL);});}},_lN=function(_lO,_lP,_lQ){return new F(function(){return _lI(_lP,_lQ);});},_lR=function(_lS,_lT){var _lU=E(_lS);if(!_lU[0]){return new F(function(){return _ce(_b8,_bI,_bV,_bW,_aL,new T(function(){return E(B(_l4(_lT))[3]);}));});}else{return new F(function(){return _ce(_b8,_bI,_bV,_bW,_lU[1],new T(function(){return E(B(_l4(_lT))[3]);}));});}},_lV=function(_lW,_lX,_lY){return new F(function(){return _lR(_lX,_lY);});},_lZ=function(_m0,_m1){var _m2=E(_m0);if(!_m2[0]){return new F(function(){return _ce(_b8,_bI,_bV,_bW,_cQ,new T(function(){return E(B(_l4(_m1))[3]);}));});}else{return new F(function(){return _ce(_b8,_bI,_bV,_bW,_m2[1],new T(function(){return E(B(_l4(_m1))[3]);}));});}},_m3=function(_m4,_m5,_m6){return new F(function(){return _lZ(_m5,_m6);});},_m7=function(_m8,_m9){return E(B(_7m(_m8,E(B(_l4(_m9))[2])-1|0))[2]);},_ma=function(_mb,_mc,_md){return new F(function(){return _m7(E(_mb)[2],_md);});},_me=function(_mf,_mg,_mh){return E(B(_7m(B(_8F(_mf)),E(B(_8A(_mh))[2])))[2]);},_mi=4,_mj=function(_mk,_ml){var _mm=E(_mk);if(!_mm[0]){return new F(function(){return _ce(_iM,_ju,_jJ,_mi,_2s,new T(function(){return E(B(_8m(_ml))[1]);}));});}else{return new F(function(){return _ce(_iM,_ju,_jJ,_mi,_mm[1],new T(function(){return E(B(_8m(_ml))[1]);}));});}},_mn=function(_mo,_mp,_mq){return new F(function(){return _mj(_mp,_mq);});},_mr=[0,2],_ms=function(_mt){var _mu=new T(function(){return B(_8c(_mt,_mr));});return [0,new T(function(){if(!E(_8x)){return B(_7r(B(_7O(B(_5Y(_mu,_8w)),B(_5Y(B(_7O(_mu,B(_8y(E(B(_8m(_mt))[2]))))),_8w))))));}else{return E(_6F);}}),new T(function(){if(!E(_8x)){return B(_7r(B(_84(_mu,_8w))))+1|0;}else{return E(_6F);}})];},_mv=function(_mw,_mx){var _my=E(_mw);if(!_my[0]){return new F(function(){return _ce(_b8,_bI,_bV,_bW,_cQ,new T(function(){return E(B(_ms(_mx))[1]);}));});}else{return new F(function(){return _ce(_b8,_bI,_bV,_bW,_my[1],new T(function(){return E(B(_ms(_mx))[1]);}));});}},_mz=function(_mA,_mB,_mC){return new F(function(){return _mv(_mB,_mC);});},_mD=function(_mE,_mF){var _mG=E(_mE);if(!_mG[0]){return new F(function(){return _ce(_b8,_bI,_bV,_bW,_cQ,new T(function(){return E(B(_km(_mF))[2]);}));});}else{return new F(function(){return _ce(_b8,_bI,_bV,_bW,_mG[1],new T(function(){return E(B(_km(_mF))[2]);}));});}},_mH=function(_mI,_mJ,_mK){return new F(function(){return _mD(_mJ,_mK);});},_mL=function(_mM,_mN){var _mO=E(_mM);if(!_mO[0]){return new F(function(){return _ce(_b8,_bI,_bV,_bW,_cQ,new T(function(){return E(B(_8A(_mN))[1]);}));});}else{return new F(function(){return _ce(_b8,_bI,_bV,_bW,_mO[1],new T(function(){return E(B(_8A(_mN))[1]);}));});}},_mP=function(_mQ,_mR,_mS){return new F(function(){return _mL(_mR,_mS);});},_mT=function(_mU,_mV){var _mW=E(_mU);if(!_mW[0]){return new F(function(){return _ce(_iM,_ju,_jJ,_mi,_2s,new T(function(){return E(B(_km(_mV))[1]);}));});}else{return new F(function(){return _ce(_iM,_ju,_jJ,_mi,_mW[1],new T(function(){return E(B(_km(_mV))[1]);}));});}},_mX=function(_mY,_mZ,_n0){return new F(function(){return _mT(_mZ,_n0);});},_n1=function(_n2,_n3,_cO){return new F(function(){return _jY(_n2,_8R,_cO);});},_n4=function(_n5,_n6,_cO){return new F(function(){return _jY(_n5,_8S,_cO);});},_n7=function(_n8,_n9){var _na=new T(function(){if(!E(_iJ)){return B(_5Y(B(_8m(_n9))[1],_iI));}else{return E(_6F);}}),_nb=E(_n8);if(!_nb[0]){return new F(function(){return _ce(_iM,_ju,_jJ,_bW,_2s,_na);});}else{return new F(function(){return _ce(_iM,_ju,_jJ,_bW,_nb[1],_na);});}},_nc=function(_nd,_ne,_nf){return new F(function(){return _n7(_ne,_nf);});},_ng=function(_nh,_ni){return E(B(_7m(_nh,E(B(_l4(_ni))[2])-1|0))[1]);},_nj=function(_nk,_nl,_nm){return new F(function(){return _ng(E(_nk)[2],_nm);});},_nn=function(_no,_np,_nq){return E(B(_7m(B(_8F(_no)),E(B(_8A(_nq))[2])))[1]);},_jY=function(_nr,_ns,_nt){while(1){var _nu=B((function(_nv,_nw,_nx){var _ny=E(_nw);if(!_ny[0]){return [0];}else{var _nz=_ny[2],_nA=E(_ny[1]);if(E(_nA)==37){var _nB=E(_nz);if(!_nB[0]){return [1,_nA,new T(function(){return B(_jY(_nv,_w,_nx));})];}else{var _nC=_nB[2],_nD=E(_nB[1]),_nE=function(_nF){switch(E(_nD)){case 37:return new F(function(){return _4(_gT,new T(function(){return B(_jY(_nv,_nC,_nx));},1));});break;case 65:return new F(function(){return _4(B(_7m(B(_8F(_nv)),E(B(_8A(_nx))[2])))[1],new T(function(){return B(_jY(_nv,_nC,_nx));},1));});break;case 66:var _nG=E(_nv);return new F(function(){return _4(B(_7m(_nG[2],E(B(_l4(_nx))[2])-1|0))[1],new T(function(){return B(_jY(_nG,_nC,_nx));},1));});break;case 67:return new F(function(){return _4(B(_n7(_2s,_nx)),new T(function(){return B(_jY(_nv,_nC,_nx));},1));});break;case 68:return new F(function(){return _4(B(_jY(_nv,_8S,_nx)),new T(function(){return B(_jY(_nv,_nC,_nx));},1));});break;case 70:return new F(function(){return _4(B(_jY(_nv,_8R,_nx)),new T(function(){return B(_jY(_nv,_nC,_nx));},1));});break;case 71:return new F(function(){return _4(B(_ce(_iM,_ju,_jJ,_mi,_2s,new T(function(){return E(B(_km(_nx))[1]);}))),new T(function(){return B(_jY(_nv,_nC,_nx));},1));});break;case 85:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_bW,_cQ,new T(function(){return E(B(_8A(_nx))[1]);}))),new T(function(){return B(_jY(_nv,_nC,_nx));},1));});break;case 86:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_bW,_cQ,new T(function(){return E(B(_km(_nx))[2]);}))),new T(function(){return B(_jY(_nv,_nC,_nx));},1));});break;case 87:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_bW,_cQ,new T(function(){return E(B(_ms(_nx))[1]);}))),new T(function(){return B(_jY(_nv,_nC,_nx));},1));});break;case 89:return new F(function(){return _4(B(_ce(_iM,_ju,_jJ,_mi,_2s,new T(function(){return E(B(_8m(_nx))[1]);}))),new T(function(){return B(_jY(_nv,_nC,_nx));},1));});break;case 97:return new F(function(){return _4(B(_7m(B(_8F(_nv)),E(B(_8A(_nx))[2])))[2],new T(function(){return B(_jY(_nv,_nC,_nx));},1));});break;case 98:var _nH=E(_nv);return new F(function(){return _4(B(_7m(_nH[2],E(B(_l4(_nx))[2])-1|0))[2],new T(function(){return B(_jY(_nH,_nC,_nx));},1));});break;case 100:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_bW,_cQ,new T(function(){return E(B(_l4(_nx))[3]);}))),new T(function(){return B(_jY(_nv,_nC,_nx));},1));});break;case 101:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_bW,_aL,new T(function(){return E(B(_l4(_nx))[3]);}))),new T(function(){return B(_jY(_nv,_nC,_nx));},1));});break;case 102:return new F(function(){return _4(B(_lI(_2s,_nx)),new T(function(){return B(_jY(_nv,_nC,_nx));},1));});break;case 103:return new F(function(){return _4(B(_lz(_2s,_nx)),new T(function(){return B(_jY(_nv,_nC,_nx));},1));});break;case 104:var _nI=E(_nv);return new F(function(){return _4(B(_7m(_nI[2],E(B(_l4(_nx))[2])-1|0))[2],new T(function(){return B(_jY(_nI,_nC,_nx));},1));});break;case 106:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_lj,_cQ,new T(function(){return E(B(_8m(_nx))[2]);}))),new T(function(){return B(_jY(_nv,_nC,_nx));},1));});break;case 109:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_bW,_cQ,new T(function(){return E(B(_l4(_nx))[2]);}))),new T(function(){return B(_jY(_nv,_nC,_nx));},1));});break;case 110:return new F(function(){return _4(_gS,new T(function(){return B(_jY(_nv,_nC,_nx));},1));});break;case 116:return new F(function(){return _4(_gR,new T(function(){return B(_jY(_nv,_nC,_nx));},1));});break;case 117:return new F(function(){return _4(B(_e(0,E(B(_km(_nx))[3]),_w)),new T(function(){return B(_jY(_nv,_nC,_nx));},1));});break;case 119:return new F(function(){return _4(B(_e(0,E(B(_8A(_nx))[2]),_w)),new T(function(){return B(_jY(_nv,_nC,_nx));},1));});break;case 120:var _nJ=E(_nv);return new F(function(){return _4(B(_jY(_nJ,_nJ[5],_nx)),new T(function(){return B(_jY(_nJ,_nC,_nx));},1));});break;case 121:return new F(function(){return _4(B(_jK(_2s,_nx)),new T(function(){return B(_jY(_nv,_nC,_nx));},1));});break;default:return new F(function(){return _jY(_nv,_nC,_nx);});}};switch(E(_nD)){case 35:var _nK=E(_nC);if(!_nK[0]){return new F(function(){return _nE(_);});}else{var _nL=_nK[2],_nM=E(_nK[1]);switch(_nM){case 37:var _nN=new T(function(){return B(_jY(_nv,_nL,_nx));}),_nO=function(_nP){var _nQ=E(_nP);return (_nQ[0]==0)?E(_nN):[1,new T(function(){return B(_gb(_nQ[1]));}),new T(function(){return B(_nO(_nQ[2]));})];};return new F(function(){return _nO(_gT);});break;case 110:var _nR=new T(function(){return B(_jY(_nv,_nL,_nx));}),_nS=function(_nT){var _nU=E(_nT);return (_nU[0]==0)?E(_nR):[1,new T(function(){return B(_gb(_nU[1]));}),new T(function(){return B(_nS(_nU[2]));})];};return new F(function(){return _nS(_gS);});break;case 116:var _nV=new T(function(){return B(_jY(_nv,_nL,_nx));}),_nW=function(_nX){var _nY=E(_nX);return (_nY[0]==0)?E(_nV):[1,new T(function(){return B(_gb(_nY[1]));}),new T(function(){return B(_nW(_nY[2]));})];};return new F(function(){return _nW(_gR);});break;default:var _nZ=function(_o0){var _o1=new T(function(){return B(_jY(_nv,_nL,_nx));}),_o2=function(_o3){var _o4=E(_o3);return (_o4[0]==0)?E(_o1):[1,new T(function(){return B(_gb(_o4[1]));}),new T(function(){return B(_o2(_o4[2]));})];};return new F(function(){return _o2(B(A(_o0,[_nv,_2s,_nx])));});};switch(E(_nM)){case 65:return new F(function(){return _nZ(_nn);});break;case 66:return new F(function(){return _nZ(_nj);});break;case 67:return new F(function(){return _nZ(_nc);});break;case 68:return new F(function(){return _nZ(_n4);});break;case 70:return new F(function(){return _nZ(_n1);});break;case 71:return new F(function(){return _nZ(_mX);});break;case 85:return new F(function(){return _nZ(_mP);});break;case 86:return new F(function(){return _nZ(_mH);});break;case 87:return new F(function(){return _nZ(_mz);});break;case 89:return new F(function(){return _nZ(_mn);});break;case 97:return new F(function(){return _nZ(_me);});break;case 98:return new F(function(){return _nZ(_ma);});break;case 100:return new F(function(){return _nZ(_m3);});break;case 101:return new F(function(){return _nZ(_lV);});break;case 102:return new F(function(){return _nZ(_lN);});break;case 103:return new F(function(){return _nZ(_lE);});break;case 104:return new F(function(){return _nZ(_lv);});break;case 106:return new F(function(){return _nZ(_lo);});break;case 109:return new F(function(){return _nZ(_lf);});break;case 117:return new F(function(){return _nZ(_kw);});break;case 119:return new F(function(){return _nZ(_jZ);});break;case 120:return new F(function(){return _nZ(_jT);});break;case 121:return new F(function(){return _nZ(_jP);});break;default:var _o5=_nv,_o6=_nx;_nr=_o5;_ns=_nL;_nt=_o6;return null;}}}break;case 45:var _o7=E(_nC);if(!_o7[0]){return new F(function(){return _nE(_);});}else{var _o8=_o7[2];switch(E(_o7[1])){case 37:return new F(function(){return _4(_gT,new T(function(){return B(_jY(_nv,_o8,_nx));},1));});break;case 65:return new F(function(){return _4(B(_7m(B(_8F(_nv)),E(B(_8A(_nx))[2])))[1],new T(function(){return B(_jY(_nv,_o8,_nx));},1));});break;case 66:var _o9=E(_nv);return new F(function(){return _4(B(_7m(_o9[2],E(B(_l4(_nx))[2])-1|0))[1],new T(function(){return B(_jY(_o9,_o8,_nx));},1));});break;case 67:return new F(function(){return _4(B(_n7(_gW,_nx)),new T(function(){return B(_jY(_nv,_o8,_nx));},1));});break;case 68:return new F(function(){return _4(B(_jY(_nv,_8S,_nx)),new T(function(){return B(_jY(_nv,_o8,_nx));},1));});break;case 70:return new F(function(){return _4(B(_jY(_nv,_8R,_nx)),new T(function(){return B(_jY(_nv,_o8,_nx));},1));});break;case 71:return new F(function(){return _4(B(_ce(_iM,_ju,_jJ,_mi,_2s,new T(function(){return E(B(_km(_nx))[1]);}))),new T(function(){return B(_jY(_nv,_o8,_nx));},1));});break;case 85:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_bW,_2s,new T(function(){return E(B(_8A(_nx))[1]);}))),new T(function(){return B(_jY(_nv,_o8,_nx));},1));});break;case 86:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_bW,_2s,new T(function(){return E(B(_km(_nx))[2]);}))),new T(function(){return B(_jY(_nv,_o8,_nx));},1));});break;case 87:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_bW,_2s,new T(function(){return E(B(_ms(_nx))[1]);}))),new T(function(){return B(_jY(_nv,_o8,_nx));},1));});break;case 89:return new F(function(){return _4(B(_ce(_iM,_ju,_jJ,_mi,_2s,new T(function(){return E(B(_8m(_nx))[1]);}))),new T(function(){return B(_jY(_nv,_o8,_nx));},1));});break;case 97:return new F(function(){return _4(B(_7m(B(_8F(_nv)),E(B(_8A(_nx))[2])))[2],new T(function(){return B(_jY(_nv,_o8,_nx));},1));});break;case 98:var _oa=E(_nv);return new F(function(){return _4(B(_7m(_oa[2],E(B(_l4(_nx))[2])-1|0))[2],new T(function(){return B(_jY(_oa,_o8,_nx));},1));});break;case 100:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_bW,_2s,new T(function(){return E(B(_l4(_nx))[3]);}))),new T(function(){return B(_jY(_nv,_o8,_nx));},1));});break;case 101:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_bW,_2s,new T(function(){return E(B(_l4(_nx))[3]);}))),new T(function(){return B(_jY(_nv,_o8,_nx));},1));});break;case 102:return new F(function(){return _4(B(_lI(_gW,_nx)),new T(function(){return B(_jY(_nv,_o8,_nx));},1));});break;case 103:return new F(function(){return _4(B(_lz(_gW,_nx)),new T(function(){return B(_jY(_nv,_o8,_nx));},1));});break;case 104:var _ob=E(_nv);return new F(function(){return _4(B(_7m(_ob[2],E(B(_l4(_nx))[2])-1|0))[2],new T(function(){return B(_jY(_ob,_o8,_nx));},1));});break;case 106:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_lj,_2s,new T(function(){return E(B(_8m(_nx))[2]);}))),new T(function(){return B(_jY(_nv,_o8,_nx));},1));});break;case 109:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_bW,_2s,new T(function(){return E(B(_l4(_nx))[2]);}))),new T(function(){return B(_jY(_nv,_o8,_nx));},1));});break;case 110:return new F(function(){return _4(_gS,new T(function(){return B(_jY(_nv,_o8,_nx));},1));});break;case 116:return new F(function(){return _4(_gR,new T(function(){return B(_jY(_nv,_o8,_nx));},1));});break;case 117:return new F(function(){return _4(B(_e(0,E(B(_km(_nx))[3]),_w)),new T(function(){return B(_jY(_nv,_o8,_nx));},1));});break;case 119:return new F(function(){return _4(B(_e(0,E(B(_8A(_nx))[2]),_w)),new T(function(){return B(_jY(_nv,_o8,_nx));},1));});break;case 120:var _oc=E(_nv);return new F(function(){return _4(B(_jY(_oc,_oc[5],_nx)),new T(function(){return B(_jY(_oc,_o8,_nx));},1));});break;case 121:return new F(function(){return _4(B(_jK(_gW,_nx)),new T(function(){return B(_jY(_nv,_o8,_nx));},1));});break;default:var _o5=_nv,_o6=_nx;_nr=_o5;_ns=_o8;_nt=_o6;return null;}}break;case 48:var _od=E(_nC);if(!_od[0]){return new F(function(){return _nE(_);});}else{var _oe=_od[2];switch(E(_od[1])){case 37:return new F(function(){return _4(_gT,new T(function(){return B(_jY(_nv,_oe,_nx));},1));});break;case 65:return new F(function(){return _4(B(_7m(B(_8F(_nv)),E(B(_8A(_nx))[2])))[1],new T(function(){return B(_jY(_nv,_oe,_nx));},1));});break;case 66:var _of=E(_nv);return new F(function(){return _4(B(_7m(_of[2],E(B(_l4(_nx))[2])-1|0))[1],new T(function(){return B(_jY(_of,_oe,_nx));},1));});break;case 67:return new F(function(){return _4(B(_n7(_gV,_nx)),new T(function(){return B(_jY(_nv,_oe,_nx));},1));});break;case 68:return new F(function(){return _4(B(_jY(_nv,_8S,_nx)),new T(function(){return B(_jY(_nv,_oe,_nx));},1));});break;case 70:return new F(function(){return _4(B(_jY(_nv,_8R,_nx)),new T(function(){return B(_jY(_nv,_oe,_nx));},1));});break;case 71:return new F(function(){return _4(B(_ce(_iM,_ju,_jJ,_mi,_cQ,new T(function(){return E(B(_km(_nx))[1]);}))),new T(function(){return B(_jY(_nv,_oe,_nx));},1));});break;case 85:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_bW,_cQ,new T(function(){return E(B(_8A(_nx))[1]);}))),new T(function(){return B(_jY(_nv,_oe,_nx));},1));});break;case 86:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_bW,_cQ,new T(function(){return E(B(_km(_nx))[2]);}))),new T(function(){return B(_jY(_nv,_oe,_nx));},1));});break;case 87:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_bW,_cQ,new T(function(){return E(B(_ms(_nx))[1]);}))),new T(function(){return B(_jY(_nv,_oe,_nx));},1));});break;case 89:return new F(function(){return _4(B(_ce(_iM,_ju,_jJ,_mi,_cQ,new T(function(){return E(B(_8m(_nx))[1]);}))),new T(function(){return B(_jY(_nv,_oe,_nx));},1));});break;case 97:return new F(function(){return _4(B(_7m(B(_8F(_nv)),E(B(_8A(_nx))[2])))[2],new T(function(){return B(_jY(_nv,_oe,_nx));},1));});break;case 98:var _og=E(_nv);return new F(function(){return _4(B(_7m(_og[2],E(B(_l4(_nx))[2])-1|0))[2],new T(function(){return B(_jY(_og,_oe,_nx));},1));});break;case 100:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_bW,_cQ,new T(function(){return E(B(_l4(_nx))[3]);}))),new T(function(){return B(_jY(_nv,_oe,_nx));},1));});break;case 101:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_bW,_cQ,new T(function(){return E(B(_l4(_nx))[3]);}))),new T(function(){return B(_jY(_nv,_oe,_nx));},1));});break;case 102:return new F(function(){return _4(B(_lI(_gV,_nx)),new T(function(){return B(_jY(_nv,_oe,_nx));},1));});break;case 103:return new F(function(){return _4(B(_lz(_gV,_nx)),new T(function(){return B(_jY(_nv,_oe,_nx));},1));});break;case 104:var _oh=E(_nv);return new F(function(){return _4(B(_7m(_oh[2],E(B(_l4(_nx))[2])-1|0))[2],new T(function(){return B(_jY(_oh,_oe,_nx));},1));});break;case 106:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_lj,_cQ,new T(function(){return E(B(_8m(_nx))[2]);}))),new T(function(){return B(_jY(_nv,_oe,_nx));},1));});break;case 109:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_bW,_cQ,new T(function(){return E(B(_l4(_nx))[2]);}))),new T(function(){return B(_jY(_nv,_oe,_nx));},1));});break;case 110:return new F(function(){return _4(_gS,new T(function(){return B(_jY(_nv,_oe,_nx));},1));});break;case 116:return new F(function(){return _4(_gR,new T(function(){return B(_jY(_nv,_oe,_nx));},1));});break;case 117:return new F(function(){return _4(B(_e(0,E(B(_km(_nx))[3]),_w)),new T(function(){return B(_jY(_nv,_oe,_nx));},1));});break;case 119:return new F(function(){return _4(B(_e(0,E(B(_8A(_nx))[2]),_w)),new T(function(){return B(_jY(_nv,_oe,_nx));},1));});break;case 120:var _oi=E(_nv);return new F(function(){return _4(B(_jY(_oi,_oi[5],_nx)),new T(function(){return B(_jY(_oi,_oe,_nx));},1));});break;case 121:return new F(function(){return _4(B(_jK(_gV,_nx)),new T(function(){return B(_jY(_nv,_oe,_nx));},1));});break;default:var _o5=_nv,_o6=_nx;_nr=_o5;_ns=_oe;_nt=_o6;return null;}}break;case 94:var _oj=E(_nC);if(!_oj[0]){return new F(function(){return _nE(_);});}else{var _ok=_oj[2],_ol=E(_oj[1]);switch(_ol){case 37:var _om=new T(function(){return B(_jY(_nv,_ok,_nx));}),_on=function(_oo){var _op=E(_oo);return (_op[0]==0)?E(_om):[1,new T(function(){return B(_gX(_op[1]));}),new T(function(){return B(_on(_op[2]));})];};return new F(function(){return _on(_gT);});break;case 110:var _oq=new T(function(){return B(_jY(_nv,_ok,_nx));}),_or=function(_os){var _ot=E(_os);return (_ot[0]==0)?E(_oq):[1,new T(function(){return B(_gX(_ot[1]));}),new T(function(){return B(_or(_ot[2]));})];};return new F(function(){return _or(_gS);});break;case 116:var _ou=new T(function(){return B(_jY(_nv,_ok,_nx));}),_ov=function(_ow){var _ox=E(_ow);return (_ox[0]==0)?E(_ou):[1,new T(function(){return B(_gX(_ox[1]));}),new T(function(){return B(_ov(_ox[2]));})];};return new F(function(){return _ov(_gR);});break;default:var _oy=function(_oz){var _oA=new T(function(){return B(_jY(_nv,_ok,_nx));}),_oB=function(_oC){var _oD=E(_oC);return (_oD[0]==0)?E(_oA):[1,new T(function(){return B(_gX(_oD[1]));}),new T(function(){return B(_oB(_oD[2]));})];};return new F(function(){return _oB(B(A(_oz,[_nv,_2s,_nx])));});};switch(E(_ol)){case 65:return new F(function(){return _oy(_nn);});break;case 66:return new F(function(){return _oy(_nj);});break;case 67:return new F(function(){return _oy(_nc);});break;case 68:return new F(function(){return _oy(_n4);});break;case 70:return new F(function(){return _oy(_n1);});break;case 71:return new F(function(){return _oy(_mX);});break;case 85:return new F(function(){return _oy(_mP);});break;case 86:return new F(function(){return _oy(_mH);});break;case 87:return new F(function(){return _oy(_mz);});break;case 89:return new F(function(){return _oy(_mn);});break;case 97:return new F(function(){return _oy(_me);});break;case 98:return new F(function(){return _oy(_ma);});break;case 100:return new F(function(){return _oy(_m3);});break;case 101:return new F(function(){return _oy(_lV);});break;case 102:return new F(function(){return _oy(_lN);});break;case 103:return new F(function(){return _oy(_lE);});break;case 104:return new F(function(){return _oy(_lv);});break;case 106:return new F(function(){return _oy(_lo);});break;case 109:return new F(function(){return _oy(_lf);});break;case 117:return new F(function(){return _oy(_kw);});break;case 119:return new F(function(){return _oy(_jZ);});break;case 120:return new F(function(){return _oy(_jT);});break;case 121:return new F(function(){return _oy(_jP);});break;default:var _o5=_nv,_o6=_nx;_nr=_o5;_ns=_ok;_nt=_o6;return null;}}}break;case 95:var _oE=E(_nC);if(!_oE[0]){return new F(function(){return _nE(_);});}else{var _oF=_oE[2];switch(E(_oE[1])){case 37:return new F(function(){return _4(_gT,new T(function(){return B(_jY(_nv,_oF,_nx));},1));});break;case 65:return new F(function(){return _4(B(_7m(B(_8F(_nv)),E(B(_8A(_nx))[2])))[1],new T(function(){return B(_jY(_nv,_oF,_nx));},1));});break;case 66:var _oG=E(_nv);return new F(function(){return _4(B(_7m(_oG[2],E(B(_l4(_nx))[2])-1|0))[1],new T(function(){return B(_jY(_oG,_oF,_nx));},1));});break;case 67:return new F(function(){return _4(B(_n7(_gU,_nx)),new T(function(){return B(_jY(_nv,_oF,_nx));},1));});break;case 68:return new F(function(){return _4(B(_jY(_nv,_8S,_nx)),new T(function(){return B(_jY(_nv,_oF,_nx));},1));});break;case 70:return new F(function(){return _4(B(_jY(_nv,_8R,_nx)),new T(function(){return B(_jY(_nv,_oF,_nx));},1));});break;case 71:return new F(function(){return _4(B(_ce(_iM,_ju,_jJ,_mi,_aL,new T(function(){return E(B(_km(_nx))[1]);}))),new T(function(){return B(_jY(_nv,_oF,_nx));},1));});break;case 85:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_bW,_aL,new T(function(){return E(B(_8A(_nx))[1]);}))),new T(function(){return B(_jY(_nv,_oF,_nx));},1));});break;case 86:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_bW,_aL,new T(function(){return E(B(_km(_nx))[2]);}))),new T(function(){return B(_jY(_nv,_oF,_nx));},1));});break;case 87:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_bW,_aL,new T(function(){return E(B(_ms(_nx))[1]);}))),new T(function(){return B(_jY(_nv,_oF,_nx));},1));});break;case 89:return new F(function(){return _4(B(_ce(_iM,_ju,_jJ,_mi,_aL,new T(function(){return E(B(_8m(_nx))[1]);}))),new T(function(){return B(_jY(_nv,_oF,_nx));},1));});break;case 97:return new F(function(){return _4(B(_7m(B(_8F(_nv)),E(B(_8A(_nx))[2])))[2],new T(function(){return B(_jY(_nv,_oF,_nx));},1));});break;case 98:var _oH=E(_nv);return new F(function(){return _4(B(_7m(_oH[2],E(B(_l4(_nx))[2])-1|0))[2],new T(function(){return B(_jY(_oH,_oF,_nx));},1));});break;case 100:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_bW,_aL,new T(function(){return E(B(_l4(_nx))[3]);}))),new T(function(){return B(_jY(_nv,_oF,_nx));},1));});break;case 101:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_bW,_aL,new T(function(){return E(B(_l4(_nx))[3]);}))),new T(function(){return B(_jY(_nv,_oF,_nx));},1));});break;case 102:return new F(function(){return _4(B(_lI(_gU,_nx)),new T(function(){return B(_jY(_nv,_oF,_nx));},1));});break;case 103:return new F(function(){return _4(B(_lz(_gU,_nx)),new T(function(){return B(_jY(_nv,_oF,_nx));},1));});break;case 104:var _oI=E(_nv);return new F(function(){return _4(B(_7m(_oI[2],E(B(_l4(_nx))[2])-1|0))[2],new T(function(){return B(_jY(_oI,_oF,_nx));},1));});break;case 106:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_lj,_aL,new T(function(){return E(B(_8m(_nx))[2]);}))),new T(function(){return B(_jY(_nv,_oF,_nx));},1));});break;case 109:return new F(function(){return _4(B(_ce(_b8,_bI,_bV,_bW,_aL,new T(function(){return E(B(_l4(_nx))[2]);}))),new T(function(){return B(_jY(_nv,_oF,_nx));},1));});break;case 110:return new F(function(){return _4(_gS,new T(function(){return B(_jY(_nv,_oF,_nx));},1));});break;case 116:return new F(function(){return _4(_gR,new T(function(){return B(_jY(_nv,_oF,_nx));},1));});break;case 117:return new F(function(){return _4(B(_e(0,E(B(_km(_nx))[3]),_w)),new T(function(){return B(_jY(_nv,_oF,_nx));},1));});break;case 119:return new F(function(){return _4(B(_e(0,E(B(_8A(_nx))[2]),_w)),new T(function(){return B(_jY(_nv,_oF,_nx));},1));});break;case 120:var _oJ=E(_nv);return new F(function(){return _4(B(_jY(_oJ,_oJ[5],_nx)),new T(function(){return B(_jY(_oJ,_oF,_nx));},1));});break;case 121:return new F(function(){return _4(B(_jK(_gU,_nx)),new T(function(){return B(_jY(_nv,_oF,_nx));},1));});break;default:var _o5=_nv,_o6=_nx;_nr=_o5;_ns=_oF;_nt=_o6;return null;}}break;default:return new F(function(){return _nE(_);});}}}else{return [1,_nA,new T(function(){return B(_jY(_nv,_nz,_nx));})];}}})(_nr,_ns,_nt));if(_nu!=null){return _nu;}}},_oK=45,_oL=43,_oM=function(_oN,_oO){return new F(function(){return _ce(_b8,_bI,_bV,_mi,_oN,new T(function(){var _oP=E(_oO);return (imul(B(_5V(_oP,60)),100)|0)+B(_7X(_oP,60))|0;}));});},_oQ=function(_oR,_oS,_oT){var _oU=E(E(_oT)[2]),_oV=E(_oU[3]);if(!_oV[0]){var _oW=E(_oU[1]);return (_oW>=0)?[1,_oL,new T(function(){var _oX=E(_oS);if(!_oX[0]){return B(_oM(_cQ,_oW));}else{return B(_oM(_oX[1],_oW));}})]:[1,_oK,new T(function(){var _oY=E(_oS);if(!_oY[0]){return B(_oM(_cQ, -_oW));}else{return B(_oM(_oY[1], -_oW));}})];}else{return E(_oV);}},_oZ=[1,_oQ],_p0=function(_p1,_p2,_p3){while(1){var _p4=B((function(_p5,_p6,_p7){var _p8=E(_p6);if(!_p8[0]){return [0];}else{var _p9=_p8[2],_pa=E(_p8[1]);if(E(_pa)==37){var _pb=E(_p9);if(!_pb[0]){return [1,_pa,new T(function(){return B(_p0(_p5,_w,_p7));})];}else{var _pc=_pb[2],_pd=E(_pb[1]),_pe=function(_pf){var _pg=E(_pd);switch(_pg){case 37:return new F(function(){return _4(_gT,new T(function(){return B(_p0(_p5,_pc,_p7));},1));});break;case 110:return new F(function(){return _4(_gS,new T(function(){return B(_p0(_p5,_pc,_p7));},1));});break;case 116:return new F(function(){return _4(_gR,new T(function(){return B(_p0(_p5,_pc,_p7));},1));});break;default:var _ph=B(_pi(_pg));if(!_ph[0]){return new F(function(){return _p0(_p5,_pc,_p7);});}else{return new F(function(){return _4(B(A(_ph[1],[_p5,_2s,_p7])),new T(function(){return B(_p0(_p5,_pc,_p7));},1));});}}};switch(E(_pd)){case 35:var _pj=E(_pc);if(!_pj[0]){return new F(function(){return _pe(_);});}else{var _pk=_pj[2],_pl=E(_pj[1]);switch(_pl){case 37:var _pm=new T(function(){return B(_p0(_p5,_pk,_p7));}),_pn=function(_po){var _pp=E(_po);return (_pp[0]==0)?E(_pm):[1,new T(function(){return B(_gb(_pp[1]));}),new T(function(){return B(_pn(_pp[2]));})];};return new F(function(){return _pn(_gT);});break;case 110:var _pq=new T(function(){return B(_p0(_p5,_pk,_p7));}),_pr=function(_ps){var _pt=E(_ps);return (_pt[0]==0)?E(_pq):[1,new T(function(){return B(_gb(_pt[1]));}),new T(function(){return B(_pr(_pt[2]));})];};return new F(function(){return _pr(_gS);});break;case 116:var _pu=new T(function(){return B(_p0(_p5,_pk,_p7));}),_pv=function(_pw){var _px=E(_pw);return (_px[0]==0)?E(_pu):[1,new T(function(){return B(_gb(_px[1]));}),new T(function(){return B(_pv(_px[2]));})];};return new F(function(){return _pv(_gR);});break;default:var _py=B(_pi(_pl));if(!_py[0]){var _pz=_p5,_pA=_p7;_p1=_pz;_p2=_pk;_p3=_pA;return null;}else{var _pB=new T(function(){return B(_p0(_p5,_pk,_p7));}),_pC=function(_pD){var _pE=E(_pD);return (_pE[0]==0)?E(_pB):[1,new T(function(){return B(_gb(_pE[1]));}),new T(function(){return B(_pC(_pE[2]));})];};return new F(function(){return _pC(B(A(_py[1],[_p5,_2s,_p7])));});}}}break;case 45:var _pF=E(_pc);if(!_pF[0]){return new F(function(){return _pe(_);});}else{var _pG=_pF[2],_pH=E(_pF[1]);switch(_pH){case 37:return new F(function(){return _4(_gT,new T(function(){return B(_p0(_p5,_pG,_p7));},1));});break;case 110:return new F(function(){return _4(_gS,new T(function(){return B(_p0(_p5,_pG,_p7));},1));});break;case 116:return new F(function(){return _4(_gR,new T(function(){return B(_p0(_p5,_pG,_p7));},1));});break;default:var _pI=B(_pi(_pH));if(!_pI[0]){var _pz=_p5,_pA=_p7;_p1=_pz;_p2=_pG;_p3=_pA;return null;}else{return new F(function(){return _4(B(A(_pI[1],[_p5,_gW,_p7])),new T(function(){return B(_p0(_p5,_pG,_p7));},1));});}}}break;case 48:var _pJ=E(_pc);if(!_pJ[0]){return new F(function(){return _pe(_);});}else{var _pK=_pJ[2],_pL=E(_pJ[1]);switch(_pL){case 37:return new F(function(){return _4(_gT,new T(function(){return B(_p0(_p5,_pK,_p7));},1));});break;case 110:return new F(function(){return _4(_gS,new T(function(){return B(_p0(_p5,_pK,_p7));},1));});break;case 116:return new F(function(){return _4(_gR,new T(function(){return B(_p0(_p5,_pK,_p7));},1));});break;default:var _pM=B(_pi(_pL));if(!_pM[0]){var _pz=_p5,_pA=_p7;_p1=_pz;_p2=_pK;_p3=_pA;return null;}else{return new F(function(){return _4(B(A(_pM[1],[_p5,_gV,_p7])),new T(function(){return B(_p0(_p5,_pK,_p7));},1));});}}}break;case 94:var _pN=E(_pc);if(!_pN[0]){return new F(function(){return _pe(_);});}else{var _pO=_pN[2],_pP=E(_pN[1]);switch(_pP){case 37:var _pQ=new T(function(){return B(_p0(_p5,_pO,_p7));}),_pR=function(_pS){var _pT=E(_pS);return (_pT[0]==0)?E(_pQ):[1,new T(function(){return B(_gX(_pT[1]));}),new T(function(){return B(_pR(_pT[2]));})];};return new F(function(){return _pR(_gT);});break;case 110:var _pU=new T(function(){return B(_p0(_p5,_pO,_p7));}),_pV=function(_pW){var _pX=E(_pW);return (_pX[0]==0)?E(_pU):[1,new T(function(){return B(_gX(_pX[1]));}),new T(function(){return B(_pV(_pX[2]));})];};return new F(function(){return _pV(_gS);});break;case 116:var _pY=new T(function(){return B(_p0(_p5,_pO,_p7));}),_pZ=function(_q0){var _q1=E(_q0);return (_q1[0]==0)?E(_pY):[1,new T(function(){return B(_gX(_q1[1]));}),new T(function(){return B(_pZ(_q1[2]));})];};return new F(function(){return _pZ(_gR);});break;default:var _q2=B(_pi(_pP));if(!_q2[0]){var _pz=_p5,_pA=_p7;_p1=_pz;_p2=_pO;_p3=_pA;return null;}else{var _q3=new T(function(){return B(_p0(_p5,_pO,_p7));}),_q4=function(_q5){var _q6=E(_q5);return (_q6[0]==0)?E(_q3):[1,new T(function(){return B(_gX(_q6[1]));}),new T(function(){return B(_q4(_q6[2]));})];};return new F(function(){return _q4(B(A(_q2[1],[_p5,_2s,_p7])));});}}}break;case 95:var _q7=E(_pc);if(!_q7[0]){return new F(function(){return _pe(_);});}else{var _q8=_q7[2],_q9=E(_q7[1]);switch(_q9){case 37:return new F(function(){return _4(_gT,new T(function(){return B(_p0(_p5,_q8,_p7));},1));});break;case 110:return new F(function(){return _4(_gS,new T(function(){return B(_p0(_p5,_q8,_p7));},1));});break;case 116:return new F(function(){return _4(_gR,new T(function(){return B(_p0(_p5,_q8,_p7));},1));});break;default:var _qa=B(_pi(_q9));if(!_qa[0]){var _pz=_p5,_pA=_p7;_p1=_pz;_p2=_q8;_p3=_pA;return null;}else{return new F(function(){return _4(B(A(_qa[1],[_p5,_gU,_p7])),new T(function(){return B(_p0(_p5,_q8,_p7));},1));});}}}break;default:return new F(function(){return _pe(_);});}}}else{return [1,_pa,new T(function(){return B(_p0(_p5,_p9,_p7));})];}}})(_p1,_p2,_p3));if(_p4!=null){return _p4;}}},_qb=function(_qc,_qd,_qe){var _qf=E(_qc);return new F(function(){return _p0(_qf,_qf[4],_qe);});},_qg=new T(function(){return [1,_qb];}),_qh=[0,1],_qi=function(_qj,_qk){var _ql=E(_qj);return [0,_ql,new T(function(){var _qm=B(_qi(B(_8c(_ql,_qk)),_qk));return [1,_qm[1],_qm[2]];})];},_qn=function(_qo){var _qp=B(_qi(_qo,_qh));return [1,_qp[1],_qp[2]];},_qq=function(_qr,_qs){var _qt=B(_qi(_qr,new T(function(){return B(_7O(_qs,_qr));})));return [1,_qt[1],_qt[2]];},_qu=[0,0],_qv=function(_qw,_qx,_qy){if(!B(_je(_qx,_qu))){var _qz=function(_qA){return (!B(_9d(_qA,_qy)))?[1,_qA,new T(function(){return B(_qz(B(_8c(_qA,_qx))));})]:[0];};return new F(function(){return _qz(_qw);});}else{var _qB=function(_qC){return (!B(_jm(_qC,_qy)))?[1,_qC,new T(function(){return B(_qB(B(_8c(_qC,_qx))));})]:[0];};return new F(function(){return _qB(_qw);});}},_qD=function(_qE,_qF,_qG){return new F(function(){return _qv(_qE,B(_7O(_qF,_qE)),_qG);});},_qH=function(_qI,_qJ){return new F(function(){return _qv(_qI,_qh,_qJ);});},_qK=function(_qL){return new F(function(){return _7r(_qL);});},_qM=function(_qN){return new F(function(){return _7O(_qN,_qh);});},_qO=function(_qP){return new F(function(){return _8c(_qP,_qh);});},_qQ=function(_qR){return new F(function(){return _8y(E(_qR));});},_qS=[0,_qO,_qM,_qQ,_qK,_qn,_qq,_qH,_qD],_qT=function(_qU,_qV){if(!B(_6G(_qV,_eD))){return new F(function(){return _5Y(_qU,_qV);});}else{return E(_6F);}},_qW=function(_qX,_qY){if(!B(_6G(_qY,_eD))){var _qZ=B(_9R(_qX,_qY));return [0,_qZ[1],_qZ[2]];}else{return E(_6F);}},_r0=function(_r1,_r2){if(!B(_6G(_r2,_eD))){return new F(function(){return _84(_r1,_r2);});}else{return E(_6F);}},_r3=function(_r4,_r5){if(!B(_6G(_r5,_eD))){return new F(function(){return _eZ(_r4,_r5);});}else{return E(_6F);}},_r6=function(_r7,_r8){if(!B(_6G(_r8,_eD))){var _r9=B(_fv(_r7,_r8));return [0,_r9[1],_r9[2]];}else{return E(_6F);}},_ra=function(_rb){return E(_rb);},_rc=function(_rd){return [0,E(_rd),E(_95)];},_re=[0,_iM,_ju,_rc],_rf=[0,_re,_qS,_r3,_eM,_qT,_r0,_r6,_qW,_ra],_rg=function(_rh){return E(E(_rh)[2]);},_ri=function(_rj,_rk,_rl){var _rm=B(_fE(_rj,_rk,_rl)),_rn=_rm[1],_ro=E(_rm[2]);if(!B(_9d(B(_6O(_ro[1],_95)),B(_6O(_eD,_ro[2]))))){return E(_rn);}else{var _rp=B(_ft(B(_fr(_rj))));return new F(function(){return A(_rg,[_rp,_rn,new T(function(){return B(A(_c6,[_rp,_95]));})]);});}},_rq=function(_rr,_rs,_rt,_ru){var _rv=new T(function(){return E(_rt)+E(E(_rr)[1])|0;}),_rw=new T(function(){return E(_rs)+B(_5V(E(_rv),60))|0;});return [0,new T(function(){return B(_8y(B(_5V(E(_rw),24))));}),[0,new T(function(){return B(_7X(E(_rw),24));}),new T(function(){return B(_7X(E(_rv),60));}),_ru]];},_rx=function(_ry,_rz,_rA){var _rB=B(A(_ry,[_rz]));if(!B(_6G(_rB,_5U))){return new F(function(){return _5Y(B(_6O(_rz,_rA)),_rB);});}else{return E(_6F);}},_rC=[1,I_fromBits([3601842176,13969])],_rD=function(_rE,_rF,_rG){return new F(function(){return _8c(B(_rx(_3i,B(_8c(B(_rx(_3i,B(_6O(B(_8y(_rE)),_3h)),_rC)),B(_6O(B(_8y(_rF)),_3h)))),_rC)),_rG);});},_rH=function(_rI){var _rJ=E(_rI);return new F(function(){return _rD(E(_rJ[1]),E(_rJ[2]),_rJ[3]);});},_rK=function(_rL,_rM,_rN){var _rO=new T(function(){var _rP=E(_rN),_rQ=B(_rq([0,new T(function(){return  -E(E(_rL)[1]);}),_8Z,_w],_rP[1],_rP[2],_rP[3]));return [0,_rQ[1],_rQ[2]];});return [0,new T(function(){return B(_8c(_rM,E(_rO)[1]));}),new T(function(){return B(_rH(E(_rO)[2]));})];},_rR=[1,I_fromBits([2627207168,20116567])],_rS=[0,40587],_rT=function(_rU,_rV){var _rW=B(_rx(_3i,B(_6O(B(_7O(_rU,_rS)),_3h)),_rR));if(!B(_7x(_rR,_rV))){return new F(function(){return _8c(_rW,_rV);});}else{return new F(function(){return _8c(_rW,_rR);});}},_rX=function(_rY,_rZ,_s0){var _s1=B(_rK(_s0,_rY,_rZ)),_s2=B(_fl(B(_rT(_s1[1],_s1[2])),_95,_3h,_95));return new F(function(){return _9m(0,B(_ri(_rf,_s2[1],_s2[2])),_w);});},_s3=function(_s4,_s5,_s6){var _s7=E(_s6),_s8=E(_s7[1]);return new F(function(){return _rX(_s8[1],_s8[2],_s7[2]);});},_s9=[1,_s3],_sa=function(_sb,_sc,_sd){var _se=E(E(E(_sd)[2])[1]);return (_se>=0)?[1,_oL,new T(function(){var _sf=E(_sc);if(!_sf[0]){return B(_oM(_cQ,_se));}else{return B(_oM(_sf[1],_se));}})]:[1,_oK,new T(function(){var _sg=E(_sc);if(!_sg[0]){return B(_oM(_cQ, -_se));}else{return B(_oM(_sg[1], -_se));}})];},_sh=[1,_sa],_si=function(_sj){return E(E(_sj)[1]);},_pi=function(_sk){switch(E(_sk)){case 65:return [1,function(_sl,_sm,_sn){return new F(function(){return _8L(_sl,_sm,new T(function(){return B(_si(_sn));}));});}];case 66:return [1,function(_so,_sp,_sq){return E(B(_7m(E(_so)[2],E(B(_l4(new T(function(){return E(E(E(_sq)[1])[1]);},1)))[2])-1|0))[1]);}];case 67:return [1,function(_sr,_ss,_st){return new F(function(){return _n7(_ss,new T(function(){return E(E(E(_st)[1])[1]);},1));});}];case 68:return [1,function(_su,_sv,_sw){return new F(function(){return _jY(_su,_8S,new T(function(){return E(E(E(_sw)[1])[1]);}));});}];case 70:return [1,function(_sx,_sy,_sz){return new F(function(){return _jY(_sx,_8R,new T(function(){return E(E(E(_sz)[1])[1]);}));});}];case 71:return [1,function(_sA,_sB,_sC){return new F(function(){return _mT(_sB,new T(function(){return E(E(E(_sC)[1])[1]);}));});}];case 72:return [1,function(_sD,_sE,_sF){return new F(function(){return _gE(_sE,new T(function(){return E(E(E(_sF)[1])[2]);},1));});}];case 73:return [1,function(_sG,_sH,_sI){return new F(function(){return _gv(_sH,new T(function(){return E(E(E(_sI)[1])[2]);},1));});}];case 77:return [1,function(_sJ,_sK,_sL){return new F(function(){return _gn(_sK,new T(function(){return E(E(E(_sL)[1])[2]);},1));});}];case 80:return [1,function(_sM,_sN,_sO){var _sP=E(E(_sM)[3]);return new F(function(){return _ge(_sP[1],_sP[2],E(E(E(E(_sO)[1])[2])[1]));});}];case 81:return [1,function(_sQ,_sR,_sS){return new F(function(){return _90(_78,B(_ac(_3i,_fY,E(E(E(_sS)[1])[2])[3])));});}];case 82:return [1,function(_sT,_sU,_sV){return new F(function(){return _cK(_sT,_8Q,new T(function(){return E(E(E(_sV)[1])[2]);}));});}];case 83:return [1,function(_sW,_sX,_sY){return new F(function(){return _fL(_sX,new T(function(){return E(E(E(_sY)[1])[2]);},1));});}];case 84:return [1,function(_sZ,_t0,_t1){return new F(function(){return _cK(_sZ,_8P,new T(function(){return E(E(E(_t1)[1])[2]);}));});}];case 85:return [1,function(_t2,_t3,_t4){return new F(function(){return _mL(_t3,new T(function(){return E(E(E(_t4)[1])[1]);}));});}];case 86:return [1,function(_t5,_t6,_t7){return new F(function(){return _mD(_t6,new T(function(){return E(E(E(_t7)[1])[1]);}));});}];case 87:return [1,function(_t8,_t9,_ta){return new F(function(){return _mv(_t9,new T(function(){return E(E(E(_ta)[1])[1]);}));});}];case 88:return [1,function(_tb,_tc,_td){var _te=E(_tb);return new F(function(){return _cK(_te,_te[6],new T(function(){return E(E(E(_td)[1])[2]);}));});}];case 89:return [1,function(_tf,_tg,_th){return new F(function(){return _mj(_tg,new T(function(){return E(E(E(_th)[1])[1]);},1));});}];case 90:return E(_oZ);case 97:return [1,function(_ti,_tj,_tk){return new F(function(){return _8H(_ti,_tj,new T(function(){return B(_si(_tk));}));});}];case 98:return [1,function(_tl,_tm,_tn){return E(B(_7m(E(_tl)[2],E(B(_l4(new T(function(){return E(E(E(_tn)[1])[1]);},1)))[2])-1|0))[2]);}];case 99:return E(_qg);case 100:return [1,function(_to,_tp,_tq){return new F(function(){return _lZ(_tp,new T(function(){return E(E(E(_tq)[1])[1]);},1));});}];case 101:return [1,function(_tr,_ts,_tt){return new F(function(){return _lR(_ts,new T(function(){return E(E(E(_tt)[1])[1]);},1));});}];case 102:return [1,function(_tu,_tv,_tw){return new F(function(){return _lI(_tv,new T(function(){return E(E(E(_tw)[1])[1]);}));});}];case 103:return [1,function(_tx,_ty,_tz){return new F(function(){return _lz(_ty,new T(function(){return E(E(E(_tz)[1])[1]);}));});}];case 104:return [1,function(_tA,_tB,_tC){return E(B(_7m(E(_tA)[2],E(B(_l4(new T(function(){return E(E(E(_tC)[1])[1]);},1)))[2])-1|0))[2]);}];case 106:return [1,function(_tD,_tE,_tF){return new F(function(){return _lk(_tE,new T(function(){return E(E(E(_tF)[1])[1]);},1));});}];case 107:return [1,function(_tG,_tH,_tI){return new F(function(){return _cx(_tH,new T(function(){return E(E(E(_tI)[1])[2]);},1));});}];case 108:return [1,function(_tJ,_tK,_tL){return new F(function(){return _co(_tK,new T(function(){return E(E(E(_tL)[1])[2]);},1));});}];case 109:return [1,function(_tM,_tN,_tO){return new F(function(){return _lb(_tN,new T(function(){return E(E(E(_tO)[1])[1]);},1));});}];case 112:return [1,function(_tP,_tQ,_tR){return (E(E(E(E(_tR)[1])[2])[1])>=12)?E(E(E(_tP)[3])[2]):E(E(E(_tP)[3])[1]);}];case 113:return [1,function(_tS,_tT,_tU){return new F(function(){return _aA(E(E(E(_tU)[1])[2])[3]);});}];case 114:return [1,function(_tV,_tW,_tX){var _tY=E(_tV);return new F(function(){return _cK(_tY,_tY[7],new T(function(){return E(E(E(_tX)[1])[2]);}));});}];case 115:return E(_s9);case 117:return [1,function(_tZ,_u0,_u1){return new F(function(){return _e(0,E(B(_km(new T(function(){return E(E(E(_u1)[1])[1]);})))[3]),_w);});}];case 119:return [1,function(_u2,_u3,_u4){return new F(function(){return _e(0,E(B(_8A(new T(function(){return E(E(E(_u4)[1])[1]);})))[2]),_w);});}];case 120:return [1,function(_u5,_u6,_u7){var _u8=E(_u5);return new F(function(){return _jY(_u8,_u8[5],new T(function(){return E(E(E(_u7)[1])[1]);}));});}];case 121:return [1,function(_u9,_ua,_ub){return new F(function(){return _jK(_ua,new T(function(){return E(E(E(_ub)[1])[1]);},1));});}];case 122:return E(_sh);default:return [0];}},_uc=function(_ud){var _ue=B(_fl(_ud,_95,_3h,_95));return [0,E(_ue[1]),E(_ue[2])];},_uf=[0,_6G,_iN],_ug=[0,_uf,_j2,_9d,_7x,_jm,_je,_iW,_iZ],_uh=function(_ui,_uj){return new F(function(){return _rx(_3i,_ui,_uj);});},_uk=function(_ul){return new F(function(){return _6O(B(_fg(_ul)),_3h);});},_um=function(_un){return new F(function(){return _6O(_un,_3h);});},_uo=[0,_8c,_7O,_uh,_a8,_eU,_uk,_um],_up=[0,_uo,_ug,_uc],_uq=59,_ur=23,_us=[0,60],_ut=[1,I_fromBits([2627207168,20116567])],_uu=function(_uv){return E(E(_uv)[3]);},_uw=function(_ux){return E(E(_ux)[3]);},_uy=function(_uz,_uA,_uB,_uC){var _uD=B(A(_uw,[_uz,_uB])),_uE=B(A(_uw,[_uz,_uC])),_uF=B(_fl(_uD[1],_uD[2],_uE[1],_uE[2]));return new F(function(){return _ri(_uA,_uF[1],_uF[2]);});},_uG=function(_uH,_uI,_uJ){var _uK=B(_ft(_uH)),_uL=new T(function(){var _uM=new T(function(){return B(A(_c6,[_uK,new T(function(){return B(_uy(_uH,_rf,_uI,_uJ));})]));});return B(A(_uu,[_uK,_uM,_uJ]));});return new F(function(){return A(_rg,[_uK,_uI,_uL]);});},_uN=function(_uO){if(!B(_je(_uO,_ut))){var _uP=new T(function(){var _uQ=B(_fl(_uO,_95,_3h,_95)),_uR=B(_fl(_rC,_95,_3h,_95)),_uS=B(_fl(_uQ[1],_uQ[2],_uR[1],_uR[2]));return B(_ri(_rf,_uS[1],_uS[2]));});return [0,new T(function(){var _uT=B(_fl(_uP,_95,_us,_95));return B(_7r(B(_ri(_rf,_uT[1],_uT[2]))));}),new T(function(){return B(_7r(B(_uG(_re,_uP,_us))));}),new T(function(){return B(_uG(_up,_uO,_rC));})];}else{return [0,_ur,_uq,new T(function(){return B(_8c(_rC,B(_7O(_uO,_ut))));})];}},_uU=function(_uV,_uW,_uX){var _uY=new T(function(){var _uZ=B(_uN(_uX)),_v0=B(_rq(_uV,_uZ[1],_uZ[2],_uZ[3]));return [0,_v0[1],_v0[2]];});return [0,new T(function(){return B(_8c(_uW,E(_uY)[1]));}),new T(function(){return E(E(_uY)[2]);})];},_v1=new T(function(){return B(unCStr("UTC"));}),_v2=0,_v3=[0,_v2,_8Z,_v1],_v4=function(_v5){var _v6=B(_pi(_v5));if(!_v6[0]){return [0];}else{return [1,function(_v7,_v8,_v9){return new F(function(){return A(_v6[1],[_v7,_v8,[0,new T(function(){var _va=E(_v9),_vb=B(_uU(_v3,_va[1],_va[2]));return [0,_vb[1],_vb[2]];}),_v3]]);});}];}},_vc=function(_vd){return new F(function(){return _v4(E(_vd));});},_ve=function(_vf,_vg,_vh,_){var _vi=B(A(_vg,[_vh,_]));return [0,_vf,new T(function(){return E(E(_vi)[2]);})];},_vj=function(_vk,_vl,_vm,_){var _vn=B(A(_vl,[_vm,_])),_vo=new T(function(){return B(A(_vk,[new T(function(){return E(E(_vn)[1]);})]));});return [0,_vo,new T(function(){return E(E(_vn)[2]);})];},_vp=[0,_vj,_ve],_vq=function(_vr,_vs,_vt,_){var _vu=B(A(_vr,[_vt,_])),_vv=B(A(_vs,[new T(function(){return E(E(_vu)[2]);}),_])),_vw=new T(function(){return B(A(E(_vu)[1],[new T(function(){return E(E(_vv)[1]);})]));});return [0,_vw,new T(function(){return E(E(_vv)[2]);})];},_vx=function(_vy,_vz,_vA,_){var _vB=B(A(_vy,[_vA,_])),_vC=B(A(_vz,[new T(function(){return E(E(_vB)[2]);}),_]));return [0,new T(function(){return E(E(_vC)[1]);}),new T(function(){return E(E(_vC)[2]);})];},_vD=function(_vE,_vF,_vG,_){var _vH=B(A(_vE,[_vG,_])),_vI=B(A(_vF,[new T(function(){return E(E(_vH)[2]);}),_]));return [0,new T(function(){return E(E(_vH)[1]);}),new T(function(){return E(E(_vI)[2]);})];},_vJ=function(_vK,_vL,_){return [0,_vK,_vL];},_vM=[0,_vp,_vJ,_vq,_vx,_vD],_vN=function(_vO,_vP,_vQ,_){var _vR=B(A(_vO,[_vQ,_]));return new F(function(){return A(_vP,[new T(function(){return E(E(_vR)[1]);}),new T(function(){return E(E(_vR)[2]);}),_]);});},_vS=function(_vT,_vU,_){return new F(function(){return _3V(_vT,_);});},_vV=function(_vW){return E(E(_vW)[2]);},_vX=function(_vY,_vZ,_w0,_w1,_w2){var _w3=function(_w4){return new F(function(){return A(_w1,[new T(function(){return E(E(_w4)[1]);}),new T(function(){return E(E(_w4)[2]);})]);});};return new F(function(){return A(_vV,[_vZ,new T(function(){return B(A(_w0,[_w2]));}),_w3]);});},_w5=function(_w6){return E(E(_w6)[5]);},_w7=function(_w8,_w9,_wa){var _wb=new T(function(){return B(A(_w5,[_w9,_wa]));});return function(_wc){return E(_wb);};},_wd=function(_we){return E(E(_we)[4]);},_wf=function(_wg,_wh){return [0,_wg,function(_wi,_wj,_wk){return new F(function(){return _vX(_wg,_wh,_wi,_wj,_wk);});},function(_wj,_wk){return new F(function(){return _wl(_wg,_wh,_wj,_wk);});},function(_wm,_wn){return new F(function(){return A(_wd,[_wh,[0,_wm,_wn]]);});},function(_wk){return new F(function(){return _w7(_wg,_wh,_wk);});}];},_wl=function(_wo,_wp,_wq,_wr){return new F(function(){return A(_vV,[B(_wf(_wo,_wp)),_wq,function(_ws){return E(_wr);}]);});},_wt=function(_wu,_wv){return new F(function(){return _wl(_vM,_3Y,_wu,_wv);});},_ww=[0,_vM,_vN,_wt,_vJ,_vS],_wx=function(_wy,_wz,_){var _wA=B(A(_wy,[_]));return [0,_wA,_wz];},_wB=[0,_ww,_wx],_wC="clock-time",_wD=function(_wE,_wF,_wG,_){var _wH=E(_72)(_wE,toJSStr(E(_73)),toJSStr(E(_wF)));return [0,_70,_wG];},_wI=function(_wJ,_wK,_wL,_){return new F(function(){return _wD(E(_wJ),_wK,_wL,_);});},_wM=-300,_wN=new T(function(){return B(unCStr("EST"));}),_wO=[0,_wM,_8Z,_wN],_wP=new T(function(){return B(unCStr("EDT"));}),_wQ=-240,_wR=[0,_wQ,_fY,_wP],_wS=-360,_wT=new T(function(){return B(unCStr("CST"));}),_wU=[0,_wS,_8Z,_wT],_wV=new T(function(){return B(unCStr("CDT"));}),_wW=[0,_wM,_fY,_wV],_wX=-420,_wY=new T(function(){return B(unCStr("MST"));}),_wZ=[0,_wX,_8Z,_wY],_x0=new T(function(){return B(unCStr("MDT"));}),_x1=[0,_wS,_fY,_x0],_x2=new T(function(){return B(unCStr("PDT"));}),_x3=[0,_wX,_fY,_x2],_x4=[1,_x3,_w],_x5=new T(function(){return B(unCStr("PST"));}),_x6=-480,_x7=[0,_x6,_8Z,_x5],_x8=[1,_x7,_x4],_x9=[1,_x1,_x8],_xa=[1,_wZ,_x9],_xb=[1,_wW,_xa],_xc=[1,_wU,_xb],_xd=[1,_wR,_xc],_xe=[1,_wO,_xd],_xf=new T(function(){return B(unCStr("GMT"));}),_xg=0,_xh=[0,_xg,_8Z,_xf],_xi=[1,_xh,_xe],_xj=new T(function(){return B(unCStr("UT"));}),_xk=[0,_xg,_8Z,_xj],_xl=[1,_xk,_xi],_xm=new T(function(){return B(unCStr("%I:%M:%S %p"));}),_xn=new T(function(){return B(unCStr("%H:%M:%S"));}),_xo=new T(function(){return B(unCStr("%m/%d/%y"));}),_xp=new T(function(){return B(unCStr("%a %b %e %H:%M:%S %Z %Y"));}),_xq=new T(function(){return B(unCStr("PM"));}),_xr=new T(function(){return B(unCStr("AM"));}),_xs=[0,_xr,_xq],_xt=new T(function(){return B(unCStr("Dec"));}),_xu=new T(function(){return B(unCStr("December"));}),_xv=[0,_xu,_xt],_xw=[1,_xv,_w],_xx=new T(function(){return B(unCStr("Nov"));}),_xy=new T(function(){return B(unCStr("November"));}),_xz=[0,_xy,_xx],_xA=[1,_xz,_xw],_xB=new T(function(){return B(unCStr("Oct"));}),_xC=new T(function(){return B(unCStr("October"));}),_xD=[0,_xC,_xB],_xE=[1,_xD,_xA],_xF=new T(function(){return B(unCStr("Sep"));}),_xG=new T(function(){return B(unCStr("September"));}),_xH=[0,_xG,_xF],_xI=[1,_xH,_xE],_xJ=new T(function(){return B(unCStr("Aug"));}),_xK=new T(function(){return B(unCStr("August"));}),_xL=[0,_xK,_xJ],_xM=[1,_xL,_xI],_xN=new T(function(){return B(unCStr("Jul"));}),_xO=new T(function(){return B(unCStr("July"));}),_xP=[0,_xO,_xN],_xQ=[1,_xP,_xM],_xR=new T(function(){return B(unCStr("Jun"));}),_xS=new T(function(){return B(unCStr("June"));}),_xT=[0,_xS,_xR],_xU=[1,_xT,_xQ],_xV=new T(function(){return B(unCStr("May"));}),_xW=[0,_xV,_xV],_xX=[1,_xW,_xU],_xY=new T(function(){return B(unCStr("Apr"));}),_xZ=new T(function(){return B(unCStr("April"));}),_y0=[0,_xZ,_xY],_y1=[1,_y0,_xX],_y2=new T(function(){return B(unCStr("Mar"));}),_y3=new T(function(){return B(unCStr("March"));}),_y4=[0,_y3,_y2],_y5=[1,_y4,_y1],_y6=new T(function(){return B(unCStr("Feb"));}),_y7=new T(function(){return B(unCStr("February"));}),_y8=[0,_y7,_y6],_y9=[1,_y8,_y5],_ya=new T(function(){return B(unCStr("Jan"));}),_yb=new T(function(){return B(unCStr("January"));}),_yc=[0,_yb,_ya],_yd=[1,_yc,_y9],_ye=new T(function(){return B(unCStr("Sun"));}),_yf=new T(function(){return B(unCStr("Sunday"));}),_yg=[0,_yf,_ye],_yh=new T(function(){return B(unCStr("Mon"));}),_yi=new T(function(){return B(unCStr("Monday"));}),_yj=[0,_yi,_yh],_yk=new T(function(){return B(unCStr("Tue"));}),_yl=new T(function(){return B(unCStr("Tuesday"));}),_ym=[0,_yl,_yk],_yn=new T(function(){return B(unCStr("Wed"));}),_yo=new T(function(){return B(unCStr("Wednesday"));}),_yp=[0,_yo,_yn],_yq=new T(function(){return B(unCStr("Thu"));}),_yr=new T(function(){return B(unCStr("Thursday"));}),_ys=[0,_yr,_yq],_yt=new T(function(){return B(unCStr("Fri"));}),_yu=new T(function(){return B(unCStr("Friday"));}),_yv=[0,_yu,_yt],_yw=new T(function(){return B(unCStr("Saturday"));}),_yx=new T(function(){return B(unCStr("Sat"));}),_yy=[0,_yw,_yx],_yz=[1,_yy,_w],_yA=[1,_yv,_yz],_yB=[1,_ys,_yA],_yC=[1,_yp,_yB],_yD=[1,_ym,_yC],_yE=[1,_yj,_yD],_yF=[1,_yg,_yE],_yG=[0,_yF,_yd,_xs,_xp,_xo,_xn,_xm,_xl],_yH=function(_yI,_yJ,_yK,_yL){while(1){var _yM=B((function(_yN,_yO,_yP,_yQ){var _yR=E(_yP);if(!_yR[0]){return [0];}else{var _yS=_yR[2],_yT=E(_yR[1]);if(E(_yT)==37){var _yU=E(_yS);if(!_yU[0]){return [1,_yT,new T(function(){return B(_yH(_yN,_yO,_w,_yQ));})];}else{var _yV=_yU[2],_yW=E(_yU[1]),_yX=function(_yY){switch(E(_yW)){case 37:return new F(function(){return _4(_gT,new T(function(){return B(_yH(_yN,_yO,_yV,_yQ));},1));});break;case 110:return new F(function(){return _4(_gS,new T(function(){return B(_yH(_yN,_yO,_yV,_yQ));},1));});break;case 116:return new F(function(){return _4(_gR,new T(function(){return B(_yH(_yN,_yO,_yV,_yQ));},1));});break;default:var _yZ=B(A(_yN,[_yW]));if(!_yZ[0]){return new F(function(){return _yH(_yN,_yO,_yV,_yQ);});}else{return new F(function(){return _4(B(A(_yZ[1],[_yO,_2s,_yQ])),new T(function(){return B(_yH(_yN,_yO,_yV,_yQ));},1));});}}};switch(E(_yW)){case 35:var _z0=E(_yV);if(!_z0[0]){return new F(function(){return _yX(_);});}else{var _z1=_z0[2],_z2=E(_z0[1]);switch(E(_z2)){case 37:var _z3=new T(function(){return B(_yH(_yN,_yO,_z1,_yQ));}),_z4=function(_z5){var _z6=E(_z5);return (_z6[0]==0)?E(_z3):[1,new T(function(){return B(_gb(_z6[1]));}),new T(function(){return B(_z4(_z6[2]));})];};return new F(function(){return _z4(_gT);});break;case 110:var _z7=new T(function(){return B(_yH(_yN,_yO,_z1,_yQ));}),_z8=function(_z9){var _za=E(_z9);return (_za[0]==0)?E(_z7):[1,new T(function(){return B(_gb(_za[1]));}),new T(function(){return B(_z8(_za[2]));})];};return new F(function(){return _z8(_gS);});break;case 116:var _zb=new T(function(){return B(_yH(_yN,_yO,_z1,_yQ));}),_zc=function(_zd){var _ze=E(_zd);return (_ze[0]==0)?E(_zb):[1,new T(function(){return B(_gb(_ze[1]));}),new T(function(){return B(_zc(_ze[2]));})];};return new F(function(){return _zc(_gR);});break;default:var _zf=B(A(_yN,[_z2]));if(!_zf[0]){var _zg=_yN,_zh=_yO,_zi=_yQ;_yI=_zg;_yJ=_zh;_yK=_z1;_yL=_zi;return null;}else{var _zj=new T(function(){return B(_yH(_yN,_yO,_z1,_yQ));}),_zk=function(_zl){var _zm=E(_zl);return (_zm[0]==0)?E(_zj):[1,new T(function(){return B(_gb(_zm[1]));}),new T(function(){return B(_zk(_zm[2]));})];};return new F(function(){return _zk(B(A(_zf[1],[_yO,_2s,_yQ])));});}}}break;case 45:var _zn=E(_yV);if(!_zn[0]){return new F(function(){return _yX(_);});}else{var _zo=_zn[2],_zp=E(_zn[1]);switch(E(_zp)){case 37:return new F(function(){return _4(_gT,new T(function(){return B(_yH(_yN,_yO,_zo,_yQ));},1));});break;case 110:return new F(function(){return _4(_gS,new T(function(){return B(_yH(_yN,_yO,_zo,_yQ));},1));});break;case 116:return new F(function(){return _4(_gR,new T(function(){return B(_yH(_yN,_yO,_zo,_yQ));},1));});break;default:var _zq=B(A(_yN,[_zp]));if(!_zq[0]){var _zg=_yN,_zh=_yO,_zi=_yQ;_yI=_zg;_yJ=_zh;_yK=_zo;_yL=_zi;return null;}else{return new F(function(){return _4(B(A(_zq[1],[_yO,_gW,_yQ])),new T(function(){return B(_yH(_yN,_yO,_zo,_yQ));},1));});}}}break;case 48:var _zr=E(_yV);if(!_zr[0]){return new F(function(){return _yX(_);});}else{var _zs=_zr[2],_zt=E(_zr[1]);switch(E(_zt)){case 37:return new F(function(){return _4(_gT,new T(function(){return B(_yH(_yN,_yO,_zs,_yQ));},1));});break;case 110:return new F(function(){return _4(_gS,new T(function(){return B(_yH(_yN,_yO,_zs,_yQ));},1));});break;case 116:return new F(function(){return _4(_gR,new T(function(){return B(_yH(_yN,_yO,_zs,_yQ));},1));});break;default:var _zu=B(A(_yN,[_zt]));if(!_zu[0]){var _zg=_yN,_zh=_yO,_zi=_yQ;_yI=_zg;_yJ=_zh;_yK=_zs;_yL=_zi;return null;}else{return new F(function(){return _4(B(A(_zu[1],[_yO,_gV,_yQ])),new T(function(){return B(_yH(_yN,_yO,_zs,_yQ));},1));});}}}break;case 94:var _zv=E(_yV);if(!_zv[0]){return new F(function(){return _yX(_);});}else{var _zw=_zv[2],_zx=E(_zv[1]);switch(E(_zx)){case 37:var _zy=new T(function(){return B(_yH(_yN,_yO,_zw,_yQ));}),_zz=function(_zA){var _zB=E(_zA);return (_zB[0]==0)?E(_zy):[1,new T(function(){return B(_gX(_zB[1]));}),new T(function(){return B(_zz(_zB[2]));})];};return new F(function(){return _zz(_gT);});break;case 110:var _zC=new T(function(){return B(_yH(_yN,_yO,_zw,_yQ));}),_zD=function(_zE){var _zF=E(_zE);return (_zF[0]==0)?E(_zC):[1,new T(function(){return B(_gX(_zF[1]));}),new T(function(){return B(_zD(_zF[2]));})];};return new F(function(){return _zD(_gS);});break;case 116:var _zG=new T(function(){return B(_yH(_yN,_yO,_zw,_yQ));}),_zH=function(_zI){var _zJ=E(_zI);return (_zJ[0]==0)?E(_zG):[1,new T(function(){return B(_gX(_zJ[1]));}),new T(function(){return B(_zH(_zJ[2]));})];};return new F(function(){return _zH(_gR);});break;default:var _zK=B(A(_yN,[_zx]));if(!_zK[0]){var _zg=_yN,_zh=_yO,_zi=_yQ;_yI=_zg;_yJ=_zh;_yK=_zw;_yL=_zi;return null;}else{var _zL=new T(function(){return B(_yH(_yN,_yO,_zw,_yQ));}),_zM=function(_zN){var _zO=E(_zN);return (_zO[0]==0)?E(_zL):[1,new T(function(){return B(_gX(_zO[1]));}),new T(function(){return B(_zM(_zO[2]));})];};return new F(function(){return _zM(B(A(_zK[1],[_yO,_2s,_yQ])));});}}}break;case 95:var _zP=E(_yV);if(!_zP[0]){return new F(function(){return _yX(_);});}else{var _zQ=_zP[2],_zR=E(_zP[1]);switch(E(_zR)){case 37:return new F(function(){return _4(_gT,new T(function(){return B(_yH(_yN,_yO,_zQ,_yQ));},1));});break;case 110:return new F(function(){return _4(_gS,new T(function(){return B(_yH(_yN,_yO,_zQ,_yQ));},1));});break;case 116:return new F(function(){return _4(_gR,new T(function(){return B(_yH(_yN,_yO,_zQ,_yQ));},1));});break;default:var _zS=B(A(_yN,[_zR]));if(!_zS[0]){var _zg=_yN,_zh=_yO,_zi=_yQ;_yI=_zg;_yJ=_zh;_yK=_zQ;_yL=_zi;return null;}else{return new F(function(){return _4(B(A(_zS[1],[_yO,_gU,_yQ])),new T(function(){return B(_yH(_yN,_yO,_zQ,_yQ));},1));});}}}break;default:return new F(function(){return _yX(_);});}}}else{return [1,_yT,new T(function(){return B(_yH(_yN,_yO,_yS,_yQ));})];}}})(_yI,_yJ,_yK,_yL));if(_yM!=null){return _yM;}}},_zT=new T(function(){return B(unCStr("%H:%M:%S"));}),_zU="alice-status-table",_zV=new T(function(){return B(unCStr("</td></tr>"));}),_zW=function(_zX,_zY){var _zZ=new T(function(){return B(unAppCStr("</th><td>",new T(function(){return B(_4(_zY,_zV));})));},1);return new F(function(){return _4(_zX,_zZ);});},_A0=new T(function(){return B(unCStr("sandwich"));}),_A1=[1,_A0,_w],_A2=new T(function(){return B(unCStr("basket"));}),_A3=[1,_A2,_A1],_A4=new T(function(){return B(unCStr("pickaxe"));}),_A5=[1,_A4,_A3],_A6=new T(function(){return B(unCStr("wood"));}),_A7=[1,_A6,_A5],_A8=function(_A9,_Aa){while(1){var _Ab=E(_A9);if(!_Ab[0]){return (E(_Aa)[0]==0)?true:false;}else{var _Ac=E(_Aa);if(!_Ac[0]){return false;}else{if(E(_Ab[1])!=E(_Ac[1])){return false;}else{_A9=_Ab[2];_Aa=_Ac[2];continue;}}}}},_Ad=function(_Ae){return E(E(_Ae)[1]);},_Af=function(_Ag){return new F(function(){return fromJSStr(E(_Ag));});},_Ah=function(_Ai){return E(E(_Ai)[1]);},_Aj=(function(e,p){return e[p].toString();}),_Ak=function(_Al){return E(E(_Al)[2]);},_Am=function(_An,_Ao,_Ap,_Aq){var _Ar=new T(function(){var _As=function(_){var _At=E(_Aj)(B(A(_Ah,[_An,_Ap])),E(_Aq));return new T(function(){return String(_At);});};return E(_As);});return new F(function(){return A(_Ak,[_Ao,_Ar]);});},_Au=function(_Av,_Aw,_Ax,_Ay){var _Az=B(_Ad(_Aw)),_AA=new T(function(){return B(_wd(_Az));}),_AB=function(_AC){return new F(function(){return A(_AA,[new T(function(){return B(_Af(_AC));})]);});},_AD=new T(function(){return B(_Am(_Av,_Aw,_Ax,new T(function(){return toJSStr(E(_Ay));},1)));});return new F(function(){return A(_vV,[_Az,_AD,_AB]);});},_AE=new T(function(){return B(unCStr("money"));}),_AF=new T(function(){return B(unCStr("\u6240\u6301\u91d1"));}),_AG=new T(function(){return B(unCStr(" \u500b"));}),_AH=new T(function(){return B(unCStr("\u30b5\u30f3\u30c9\u30a6\u30a3\u30c3\u30c1"));}),_AI=new T(function(){return B(unCStr(" \u672c"));}),_AJ=new T(function(){return B(unCStr("\u6728\u6750"));}),_AK=new T(function(){return B(unCStr("\u30d4\u30c3\u30b1\u30eb"));}),_AL=new T(function(){return B(_zW(_AK,_w));}),_AM=new T(function(){return B(unCStr(" G"));}),_AN=new T(function(){return B(unCStr("\u30d0\u30b9\u30b1\u30c3\u30c8"));}),_AO=new T(function(){return B(_zW(_AN,_w));}),_AP=new T(function(){return B(unCStr("Control.Exception.Base"));}),_AQ=new T(function(){return B(unCStr("base"));}),_AR=new T(function(){return B(unCStr("PatternMatchFail"));}),_AS=new T(function(){var _AT=hs_wordToWord64(18445595),_AU=hs_wordToWord64(52003073);return [0,_AT,_AU,[0,_AT,_AU,_AQ,_AP,_AR],_w,_w];}),_AV=function(_AW){return E(_AS);},_AX=function(_AY){var _AZ=E(_AY);return new F(function(){return _Z(B(_X(_AZ[1])),_AV,_AZ[2]);});},_B0=function(_B1){return E(E(_B1)[1]);},_B2=function(_B3){return [0,_B4,_B3];},_B5=function(_B6,_B7){return new F(function(){return _4(E(_B6)[1],_B7);});},_B8=function(_B9,_Ba){return new F(function(){return _2a(_B5,_B9,_Ba);});},_Bb=function(_Bc,_Bd,_Be){return new F(function(){return _4(E(_Bd)[1],_Be);});},_Bf=[0,_Bb,_B0,_B8],_B4=new T(function(){return [0,_AV,_Bf,_B2,_AX,_B0];}),_Bg=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_Bh=function(_Bi){return E(E(_Bi)[3]);},_Bj=function(_Bk,_Bl){return new F(function(){return die(new T(function(){return B(A(_Bh,[_Bl,_Bk]));}));});},_Bm=function(_Bn,_6C){return new F(function(){return _Bj(_Bn,_6C);});},_Bo=function(_Bp,_Bq){var _Br=E(_Bq);if(!_Br[0]){return [0,_w,_w];}else{var _Bs=_Br[1];if(!B(A(_Bp,[_Bs]))){return [0,_w,_Br];}else{var _Bt=new T(function(){var _Bu=B(_Bo(_Bp,_Br[2]));return [0,_Bu[1],_Bu[2]];});return [0,[1,_Bs,new T(function(){return E(E(_Bt)[1]);})],new T(function(){return E(E(_Bt)[2]);})];}}},_Bv=32,_Bw=new T(function(){return B(unCStr("\n"));}),_Bx=function(_By){return (E(_By)==124)?false:true;},_Bz=function(_BA,_BB){var _BC=B(_Bo(_Bx,B(unCStr(_BA)))),_BD=_BC[1],_BE=function(_BF,_BG){var _BH=new T(function(){var _BI=new T(function(){return B(_4(_BB,new T(function(){return B(_4(_BG,_Bw));},1)));});return B(unAppCStr(": ",_BI));},1);return new F(function(){return _4(_BF,_BH);});},_BJ=E(_BC[2]);if(!_BJ[0]){return new F(function(){return _BE(_BD,_w);});}else{if(E(_BJ[1])==124){return new F(function(){return _BE(_BD,[1,_Bv,_BJ[2]]);});}else{return new F(function(){return _BE(_BD,_w);});}}},_BK=function(_BL){return new F(function(){return _Bm([0,new T(function(){return B(_Bz(_BL,_Bg));})],_B4);});},_BM=new T(function(){return B(_BK("Main.hs:(94,1)-(98,43)|function itemDisplayLabel"));}),_BN=function(_BO){var _BP=new T(function(){return B(_Au(_3o,_wB,_BO,_73));}),_BQ=function(_BR,_){var _BS=E(_BO),_BT=B(_wD(_BS,_w,_BR,_)),_BU=new T(function(){return E(E(_BT)[2]);}),_BV=new T(function(){return E(E(E(E(E(_BU)[1])[3])[2])[1]);}),_BW=function(_BX,_BY,_){while(1){var _BZ=B((function(_C0,_C1,_){var _C2=E(_C0);if(!_C2[0]){return [0,_70,_C1];}else{var _C3=_C2[1],_C4=_C2[2];if(!B(_5P(_C3,_BV))){var _C5=_C1;_BX=_C4;_BY=_C5;return null;}else{var _C6=B(A(_BP,[_C1,_])),_C7=E(_73),_C8=E(_C6),_C9=new T(function(){var _Ca=new T(function(){if(!B(_A8(_C3,_A2))){if(!B(_A8(_C3,_AE))){if(!B(_A8(_C3,_A4))){if(!B(_A8(_C3,_A0))){if(!B(_A8(_C3,_A6))){return E(_BM);}else{return B(_zW(_AJ,new T(function(){return B(_4(B(_e(0,B(_4a(_C3,_BV)),_w)),_AI));},1)));}}else{return B(_zW(_AH,new T(function(){return B(_4(B(_e(0,B(_4a(_C3,_BV)),_w)),_AG));},1)));}}else{return E(_AL);}}else{return B(_zW(_AF,new T(function(){return B(_4(B(_e(0,B(_4a(_C3,_BV)),_w)),_AM));},1)));}}else{return E(_AO);}});return B(unAppCStr("<tr><th>",_Ca));},1),_Cb=E(_72),_Cc=_Cb(_BS,toJSStr(_C7),toJSStr(B(_4(_C8[1],_C9)))),_Cd=_C4,_Ce=_C8[2];while(1){var _Cf=B((function(_Cg,_Ch,_){var _Ci=E(_Cg);if(!_Ci[0]){return [0,_70,_Ch];}else{var _Cj=_Ci[1],_Ck=_Ci[2];if(!B(_5P(_Cj,_BV))){var _Cl=_Ch;_Cd=_Ck;_Ce=_Cl;return null;}else{var _Cm=B(A(_BP,[_Ch,_])),_Cn=E(_Cm),_Co=new T(function(){var _Cp=new T(function(){if(!B(_A8(_Cj,_A2))){if(!B(_A8(_Cj,_AE))){if(!B(_A8(_Cj,_A4))){if(!B(_A8(_Cj,_A0))){if(!B(_A8(_Cj,_A6))){return E(_BM);}else{return B(_zW(_AJ,new T(function(){return B(_4(B(_e(0,B(_4a(_Cj,_BV)),_w)),_AI));},1)));}}else{return B(_zW(_AH,new T(function(){return B(_4(B(_e(0,B(_4a(_Cj,_BV)),_w)),_AG));},1)));}}else{return E(_AL);}}else{return B(_zW(_AF,new T(function(){return B(_4(B(_e(0,B(_4a(_Cj,_BV)),_w)),_AM));},1)));}}else{return E(_AO);}});return B(unAppCStr("<tr><th>",_Cp));},1),_Cq=_Cb(_BS,toJSStr(_C7),toJSStr(B(_4(_Cn[1],_Co))));_Cd=_Ck;_Ce=_Cn[2];return null;}}})(_Cd,_Ce,_));if(_Cf!=null){return _Cf;}}}}})(_BX,_BY,_));if(_BZ!=null){return _BZ;}}},_Cr=_AE,_Cs=_A7,_Ct=_BU;if(!B(_5P(_Cr,_BV))){return new F(function(){return _BW(_Cs,_Ct,_);});}else{var _Cu=B(A(_BP,[_Ct,_])),_Cv=E(_73),_Cw=E(_Cu),_Cx=new T(function(){var _Cy=new T(function(){if(!B(_A8(_Cr,_A2))){if(!B(_A8(_Cr,_AE))){if(!B(_A8(_Cr,_A4))){if(!B(_A8(_Cr,_A0))){if(!B(_A8(_Cr,_A6))){return E(_BM);}else{return B(_zW(_AJ,new T(function(){return B(_4(B(_e(0,B(_4a(_Cr,_BV)),_w)),_AI));},1)));}}else{return B(_zW(_AH,new T(function(){return B(_4(B(_e(0,B(_4a(_Cr,_BV)),_w)),_AG));},1)));}}else{return E(_AL);}}else{return B(_zW(_AF,new T(function(){return B(_4(B(_e(0,B(_4a(_Cr,_BV)),_w)),_AM));},1)));}}else{return E(_AO);}});return B(unAppCStr("<tr><th>",_Cy));},1),_Cz=E(_72),_CA=_Cz(_BS,toJSStr(_Cv),toJSStr(B(_4(_Cw[1],_Cx)))),_CB=_Cs,_CC=_Cw[2];while(1){var _CD=B((function(_CE,_CF,_){var _CG=E(_CE);if(!_CG[0]){return [0,_70,_CF];}else{var _CH=_CG[1],_CI=_CG[2];if(!B(_5P(_CH,_BV))){var _CJ=_CF;_CB=_CI;_CC=_CJ;return null;}else{var _CK=B(A(_BP,[_CF,_])),_CL=E(_CK),_CM=new T(function(){var _CN=new T(function(){if(!B(_A8(_CH,_A2))){if(!B(_A8(_CH,_AE))){if(!B(_A8(_CH,_A4))){if(!B(_A8(_CH,_A0))){if(!B(_A8(_CH,_A6))){return E(_BM);}else{return B(_zW(_AJ,new T(function(){return B(_4(B(_e(0,B(_4a(_CH,_BV)),_w)),_AI));},1)));}}else{return B(_zW(_AH,new T(function(){return B(_4(B(_e(0,B(_4a(_CH,_BV)),_w)),_AG));},1)));}}else{return E(_AL);}}else{return B(_zW(_AF,new T(function(){return B(_4(B(_e(0,B(_4a(_CH,_BV)),_w)),_AM));},1)));}}else{return E(_AO);}});return B(unAppCStr("<tr><th>",_CN));},1),_CO=_Cz(_BS,toJSStr(_Cv),toJSStr(B(_4(_CL[1],_CM))));_CB=_CI;_CC=_CL[2];return null;}}})(_CB,_CC,_));if(_CD!=null){return _CD;}}}};return E(_BQ);},_CP=(function(id){return document.getElementById(id);}),_CQ=new T(function(){return B(unCStr(" found!"));}),_CR=function(_CS){return new F(function(){return err(B(unAppCStr("No element with ID ",new T(function(){return B(_4(fromJSStr(E(_CS)),_CQ));}))));});},_CT=function(_CU,_CV,_CW){var _CX=new T(function(){var _CY=function(_){var _CZ=E(_CP)(E(_CV)),_D0=__eq(_CZ,E(_2P));return (E(_D0)==0)?[1,_CZ]:_2s;};return B(A(_Ak,[_CU,_CY]));});return new F(function(){return A(_vV,[B(_Ad(_CU)),_CX,function(_D1){var _D2=E(_D1);if(!_D2[0]){return new F(function(){return _CR(_CV);});}else{return new F(function(){return A(_CW,[_D2[1]]);});}}]);});},_D3=new T(function(){return B(_CT(_wB,_zU,_BN));}),_D4=function(_,_D5){var _D6=new T(function(){return E(E(_D5)[2]);}),_D7=new T(function(){return B(_yH(_vc,_yG,_zT,new T(function(){return E(E(E(E(E(E(E(E(_D6)[1])[3])[3])[3])[3])[2])[1]);})));}),_D8=B(A(_CT,[_wB,_wC,function(_D9,_Da,_){return new F(function(){return _wI(_D9,_D7,_Da,_);});},_D6,_]));return new F(function(){return A(_D3,[new T(function(){return E(E(_D8)[2]);}),_]);});},_Db=[1,I_fromBits([658067456,1164])],_Dc=[0],_Dd=[0,_Dc],_De="forest-collecting",_Df=new T(function(){return B(unCStr("disabled"));}),_Dg=(function(e,c){e.removeAttribute(c);}),_Dh=function(_Di,_Dj,_){var _Dk=__apply(E(_Dg),[1,toJSStr(_Dj),[1,_Di,_w]]);return new F(function(){return _71(_);});},_Dl=function(_Dm,_Dn,_){return new F(function(){return _Dh(E(_Dm),_Dn,_);});},_Do=function(_Dp,_wu,_){return new F(function(){return _Dl(_Dp,_wu,_);});},_Dq=function(_Dr,_){return new F(function(){return _Do(_Dr,_Df,_);});},_Ds=new T(function(){return B(_CT(_3Z,_De,_Dq));}),_Dt=function(_Du,_){var _Dv=E(_Du),_Dw=E(_Dv[3]),_Dx=E(_Dw[3]),_Dy=E(E(_Dx[2])[1]);if(!_Dy[0]){return new F(function(){return _D4(_,[0,_70,[0,_Dv]]);});}else{if(!B(_je(_Dy[1],_Db))){return new F(function(){return _D4(_,[0,_70,[0,_Dv]]);});}else{var _Dz=B(A(_Ds,[_]));return new F(function(){return _D4(_,[0,_70,[0,[1,_,_Dv[2],[1,_,_Dw[2],[1,_,_Dd,_Dx[3]]]]]]);});}}},_DA=function(_DB){var _DC=new T(function(){var _DD=B(_fl(_DB,_95,_3h,_95)),_DE=B(_fl(_rR,_95,_3h,_95)),_DF=B(_fl(_DD[1],_DD[2],_DE[1],_DE[2]));return B(_ri(_rf,_DF[1],_DF[2]));});return [0,new T(function(){return B(_8c(_rS,_DC));}),new T(function(){return B(_7O(_DB,B(_rx(_3i,B(_6O(_DC,_3h)),_rR))));})];},_DG=0,_DH=(function(c,p){p.appendChild(c);}),_DI=function(_DJ,_){var _DK=_DJ[0],_DL=_DJ[1],_DM=Number(_DK),_DN=jsTrunc(_DM),_DO=Number(_DL),_DP=jsTrunc(_DO);return [0,_DN,_DP];},_DQ=(function(){var ms = new Date().getTime();                   return [(ms/1000)|0, ((ms % 1000)*1000)|0];}),_DR=[1,I_fromBits([2808348672,232830643])],_DS=function(_){var _DT=E(_DQ)(),_DU=B(_DI(_DT,_));return new T(function(){var _DV=E(_DU);if(!B(_6G(_DR,_5U))){return B(_8c(B(_6O(B(_8y(E(_DV[1]))),_3h)),B(_5Y(B(_6O(B(_6O(B(_8y(E(_DV[2]))),_3h)),_3h)),_DR))));}else{return E(_6F);}});},_DW=(function(e,p,v){e.setAttribute(p, v);}),_DX=1,_DY=(function(t){return document.createElement(t);}),_DZ=function(_){return new F(function(){return E(_DY)("button");});},_E0=new T(function(){return [0,[2,"type"],"button"];}),_E1=new T(function(){return [0,[2,"class"],"btn btn-default"];}),_E2=[1,_E1,_w],_E3=[1,_E0,_E2],_E4=function(_E5){return E(E(_E5)[3]);},_E6=(function(e,p,v){e.style[p] = v;}),_E7=function(_E8,_E9,_Ea,_Eb){var _Ec=new T(function(){return B(A(_Ah,[_E8,_Ea]));}),_Ed=function(_Ee,_){var _Ef=E(_Ee);if(!_Ef[0]){return _70;}else{var _Eg=E(_Ec),_Eh=E(_DH),_Ei=_Eh(E(_Ef[1]),_Eg),_Ej=_Ef[2];while(1){var _Ek=E(_Ej);if(!_Ek[0]){return _70;}else{var _El=_Eh(E(_Ek[1]),_Eg);_Ej=_Ek[2];continue;}}}},_Em=function(_En,_){while(1){var _Eo=B((function(_Ep,_){var _Eq=E(_Ep);if(!_Eq[0]){return _70;}else{var _Er=_Eq[2],_Es=E(_Eq[1]);if(!_Es[0]){var _Et=_Es[2],_Eu=E(_Es[1]);switch(_Eu[0]){case 0:var _Ev=E(_Ec),_Ew=E(_72),_Ex=_Ew(_Ev,_Eu[1],_Et),_Ey=_Er;while(1){var _Ez=E(_Ey);if(!_Ez[0]){return _70;}else{var _EA=_Ez[2],_EB=E(_Ez[1]);if(!_EB[0]){var _EC=_EB[2],_ED=E(_EB[1]);switch(_ED[0]){case 0:var _EE=_Ew(_Ev,_ED[1],_EC);_Ey=_EA;continue;case 1:var _EF=E(_E6)(_Ev,_ED[1],_EC);_Ey=_EA;continue;default:var _EG=E(_DW)(_Ev,_ED[1],_EC);_Ey=_EA;continue;}}else{var _EH=B(_Ed(_EB[1],_));_Ey=_EA;continue;}}}break;case 1:var _EI=E(_Ec),_EJ=E(_E6),_EK=_EJ(_EI,_Eu[1],_Et),_EL=_Er;while(1){var _EM=E(_EL);if(!_EM[0]){return _70;}else{var _EN=_EM[2],_EO=E(_EM[1]);if(!_EO[0]){var _EP=_EO[2],_EQ=E(_EO[1]);switch(_EQ[0]){case 0:var _ER=E(_72)(_EI,_EQ[1],_EP);_EL=_EN;continue;case 1:var _ES=_EJ(_EI,_EQ[1],_EP);_EL=_EN;continue;default:var _ET=E(_DW)(_EI,_EQ[1],_EP);_EL=_EN;continue;}}else{var _EU=B(_Ed(_EO[1],_));_EL=_EN;continue;}}}break;default:var _EV=E(_Ec),_EW=E(_DW),_EX=_EW(_EV,_Eu[1],_Et),_EY=_Er;while(1){var _EZ=E(_EY);if(!_EZ[0]){return _70;}else{var _F0=_EZ[2],_F1=E(_EZ[1]);if(!_F1[0]){var _F2=_F1[2],_F3=E(_F1[1]);switch(_F3[0]){case 0:var _F4=E(_72)(_EV,_F3[1],_F2);_EY=_F0;continue;case 1:var _F5=E(_E6)(_EV,_F3[1],_F2);_EY=_F0;continue;default:var _F6=_EW(_EV,_F3[1],_F2);_EY=_F0;continue;}}else{var _F7=B(_Ed(_F1[1],_));_EY=_F0;continue;}}}}}else{var _F8=B(_Ed(_Es[1],_));_En=_Er;return null;}}})(_En,_));if(_Eo!=null){return _Eo;}}};return new F(function(){return A(_Ak,[_E9,function(_){return new F(function(){return _Em(_Eb,_);});}]);});},_F9=function(_Fa,_Fb,_Fc,_Fd){var _Fe=B(_Ad(_Fb)),_Ff=function(_Fg){return new F(function(){return A(_E4,[_Fe,new T(function(){return B(_E7(_Fa,_Fb,_Fg,_Fd));}),new T(function(){return B(A(_wd,[_Fe,_Fg]));})]);});};return new F(function(){return A(_vV,[_Fe,_Fc,_Ff]);});},_Fh=new T(function(){return B(_F9(_3o,_3Z,_DZ,_E3));}),_Fi=function(_Fj,_Fk){return [0,1,E(_Fj),_Fk,E(_4e),E(_4e)];},_Fl=function(_Fm,_Fn,_Fo){var _Fp=E(_Fo);if(!_Fp[0]){return new F(function(){return _50(_Fp[2],_Fp[3],_Fp[4],B(_Fl(_Fm,_Fn,_Fp[5])));});}else{return new F(function(){return _Fi(_Fm,_Fn);});}},_Fq=function(_Fr,_Fs,_Ft){var _Fu=E(_Ft);if(!_Fu[0]){return new F(function(){return _4j(_Fu[2],_Fu[3],B(_Fq(_Fr,_Fs,_Fu[4])),_Fu[5]);});}else{return new F(function(){return _Fi(_Fr,_Fs);});}},_Fv=function(_Fw,_Fx,_Fy,_Fz,_FA,_FB,_FC){return new F(function(){return _4j(_Fz,_FA,B(_Fq(_Fw,_Fx,_FB)),_FC);});},_FD=function(_FE,_FF,_FG,_FH,_FI,_FJ,_FK,_FL){var _FM=E(_FG);if(!_FM[0]){var _FN=_FM[1],_FO=_FM[2],_FP=_FM[3],_FQ=_FM[4],_FR=_FM[5];if((imul(3,_FN)|0)>=_FH){if((imul(3,_FH)|0)>=_FN){return [0,(_FN+_FH|0)+1|0,E(_FE),_FF,E(_FM),[0,_FH,E(_FI),_FJ,E(_FK),E(_FL)]];}else{return new F(function(){return _50(_FO,_FP,_FQ,B(_FD(_FE,_FF,_FR,_FH,_FI,_FJ,_FK,_FL)));});}}else{return new F(function(){return _4j(_FI,_FJ,B(_FS(_FE,_FF,_FN,_FO,_FP,_FQ,_FR,_FK)),_FL);});}}else{return new F(function(){return _Fv(_FE,_FF,_FH,_FI,_FJ,_FK,_FL);});}},_FS=function(_FT,_FU,_FV,_FW,_FX,_FY,_FZ,_G0){var _G1=E(_G0);if(!_G1[0]){var _G2=_G1[1],_G3=_G1[2],_G4=_G1[3],_G5=_G1[4],_G6=_G1[5];if((imul(3,_FV)|0)>=_G2){if((imul(3,_G2)|0)>=_FV){return [0,(_FV+_G2|0)+1|0,E(_FT),_FU,[0,_FV,E(_FW),_FX,E(_FY),E(_FZ)],E(_G1)];}else{return new F(function(){return _50(_FW,_FX,_FY,B(_FD(_FT,_FU,_FZ,_G2,_G3,_G4,_G5,_G6)));});}}else{return new F(function(){return _4j(_G3,_G4,B(_FS(_FT,_FU,_FV,_FW,_FX,_FY,_FZ,_G5)),_G6);});}}else{return new F(function(){return _Fl(_FT,_FU,[0,_FV,E(_FW),_FX,E(_FY),E(_FZ)]);});}},_G7=function(_G8,_G9,_Ga,_Gb){var _Gc=E(_Ga);if(!_Gc[0]){var _Gd=_Gc[1],_Ge=_Gc[2],_Gf=_Gc[3],_Gg=_Gc[4],_Gh=_Gc[5],_Gi=E(_Gb);if(!_Gi[0]){var _Gj=_Gi[1],_Gk=_Gi[2],_Gl=_Gi[3],_Gm=_Gi[4],_Gn=_Gi[5];if((imul(3,_Gd)|0)>=_Gj){if((imul(3,_Gj)|0)>=_Gd){return [0,(_Gd+_Gj|0)+1|0,E(_G8),_G9,E(_Gc),E(_Gi)];}else{return new F(function(){return _50(_Ge,_Gf,_Gg,B(_FD(_G8,_G9,_Gh,_Gj,_Gk,_Gl,_Gm,_Gn)));});}}else{return new F(function(){return _4j(_Gk,_Gl,B(_FS(_G8,_G9,_Gd,_Ge,_Gf,_Gg,_Gh,_Gm)),_Gn);});}}else{return new F(function(){return _Fl(_G8,_G9,_Gc);});}}else{return new F(function(){return _Fq(_G8,_G9,_Gb);});}},_Go=function(_Gp,_Gq,_Gr,_Gs){var _Gt=E(_Gp);if(_Gt==1){var _Gu=E(_Gs);return (_Gu[0]==0)?[0,new T(function(){return [0,1,E(_Gq),_Gr,E(_4e),E(_4e)];}),_w,_w]:(B(_41(_Gq,E(_Gu[1])[1]))==0)?[0,new T(function(){return [0,1,E(_Gq),_Gr,E(_4e),E(_4e)];}),_Gu,_w]:[0,new T(function(){return [0,1,E(_Gq),_Gr,E(_4e),E(_4e)];}),_w,_Gu];}else{var _Gv=B(_Go(_Gt>>1,_Gq,_Gr,_Gs)),_Gw=_Gv[1],_Gx=_Gv[3],_Gy=E(_Gv[2]);if(!_Gy[0]){return [0,_Gw,_w,_Gx];}else{var _Gz=E(_Gy[1]),_GA=_Gz[1],_GB=_Gz[2],_GC=E(_Gy[2]);if(!_GC[0]){return [0,new T(function(){return B(_Fl(_GA,_GB,_Gw));}),_w,_Gx];}else{var _GD=E(_GC[1]),_GE=_GD[1];if(!B(_41(_GA,_GE))){var _GF=B(_Go(_Gt>>1,_GE,_GD[2],_GC[2]));return [0,new T(function(){return B(_G7(_GA,_GB,_Gw,_GF[1]));}),_GF[2],_GF[3]];}else{return [0,_Gw,_w,_Gy];}}}}},_GG=function(_GH,_GI){while(1){var _GJ=E(_GI);if(!_GJ[0]){return E(_GH);}else{var _GK=E(_GJ[1]),_GL=B(_5F(_GK[1],_GK[2],_GH));_GH=_GL;_GI=_GJ[2];continue;}}},_GM=function(_GN,_GO,_GP,_GQ){return new F(function(){return _GG(B(_5F(_GO,_GP,_GN)),_GQ);});},_GR=function(_GS,_GT,_GU){var _GV=E(_GT);return new F(function(){return _GG(B(_5F(_GV[1],_GV[2],_GS)),_GU);});},_GW=function(_GX,_GY,_GZ){while(1){var _H0=E(_GZ);if(!_H0[0]){return E(_GY);}else{var _H1=E(_H0[1]),_H2=_H1[1],_H3=_H1[2],_H4=E(_H0[2]);if(!_H4[0]){return new F(function(){return _Fl(_H2,_H3,_GY);});}else{var _H5=E(_H4[1]),_H6=_H5[1];if(!B(_41(_H2,_H6))){var _H7=B(_Go(_GX,_H6,_H5[2],_H4[2])),_H8=_H7[1],_H9=E(_H7[3]);if(!_H9[0]){var _Ha=_GX<<1,_Hb=B(_G7(_H2,_H3,_GY,_H8));_GX=_Ha;_GY=_Hb;_GZ=_H7[2];continue;}else{return new F(function(){return _GR(B(_G7(_H2,_H3,_GY,_H8)),_H9[1],_H9[2]);});}}else{return new F(function(){return _GM(_GY,_H2,_H3,_H4);});}}}}},_Hc=function(_Hd,_He,_Hf,_Hg,_Hh){var _Hi=E(_Hh);if(!_Hi[0]){return new F(function(){return _Fl(_Hf,_Hg,_He);});}else{var _Hj=E(_Hi[1]),_Hk=_Hj[1];if(!B(_41(_Hf,_Hk))){var _Hl=B(_Go(_Hd,_Hk,_Hj[2],_Hi[2])),_Hm=_Hl[1],_Hn=E(_Hl[3]);if(!_Hn[0]){return new F(function(){return _GW(_Hd<<1,B(_G7(_Hf,_Hg,_He,_Hm)),_Hl[2]);});}else{return new F(function(){return _GR(B(_G7(_Hf,_Hg,_He,_Hm)),_Hn[1],_Hn[2]);});}}else{return new F(function(){return _GM(_He,_Hf,_Hg,_Hi);});}}},_Ho=function(_Hp){var _Hq=E(_Hp);if(!_Hq[0]){return [1];}else{var _Hr=E(_Hq[1]),_Hs=_Hr[1],_Ht=_Hr[2],_Hu=E(_Hq[2]);if(!_Hu[0]){return [0,1,E(_Hs),_Ht,E(_4e),E(_4e)];}else{var _Hv=_Hu[2],_Hw=E(_Hu[1]),_Hx=_Hw[1],_Hy=_Hw[2];if(!B(_41(_Hs,_Hx))){return new F(function(){return _Hc(1,[0,1,E(_Hs),_Ht,E(_4e),E(_4e)],_Hx,_Hy,_Hv);});}else{return new F(function(){return _GM([0,1,E(_Hs),_Ht,E(_4e),E(_4e)],_Hx,_Hy,_Hv);});}}}},_Hz=200,_HA=[0,_Hz],_HB=[0,_AH],_HC=[1,_,_HB,_0],_HD=[1,_,_HA,_HC],_HE=[0,_HD],_HF=[0,_A0,_HE],_HG=[0,_AK],_HH=[1,_,_HG,_0],_HI=[1,_,_HA,_HH],_HJ=[0,_HI],_HK=[0,_A4,_HJ],_HL=[0,_AN],_HM=[1,_,_HL,_0],_HN=[1,_,_HA,_HM],_HO=[0,_HN],_HP=[0,_A2,_HO],_HQ=[1,_HP,_w],_HR=[1,_HK,_HQ],_HS=[1,_HF,_HR],_HT=new T(function(){return B(_Ho(_HS));}),_HU=function(_HV,_HW){while(1){var _HX=B((function(_HY,_HZ){var _I0=E(_HZ);if(!_I0[0]){_HV=[1,[0,_I0[2],_I0[3]],new T(function(){return B(_HU(_HY,_I0[5]));})];_HW=_I0[4];return null;}else{return E(_HY);}})(_HV,_HW));if(_HX!=null){return _HX;}}},_I1=new T(function(){return B(_HU(_w,_HT));}),_I2=new T(function(){return B(unCStr(")"));}),_I3=[1,I_fromBits([3948404736,6984])],_I4=[1,100],_I5=[1,I_fromBits([2764472320,232830])],_I6="shop",_I7=[0,0],_I8=[1,_I7],_I9=[0,_I8],_Ia="outskirts-time",_Ib="calendar",_Ic=function(_Id,_Ie,_){return new F(function(){return _74(E(_Id),_Ie,_);});},_If=new T(function(){return B(unCStr("</tr>"));}),_Ig=[1,_If,_w],_Ih=new T(function(){return B(unCStr("</td>"));}),_Ii=function(_Ij){var _Ik=E(_Ij);if(!_Ik[0]){return E(_Ig);}else{var _Il=new T(function(){return B(unAppCStr("<td>",new T(function(){var _Im=E(_Ik[1]);if(!_Im){return E(_Ih);}else{return B(_4(B(_e(0,_Im,_w)),_Ih));}})));});return [1,_Il,new T(function(){return B(_Ii(_Ik[2]));})];}},_In=new T(function(){return B(unCStr("<tr>"));}),_Io=function(_Ip){var _Iq=E(_Ip);if(!_Iq[0]){return [0];}else{var _Ir=new T(function(){return B(_Io(_Iq[2]));}),_Is=function(_It){var _Iu=E(_It);if(!_Iu[0]){return E(_Ir);}else{return new F(function(){return _4(_Iu[1],new T(function(){return B(_Is(_Iu[2]));},1));});}},_Iv=_In,_Iw=new T(function(){return B(_Ii(_Iq[1]));});return new F(function(){return _4(_Iv,new T(function(){return B(_Is(_Iw));},1));});}},_Ix=function(_Iy,_Iz){while(1){var _IA=E(_Iz);if(!_IA[0]){return [0];}else{var _IB=_IA[2],_IC=E(_Iy);if(_IC==1){return E(_IB);}else{_Iy=_IC-1|0;_Iz=_IB;continue;}}}},_ID=function(_IE,_IF,_IG){var _IH=E(_IE);if(_IH==1){return E(_IG);}else{return new F(function(){return _Ix(_IH-1|0,_IG);});}},_II=function(_IJ,_IK){var _IL=E(_IK);if(!_IL[0]){return [0];}else{var _IM=_IL[1],_IN=E(_IJ);return (_IN==1)?[1,_IM,_w]:[1,_IM,new T(function(){return B(_II(_IN-1|0,_IL[2]));})];}},_IO=function(_IP,_IQ){var _IR=E(_IQ);if(!_IR[0]){return [0];}else{var _IS=_IR[1],_IT=_IR[2];return [1,new T(function(){if(0>=_IP){return [0];}else{return B(_II(_IP,_IR));}}),new T(function(){if(_IP>0){return B(_IO(_IP,B(_ID(_IP,_IS,_IT))));}else{return B(_IU(_IP,_IS,_IT));}})];}},_IU=function(_IV,_IW,_IX){return [1,new T(function(){if(0>=_IV){return [0];}else{return B(_II(_IV,[1,_IW,_IX]));}}),new T(function(){if(_IV>0){return B(_IO(_IV,B(_ID(_IV,_IW,_IX))));}else{return B(_IU(_IV,_IW,_IX));}})];},_IY=function(_IZ,_J0){var _J1=E(_J0);if(!_J1[0]){return [0];}else{var _J2=_J1[1],_J3=_J1[2];return [1,new T(function(){var _J4=E(_IZ);if(0>=_J4){return [0];}else{return B(_II(_J4,_J1));}}),new T(function(){var _J5=E(_IZ);if(_J5>0){return B(_IO(_J5,B(_ID(_J5,_J2,_J3))));}else{return B(_IU(_J5,_J2,_J3));}})];}},_J6=function(_J7,_J8){while(1){var _J9=E(_J7);if(_J9==4){return _J8+1|0;}else{var _Ja=_J8+1|0;_J7=_J9+1|0;_J8=_Ja;continue;}}},_Jb=new T(function(){return B(_J6(0,0));}),_Jc=0,_Jd=new T(function(){return B(_e(0,4,_I2));}),_Je=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_Jd));}),_Jf=function(_Jg){return new F(function(){return err(B(unAppCStr("toEnum{Date}: tag (",new T(function(){return B(_e(0,_Jg,_Je));}))));});},_Jh=function(_Ji){var _Jj=1+_Ji|0;if(_Jj<0){return new F(function(){return _Jf(_Jj);});}else{if(_Jj>4){return new F(function(){return _Jf(_Jj);});}else{return _Jj;}}},_Jk=new T(function(){return B(_Jh(0));}),_Jl=new T(function(){return B(_Jh(1));}),_Jm=new T(function(){return B(_Jh(2));}),_Jn=new T(function(){return B(_Jh(3));}),_Jo=[1,_Jc,_w],_Jp=function(_Jq){var _Jr=E(_Jq);return (_Jr==1)?E(_Jo):[1,_Jc,new T(function(){return B(_Jp(_Jr-1|0));})];},_Js=new T(function(){return B(_Jp(5));}),_Jt=new T(function(){return B(_Jp(4));}),_Ju=new T(function(){return B(_Jp(3));}),_Jv=new T(function(){return B(_Jp(2));}),_Jw=new T(function(){return B(_Jp(1));}),_Jx=function(_Jy,_Jz){if(_Jy<=20){var _JA=new T(function(){return B(_Jx(_Jy+1|0,new T(function(){switch(E(_Jz)){case 0:return E(_Jk);break;case 1:return E(_Jl);break;case 2:return E(_Jm);break;case 3:return E(_Jn);break;default:return 0;}})));});return [1,_Jy,_JA];}else{switch(E(_Jz)){case 0:return E(_Js);case 1:return E(_Jt);case 2:return E(_Ju);case 3:return E(_Jv);default:return E(_Jw);}}},_JB=function(_JC,_JD,_JE){if(_JC<=20){if(!E(_JE)){var _JF=new T(function(){return B(_JB(_JC,new T(function(){switch(E(_JD)){case 0:return E(_Jk);break;case 1:return E(_Jl);break;case 2:return E(_Jm);break;case 3:return E(_Jn);break;default:return 0;}}),new T(function(){switch(E(_JD)){case 0:if(E(_Jk)==2){return true;}else{return false;}break;case 1:if(E(_Jl)==2){return true;}else{return false;}break;case 2:if(E(_Jm)==2){return true;}else{return false;}break;case 3:if(E(_Jn)==2){return true;}else{return false;}break;default:return false;}},1)));});return [1,_Jc,_JF];}else{var _JG=new T(function(){return B(_Jx(_JC+1|0,new T(function(){switch(E(_JD)){case 0:return E(_Jk);break;case 1:return E(_Jl);break;case 2:return E(_Jm);break;case 3:return E(_Jn);break;default:return 0;}})));});return [1,_JC,_JG];}}else{switch(E(_JD)){case 0:return E(_Js);case 1:return E(_Jt);case 2:return E(_Ju);case 3:return E(_Jv);default:return E(_Jw);}}},_JH=function(_JI){if(_JI<=20){var _JJ=new T(function(){return B(_JB(_JI,_Jk,new T(function(){if(E(_Jk)==2){return true;}else{return false;}},1)));});return [1,_Jc,_JJ];}else{return E(_Js);}},_JK=new T(function(){return B(_JH(1));}),_JL=new T(function(){return B(_IY(_Jb,_JK));}),_JM=new T(function(){return B(_Io(_JL));}),_JN=function(_JO,_){return new F(function(){return _Ic(_JO,_JM,_);});},_JP=[0,_Jc],_JQ=1000,_JR=[0,_AE,_JQ],_JS=[0,_A6,_Jc],_JT=[1,_JS,_w],_JU=[1,_JR,_JT],_JV=new T(function(){return B(_Ho(_JU));}),_JW=[0,_JV],_JX=[1,I_fromBits([276447232,23283])],_JY=[0,_JX],_JZ=function(_K0){return E(E(_K0)[1]);},_K1=function(_K2){return E(E(_K2)[2]);},_K3=function(_K4){return E(E(_K4)[1]);},_K5=function(_){return new F(function(){return nMV(_2s);});},_K6=new T(function(){return B(_2L(_K5));}),_K7=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_K8=function(_K9){return E(E(_K9)[2]);},_Ka=function(_Kb,_Kc,_Kd,_Ke,_Kf,_Kg){var _Kh=B(_JZ(_Kb)),_Ki=B(_Ad(_Kh)),_Kj=new T(function(){return B(_Ak(_Kh));}),_Kk=new T(function(){return B(_wd(_Ki));}),_Kl=new T(function(){return B(A(_Ah,[_Kc,_Ke]));}),_Km=new T(function(){return B(A(_K3,[_Kd,_Kf]));}),_Kn=function(_Ko){return new F(function(){return A(_Kk,[[0,_Km,_Kl,_Ko]]);});},_Kp=function(_Kq){var _Kr=new T(function(){var _Ks=new T(function(){var _Kt=__createJSFunc(2,function(_Ku,_){var _Kv=B(A(E(_Kq),[_Ku,_]));return _2P;}),_Kw=_Kt;return function(_){return new F(function(){return E(_K7)(E(_Kl),E(_Km),_Kw);});};});return B(A(_Kj,[_Ks]));});return new F(function(){return A(_vV,[_Ki,_Kr,_Kn]);});},_Kx=new T(function(){var _Ky=new T(function(){return B(_Ak(_Kh));}),_Kz=function(_KA){var _KB=new T(function(){return B(A(_Ky,[function(_){var _=wMV(E(_K6),[1,_KA]);return new F(function(){return A(_K1,[_Kd,_Kf,_KA,_]);});}]));});return new F(function(){return A(_vV,[_Ki,_KB,_Kg]);});};return B(A(_K8,[_Kb,_Kz]));});return new F(function(){return A(_vV,[_Ki,_Kx,_Kp]);});},_KC=function(_KD){var _KE=B(_DA(_KD));return [0,_KE[1],_KE[2]];},_KF=(function(t,f){window.setInterval(f,t);}),_KG=(function(t,f){window.setTimeout(f,t);}),_KH=function(_KI,_KJ,_KK){var _KL=B(_JZ(_KI)),_KM=new T(function(){return B(_Ak(_KL));}),_KN=function(_KO){var _KP=function(_){var _KQ=E(_KJ);if(!_KQ[0]){var _KR=B(A(_KO,[_70])),_KS=__createJSFunc(0,function(_){var _KT=B(A(_KR,[_]));return _2P;}),_KU=E(_KG)(_KQ[1],_KS);return new T(function(){var _KV=Number(_KU),_KW=jsTrunc(_KV);return [0,_KW,E(_KQ)];});}else{var _KX=B(A(_KO,[_70])),_KY=__createJSFunc(0,function(_){var _KZ=B(A(_KX,[_]));return _2P;}),_L0=E(_KF)(_KQ[1],_KY);return new T(function(){var _L1=Number(_L0),_L2=jsTrunc(_L1);return [0,_L2,E(_KQ)];});}};return new F(function(){return A(_KM,[_KP]);});},_L3=new T(function(){return B(A(_K8,[_KI,function(_L4){return E(_KK);}]));});return new F(function(){return A(_vV,[B(_Ad(_KL)),_L3,_KN]);});},_L5=function(_){var _L6=B(_DS(_)),_L7=nMV([0,[1,_,_JP,[1,_,_JW,[1,_,_Dd,[1,_,_JY,[1,_,[0,new T(function(){return B(_KC(_L6));})],_0]]]]]]),_L8=_L7,_L9=B(A(_CT,[_3Z,_Ib,_JN,_])),_La=function(_){var _Lb=rMV(_L8),_Lc=new T(function(){var _Ld=E(E(_Lb)[1]),_Le=new T(function(){var _Lf=E(_Ld[3]),_Lg=new T(function(){var _Lh=E(_Lf[3]),_Li=new T(function(){var _Lj=E(_Lh[3]);return [1,_,[0,new T(function(){return B(_8c(E(_Lj[2])[1],_I3));})],_Lj[3]];});return [1,_,_Lh[2],_Li];});return [1,_,_Lf[2],_Lg];});return [1,_,_Ld[2],_Le];}),_=wMV(_L8,[0,_Lc]);return _70;},_Lk=function(_Ll,_){return new F(function(){return _La(_);});},_Lm=B(A(_CT,[_3Z,_Ia,function(_Ln){return new F(function(){return _Ka(_40,_3o,_3g,_Ln,_DG,_Lk);});},_])),_Lo=function(_Lp){var _Lq=function(_Lr,_){var _Ls=toJSStr(E(_Df)),_Lt=E(_DW)(E(_Lp),_Ls,_Ls),_Lu=rMV(_L8),_Lv=new T(function(){var _Lw=E(E(_Lu)[1]),_Lx=new T(function(){var _Ly=E(_Lw[3]);return [1,_,_Ly[2],new T(function(){var _Lz=E(_Ly[3]),_LA=E(_Lz[2]);return [1,_,_I9,_Lz[3]];})];});return [1,_,_Lw[2],_Lx];}),_=wMV(_L8,[0,_Lv]);return _70;};return new F(function(){return _Ka(_40,_3o,_3g,_Lp,_DG,_Lq);});},_LB=B(A(_CT,[_3Z,_De,_Lo,_])),_LC=function(_LD,_){var _LE=E(_I1);if(!_LE[0]){return _70;}else{var _LF=E(_LE[1]),_LG=_LF[1],_LH=B(A(_Fh,[_])),_LI=E(_LH),_LJ=E(_LD),_LK=E(_DH),_LL=_LK(_LI,_LJ),_LM=E(E(_LF[2])[1]),_LN=new T(function(){return B(unAppCStr("(-",new T(function(){return B(_4(B(_e(0,E(E(_LM[2])[1]),_w)),_I2));})));},1),_LO=B(_74(_LI,B(_4(E(E(_LM[3])[2])[1],_LN)),_)),_LP=function(_LQ,_){var _LR=toJSStr(E(_Df)),_LS=E(_DW)(_LI,_LR,_LR),_LT=rMV(_L8),_LU=E(E(_LT)[1]),_LV=_LU[2],_LW=E(_LU[3]),_LX=_LW[3],_LY=E(_LW[2])[1];if(!B(_5P(_LG,_LY))){var _=wMV(_L8,[0,[1,_,_LV,[1,_,[0,new T(function(){return B(_5F(_LG,_DX,_LY));})],_LX]]]);return _70;}else{var _LZ=new T(function(){return B(_5F(_LG,new T(function(){return B(_4a(_LG,_LY))+1|0;}),_LY));}),_=wMV(_L8,[0,[1,_,_LV,[1,_,[0,_LZ],_LX]]]);return _70;}},_M0=B(A(_Ka,[_40,_3o,_3g,_LI,_DG,_LP,_])),_M1=_LE[2];while(1){var _M2=B((function(_M3,_){var _M4=E(_M3);if(!_M4[0]){return _70;}else{var _M5=E(_M4[1]),_M6=_M5[1],_M7=B(A(_Fh,[_])),_M8=E(_M7),_M9=_LK(_M8,_LJ),_Ma=E(E(_M5[2])[1]),_Mb=new T(function(){return B(unAppCStr("(-",new T(function(){return B(_4(B(_e(0,E(E(_Ma[2])[1]),_w)),_I2));})));},1),_Mc=B(_74(_M8,B(_4(E(E(_Ma[3])[2])[1],_Mb)),_)),_Md=function(_Me,_){var _Mf=toJSStr(E(_Df)),_Mg=E(_DW)(_M8,_Mf,_Mf),_Mh=rMV(_L8),_Mi=E(E(_Mh)[1]),_Mj=_Mi[2],_Mk=E(_Mi[3]),_Ml=_Mk[3],_Mm=E(_Mk[2])[1];if(!B(_5P(_M6,_Mm))){var _=wMV(_L8,[0,[1,_,_Mj,[1,_,[0,new T(function(){return B(_5F(_M6,_DX,_Mm));})],_Ml]]]);return _70;}else{var _Mn=new T(function(){return B(_5F(_M6,new T(function(){return B(_4a(_M6,_Mm))+1|0;}),_Mm));}),_=wMV(_L8,[0,[1,_,_Mj,[1,_,[0,_Mn],_Ml]]]);return _70;}},_Mo=B(A(_Ka,[_40,_3o,_3g,_M8,_DG,_Md,_]));_M1=_M4[2];return null;}})(_M1,_));if(_M2!=null){return _M2;}}}},_Mp=B(A(_CT,[_3Z,_I6,_LC,_])),_Mq=function(_){var _Mr=rMV(_L8),_Ms=E(E(_Mr)[1]),_Mt=E(_Ms[2]),_Mu=E(_Ms[3]),_Mv=_Mu[2],_Mw=E(_Mu[3]),_Mx=_Mw[3],_My=new T(function(){return E(E(E(_Mx)[2])[1]);}),_Mz=new T(function(){var _MA=E(_Mx),_MB=new T(function(){var _MC=E(_MA[3]),_MD=new T(function(){var _ME=B(_DA(new T(function(){var _MF=E(E(_MC[2])[1]);return B(_8c(B(_6W(_3i,_My,_I5)),B(_rT(_MF[1],_MF[2]))));})));return [0,_ME[1],_ME[2]];});return [1,_,[0,_MD],_MC[3]];});return [1,_,_MA[2],_MB];}),_MG=E(E(_Mw[2])[1]);if(!_MG[0]){var _MH=B(_Dt([1,_,[0,new T(function(){return E(E(_Mt)[1])+1|0;})],[1,_,_Mv,[1,_,_Dd,_Mz]]],_)),_MI=E(_MH),_=wMV(_L8,E(_MI[2]));return _MI[1];}else{var _MJ=E(E(_Mt)[1])+1|0,_MK=new T(function(){return B(_8c(_MG[1],B(_6W(_3i,_My,_I5))));});if(!B(_7X(_MJ,10))){var _ML=new T(function(){var _MM=new T(function(){var _MN=E(_Mv)[1];return B(_5F(_A6,new T(function(){return B(_4a(_A6,_MN))+1|0;}),_MN));});return [1,_,[0,_MM],[1,_,[0,[1,_MK]],_Mz]];}),_MO=B(_Dt([1,_,[0,_MJ],_ML],_)),_MP=E(_MO),_=wMV(_L8,E(_MP[2]));return _MP[1];}else{var _MQ=B(_Dt([1,_,[0,_MJ],[1,_,_Mv,[1,_,[0,[1,_MK]],_Mz]]],_)),_MR=E(_MQ),_=wMV(_L8,E(_MR[2]));return _MR[1];}}};return new F(function(){return A(_KH,[_40,_I4,_Mq,_]);});},_MS=function(_){return new F(function(){return _L5(_);});};
var hasteMain = function() {B(A(_MS, [0]));};window.onload = hasteMain;