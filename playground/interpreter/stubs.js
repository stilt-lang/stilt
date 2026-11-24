// The calls of the reference interpreter that js_of_ocaml's runtime doesn't give, as the
// playground gives them in the browser: no C library is found or called, a path is its own real
// path, since the files a run writes are in memory and hold no link, a file in memory has the
// status of a regular file or a directory, and is created or renamed only in a directory that
// exists, standard input is empty and at its end, and sleeping
// waits, in the run's worker. And `Printf`'s formatting of floats, which
// js_of_ocaml's runtime does through JavaScript's `toFixed` and `toExponential`, which round a
// tie away from zero, from the exact digits instead, a tie to even, as C's printf rounds them
// (std.precision and std.scientific-notation).

//Provides: stilt_playground_no_c
//Requires: caml_failwith
function stilt_playground_no_c() {
  caml_failwith("a program in the browser calls no C");
}

//Provides: stilt_c_load
function stilt_c_load(_name) {
  return 0;
}

//Provides: stilt_c_symbol
//Requires: stilt_playground_no_c
function stilt_c_symbol(_name) {
  stilt_playground_no_c();
}

//Provides: stilt_c_call
//Requires: stilt_playground_no_c
function stilt_c_call(_f, _kinds, _args, _result) {
  stilt_playground_no_c();
}

//Provides: stilt_c_alloc
//Requires: stilt_playground_no_c
function stilt_c_alloc(_size) {
  stilt_playground_no_c();
}

//Provides: stilt_c_free
//Requires: stilt_playground_no_c
function stilt_c_free(_at) {
  stilt_playground_no_c();
}

//Provides: stilt_c_peek
//Requires: stilt_playground_no_c
function stilt_c_peek(_at, _kind, _signed) {
  stilt_playground_no_c();
}

//Provides: stilt_c_poke
//Requires: stilt_playground_no_c
function stilt_c_poke(_at, _kind, _value) {
  stilt_playground_no_c();
}

//Provides: stilt_c_string
//Requires: stilt_playground_no_c
function stilt_c_string(_at) {
  stilt_playground_no_c();
}

//Provides: stilt_c_write_bytes
//Requires: stilt_playground_no_c
function stilt_c_write_bytes(_at, _bytes) {
  stilt_playground_no_c();
}

//Provides: caml_unix_realpath
function caml_unix_realpath(path) {
  return path;
}

//Provides: caml_unix_select
function caml_unix_select(read, write, except, _timeout) {
  return [0, read, write, except];
}

//Provides: caml_unix_sleep
function caml_unix_sleep(seconds) {
  var until = Date.now() + seconds * 1000;
  while (Date.now() < until) {}
  return 0;
}

//Provides: stilt_playground_stats
function stilt_playground_stats(kind, size) {
  // A Unix.stats record: of a regular file (kind 0) or a directory (kind 1), in memory.
  var now = Date.now() / 1000;
  return [0, 0, 0, kind, kind === 1 ? 0o755 : 0o644, 1, 0, 0, 0, size, now, now, now];
}

//Provides: stilt_playground_device
//Requires: MlFakeDevice, caml_raise_system_error
var stilt_playground_device = (function () {
  // Fails, as the system does, unless the directory that would hold `name` exists.
  function parent(device, name, call, raise_unix) {
    var found = /^(.*)\/[^/]+/.exec(name);
    var dir = (found && found[1]) || "";
    if (!device.exists(dir))
      caml_raise_system_error(raise_unix, "ENOENT", call, "no such file or directory", device.nm(name));
    if (!device.is_dir(dir))
      caml_raise_system_error(raise_unix, "ENOTDIR", call, "not a directory", device.nm(name));
  }
  var open = MlFakeDevice.prototype.open;
  MlFakeDevice.prototype.open = function (name, f, perms, raise_unix) {
    if (f.create && !this.exists(name)) parent(this, name, "open", raise_unix);
    return open.call(this, name, f, perms, raise_unix);
  };
  var rename = MlFakeDevice.prototype.rename;
  MlFakeDevice.prototype.rename = function (from, into, raise_unix) {
    if (this.exists(from)) parent(this, into, "rename", raise_unix);
    return rename.call(this, from, into, raise_unix);
  };
  return MlFakeDevice;
})();

//Provides: stilt_playground_stat
//Requires: resolve_fs_device, caml_raise_system_error, stilt_playground_stats
//Requires: stilt_playground_device
function stilt_playground_stat(name, call) {
  var root = resolve_fs_device(name, 1);
  if (root.device[call]) return root.device[call](root.rest, false, true);
  var device = root.device;
  if (root.rest === "" || device.is_dir(root.rest)) return stilt_playground_stats(1, 0);
  if (device.exists(root.rest)) {
    return stilt_playground_stats(0, device.content[root.rest].length());
  }
  caml_raise_system_error(1, "ENOENT", call, "no such file or directory", name);
}

//Provides: caml_unix_stat
//Requires: stilt_playground_stat
function caml_unix_stat(name) {
  return stilt_playground_stat(name, "stat");
}

//Provides: caml_unix_lstat
//Requires: stilt_playground_stat
function caml_unix_lstat(name) {
  return stilt_playground_stat(name, "lstat");
}

//Provides: caml_unix_fstat
//Requires: caml_unix_lookup_file, stilt_playground_stats, stilt_playground_device
function caml_unix_fstat(fd) {
  var file = caml_unix_lookup_file(fd, "fstat");
  if (file.stat) return file.stat(false);
  return stilt_playground_stats(0, file.length());
}

//Provides: stilt_playground_scaled
function stilt_playground_scaled(x, k) {
  // round_half_even(x * 10^k), x finite and >= 0, x being m * 2^e exactly.
  var view = new DataView(new ArrayBuffer(8));
  view.setFloat64(0, x);
  var hi = view.getUint32(0);
  var biased = (hi >>> 20) & 0x7ff;
  var m = (BigInt(hi & 0xfffff) << 32n) | BigInt(view.getUint32(4));
  var e = biased === 0 ? -1074 : biased - 1075;
  if (biased !== 0) m |= 1n << 52n;
  var num = m;
  var den = 1n;
  if (k >= 0) num *= 10n ** BigInt(k);
  else den = 10n ** BigInt(-k);
  if (e >= 0) num <<= BigInt(e);
  else den <<= BigInt(-e);
  var q = num / den;
  var twice = (num % den) * 2n;
  if (twice > den || (twice === den && q & 1n)) q += 1n;
  return q;
}

//Provides: stilt_playground_fixed
//Requires: stilt_playground_scaled, caml_str_repeat
function stilt_playground_fixed(x, places) {
  var q = stilt_playground_scaled(x, places).toString();
  if (places === 0) return q;
  if (q.length <= places) q = caml_str_repeat(places + 1 - q.length, "0") + q;
  return q.slice(0, q.length - places) + "." + q.slice(q.length - places);
}

//Provides: stilt_playground_exponential
//Requires: stilt_playground_scaled, caml_str_repeat
function stilt_playground_exponential(x, places) {
  if (x === 0) return (places > 0 ? "0." + caml_str_repeat(places, "0") : "0") + "e+00";
  var e10 = Math.floor(Math.log10(x));
  for (;;) {
    var s = stilt_playground_scaled(x, places - e10).toString();
    if (s.length === places + 1) {
      var m = places > 0 ? s.charAt(0) + "." + s.slice(1) : s;
      var abs = Math.abs(e10);
      return m + "e" + (e10 < 0 ? "-" : "+") + (abs < 10 ? "0" : "") + abs;
    }
    e10 += s.length - (places + 1);
  }
}

//Provides: caml_format_float const
//Requires: caml_parse_format, caml_finish_formatting
//Requires: stilt_playground_fixed, stilt_playground_exponential
function caml_format_float(fmt, x) {
  var f = caml_parse_format(fmt);
  var prec = f.prec < 0 ? 6 : f.prec;
  var s;
  if (x < 0 || (x === 0 && 1 / x === Number.NEGATIVE_INFINITY)) {
    f.sign = -1;
    x = -x;
  }
  if (Number.isNaN(x)) {
    s = "nan";
    f.filler = " ";
  } else if (!Number.isFinite(x)) {
    s = "inf";
    f.filler = " ";
  } else if (f.conv === "e") {
    s = stilt_playground_exponential(x, prec);
  } else if (f.conv === "f") {
    s = stilt_playground_fixed(x, prec);
  } else {
    // %g: the shorter of %e and %f at `prec` significant digits, without trailing zeros.
    prec = prec ? prec : 1;
    s = stilt_playground_exponential(x, prec - 1);
    var exp = +s.slice(s.indexOf("e") + 1);
    var trim = function (t) {
      return t.indexOf(".") < 0 ? t : t.replace(/0+$/, "").replace(/\.$/, "");
    };
    if (exp < -4 || exp >= prec) {
      var j = s.indexOf("e");
      s = trim(s.slice(0, j)) + s.slice(j);
    } else {
      s = trim(stilt_playground_fixed(x, prec - 1 - exp));
    }
  }
  return caml_finish_formatting(f, s);
}
