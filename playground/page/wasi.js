// A host of WASI preview 1 for the playground's compiler, a command module: one run of it, with
// its arguments, a current directory that holds the files it is given, an empty standard input,
// and what it writes on stdout and stderr. Every other call of WASI fails with ENOSYS, and a call
// of an import outside WASI traps, as wasmtime's `unknown-imports-trap` does. It runs in a page,
// in a worker, and under Node for the playground's test.

"use strict";

{
  const SUCCESS = 0;
  const BADF = 8;
  const INVAL = 28;
  const NOENT = 44;
  const NOSYS = 52;
  const CHARACTER_DEVICE = 2;
  const DIRECTORY = 3;
  const REGULAR_FILE = 4;
  // The flag of `path_open` that asks for a directory.
  const O_DIRECTORY = 2;
  // The descriptor of the current directory, the one that the module's C library asks for.
  const CWD = 3;

  /** How the module ended, by `proc_exit`. */
  class Exit {
    constructor(code) {
      this.code = code;
    }
  }

  /** The name of a file of the current directory that `path` gives, or "" for the directory. */
  function local(path) {
    let name = path;
    while (name.startsWith("./")) name = name.slice(2);
    return name === "." ? "" : name;
  }

  /**
   * The state of one run over `files`, a map from a name to its bytes, with `memory()`: its
   * arguments, its open descriptors, what it writes into `written`, and the ways to read and
   * write its memory.
   */
  function state(memory, args, files, written) {
    const view = () => new DataView(memory().buffer);
    const bytes = () => new Uint8Array(memory().buffer);
    const decoder = new TextDecoder();
    const s = {
      view,
      bytes,
      files,
      written,
      argv: args.map((a) => new TextEncoder().encode(a + "\0")),
      open: new Map([
        [0, { kind: "input", at: 0, data: new Uint8Array(0) }],
        [1, { kind: "output", stream: "stdout" }],
        [2, { kind: "output", stream: "stderr" }],
        [CWD, { kind: "directory" }],
      ]),
      next: CWD + 1,
      string: (at, len) => decoder.decode(bytes().subarray(at, at + len)),
    };
    // Calls `f` on each buffer of the `count` at `iovs`, until one isn't used whole.
    s.each = (iovs, count, f) => {
      let total = 0;
      for (let i = 0; i < count; i++) {
        const len = view().getUint32(iovs + 8 * i + 4, true);
        const done = f(view().getUint32(iovs + 8 * i, true), len);
        total += done;
        if (done < len) break;
      }
      return total;
    };
    s.filestat = (at, type, size) => {
      bytes().fill(0, at, at + 64);
      view().setUint8(at + 16, type);
      view().setBigUint64(at + 24, 1n, true);
      view().setBigUint64(at + 32, BigInt(size), true);
    };
    return s;
  }

  /** The calls about the process: its arguments, environment, clock, randomness and end. */
  function processCalls(s) {
    return {
      args_sizes_get(count, size) {
        s.view().setUint32(count, s.argv.length, true);
        s.view().setUint32(size, s.argv.reduce((n, a) => n + a.length, 0), true);
        return SUCCESS;
      },
      args_get(pointers, buffer) {
        let at = buffer;
        s.argv.forEach((a, i) => {
          s.view().setUint32(pointers + 4 * i, at, true);
          s.bytes().set(a, at);
          at += a.length;
        });
        return SUCCESS;
      },
      environ_sizes_get(count, size) {
        s.view().setUint32(count, 0, true);
        s.view().setUint32(size, 0, true);
        return SUCCESS;
      },
      environ_get: () => SUCCESS,
      clock_time_get(_id, _precision, time) {
        s.view().setBigUint64(time, BigInt(Date.now()) * 1000000n, true);
        return SUCCESS;
      },
      random_get(at, len) {
        for (let done = 0; done < len; done += 65536) {
          globalThis.crypto.getRandomValues(s.bytes().subarray(at + done, at + Math.min(len, done + 65536)));
        }
        return SUCCESS;
      },
      proc_exit(code) {
        throw new Exit(code);
      },
      sched_yield: () => SUCCESS,
    };
  }

  /** The calls that read and write open descriptors. */
  function streamCalls(s) {
    return {
      fd_write(fd, iovs, count, wrote) {
        const file = s.open.get(fd);
        if (!file || file.kind !== "output") return BADF;
        const total = s.each(iovs, count, (at, len) => {
          s.written.push([file.stream, s.bytes().slice(at, at + len)]);
          return len;
        });
        s.view().setUint32(wrote, total, true);
        return SUCCESS;
      },
      fd_read(fd, iovs, count, read) {
        const file = s.open.get(fd);
        if (!file || !file.data) return BADF;
        const total = s.each(iovs, count, (at, len) => {
          const part = file.data.subarray(file.at, file.at + len);
          s.bytes().set(part, at);
          file.at += part.length;
          return part.length;
        });
        s.view().setUint32(read, total, true);
        return SUCCESS;
      },
      fd_seek(fd, offset, whence, to) {
        const file = s.open.get(fd);
        if (!file || !file.data) return BADF;
        const from = [0, file.at, file.data.length][whence];
        if (from === undefined) return INVAL;
        file.at = Math.max(0, Math.min(file.data.length, from + Number(offset)));
        s.view().setBigUint64(to, BigInt(file.at), true);
        return SUCCESS;
      },
      fd_close: (fd) => (s.open.delete(fd) ? SUCCESS : BADF),
    };
  }

  /** The calls about the current directory and its files. */
  function fileCalls(s) {
    const type = (file) =>
      ({ directory: DIRECTORY, file: REGULAR_FILE })[file.kind] ?? CHARACTER_DEVICE;
    return {
      fd_fdstat_get(fd, at) {
        const file = s.open.get(fd);
        if (!file) return BADF;
        s.bytes().fill(0, at, at + 24);
        s.view().setUint8(at, type(file));
        s.view().setBigUint64(at + 8, 0xffffffffffffffffn, true);
        s.view().setBigUint64(at + 16, 0xffffffffffffffffn, true);
        return SUCCESS;
      },
      fd_filestat_get(fd, at) {
        const file = s.open.get(fd);
        if (!file) return BADF;
        s.filestat(at, type(file), file.kind === "file" ? file.data.length : 0);
        return SUCCESS;
      },
      fd_prestat_get(fd, at) {
        if (fd !== CWD) return BADF;
        s.view().setUint8(at, 0);
        s.view().setUint32(at + 4, 1, true);
        return SUCCESS;
      },
      fd_prestat_dir_name(fd, at, len) {
        if (fd !== CWD || len < 1) return BADF;
        s.bytes()[at] = ".".charCodeAt(0);
        return SUCCESS;
      },
      path_filestat_get(fd, _flags, path, len, at) {
        if (fd !== CWD) return BADF;
        const name = local(s.string(path, len));
        if (name === "") s.filestat(at, DIRECTORY, 0);
        else if (s.files.has(name)) s.filestat(at, REGULAR_FILE, s.files.get(name).length);
        else return NOENT;
        return SUCCESS;
      },
      path_open(fd, _dirflags, path, len, oflags, _base, _inheriting, _fdflags, opened) {
        if (fd !== CWD) return BADF;
        const name = local(s.string(path, len));
        let file;
        if (name === "") file = { kind: "directory" };
        else if (s.files.has(name) && !(oflags & O_DIRECTORY)) {
          file = { kind: "file", at: 0, data: s.files.get(name) };
        } else return NOENT;
        s.open.set(s.next, file);
        s.view().setUint32(opened, s.next, true);
        s.next += 1;
        return SUCCESS;
      },
    };
  }

  /** The imports of `module`: WASI's functions of `given`, and a trap for any other. */
  function imports(module, given) {
    const out = {};
    for (const { module: from, name, kind } of WebAssembly.Module.imports(module)) {
      if (kind !== "function") continue;
      out[from] ??= {};
      if (from === "wasi_snapshot_preview1") {
        out[from][name] = given[name] ?? (() => NOSYS);
      } else {
        out[from][name] = () => {
          throw new WebAssembly.RuntimeError(`the module called ${from}.${name}, which no host gives`);
        };
      }
    }
    return out;
  }

  /** The text of the pieces of `stream` among `written`. */
  function text(written, stream) {
    const pieces = written.filter(([s]) => s === stream).map(([, b]) => b);
    const all = new Uint8Array(pieces.reduce((n, b) => n + b.length, 0));
    let at = 0;
    for (const b of pieces) {
      all.set(b, at);
      at += b.length;
    }
    return new TextDecoder().decode(all);
  }

  /**
   * Runs the command `module`, a compiled `WebAssembly.Module`, with `args` after its name and
   * `files`, an object from names to texts, in its current directory, and gives its exit status
   * and what it wrote. A trap, as Rust's panics end in WebAssembly, ends it with 134, as the
   * runtime of compiled programs ends one (wasm.limits).
   */
  async function run(module, args, files) {
    const encoder = new TextEncoder();
    const named = new Map(Object.entries(files).map(([n, t]) => [n, encoder.encode(t)]));
    const written = [];
    let instance;
    const s = state(() => instance.exports.memory, ["stilt-playground", ...args], named, written);
    const given = { ...processCalls(s), ...streamCalls(s), ...fileCalls(s) };
    instance = await WebAssembly.instantiate(module, imports(module, given));
    let status = 0;
    try {
      instance.exports._start();
    } catch (e) {
      if (e instanceof Exit) status = e.code;
      else if (e instanceof WebAssembly.RuntimeError) status = 134;
      else throw e;
    }
    return { status, stdout: text(written, "stdout"), stderr: text(written, "stderr") };
  }

  if (typeof module === "object" && module.exports) module.exports = { run };
  else globalThis.StiltWasi = { run };
}
