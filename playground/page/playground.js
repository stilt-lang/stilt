// The playground's page: an editor whose text the compiler checks as one types, with each
// diagnostic under the code it is about and listed under the editor as `stilt check` renders
// it, the facts that the compiler infers at the end of the lines they are about, as the language
// server's inlay hints write them, beside the editor what `stilt show` prints of the function at
// the cursor, a Run button for the reference interpreter, and a link that holds the program in
// its fragment, `#code=` and the program's UTF-8 in base64url.

"use strict";

{
  const $ = (id) => document.getElementById(id);
  const source = $("source");
  const layer = $("layer");
  const base = document.currentScript.src.replace(/[^/]*$/, "");
  const highlighter = new globalThis.StiltHighlight.Highlighter(globalThis.stiltGrammar);
  const SCRIPTS = { check: ["wasi.js", "compiler.js"], run: ["interpreter.js"] };

  /** Asks `engine.js` on the page, after loading the scripts of `role`. */
  function onPage(role) {
    let loaded = null;
    const script = (name) =>
      new Promise((done, failed) => {
        const s = document.createElement("script");
        s.src = base + name;
        s.onload = done;
        s.onerror = () => failed(new Error(`${name} didn't load`));
        document.body.append(s);
      });
    const load = async () => {
      for (const name of [...SCRIPTS[role], "engine.js"]) await script(name);
    };
    return {
      ask: async (request) => {
        await (loaded ??= load());
        return globalThis.StiltEngine.handle(request);
      },
      stop: null,
    };
  }

  /** Asks a worker of `role`, which `stop` ends; or the page, if no worker starts. */
  function inWorker(role) {
    let worker = null;
    let ready = false;
    let fallback = null;
    let next = 0;
    const pending = new Map();
    const settle = (each) => {
      for (const [, asked] of pending) each(asked);
      pending.clear();
    };
    const start = () => {
      worker = new Worker(`${base}worker.js#${role}`);
      worker.onmessage = ({ data }) => {
        if (data.ready) ready = true;
        const asked = pending.get(data.id);
        if (!asked) return;
        pending.delete(data.id);
        if ("error" in data) asked.failed(new Error(data.error));
        else asked.done(data.result);
      };
      worker.onerror = (e) => {
        e.preventDefault();
        if (ready) {
          settle((asked) => asked.failed(new Error(e.message)));
          return;
        }
        fallback = onPage(role);
        settle((asked) => fallback.ask(asked.request).then(asked.done, asked.failed));
        worker = null;
      };
    };
    return {
      ask: (request) => {
        if (fallback) return fallback.ask(request);
        if (!worker) start();
        const id = next++;
        return new Promise((done, failed) => {
          pending.set(id, { request, done, failed });
          worker.postMessage({ id, request });
        });
      },
      stop: () => {
        if (!worker) return;
        worker.terminate();
        worker = null;
        ready = false;
        settle((asked) => asked.failed(new Error("Stopped.")));
      },
    };
  }

  const fromFile = location.protocol === "file:";
  const checker = fromFile ? onPage("check") : inWorker("check");
  const runner = fromFile ? onPage("run") : inWorker("run");

  /** `text` escaped for HTML. */
  const escape = (text) =>
    text.replaceAll("&", "&amp;").replaceAll("<", "&lt;").replaceAll(">", "&gt;");

  /** The index in `line`'s UTF-16 of column `col`, which counts characters from 1. */
  function unit(line, col) {
    let at = 0;
    for (let c = 1; c < col && at < line.length; c++) at += line.codePointAt(at) > 0xffff ? 2 : 1;
    return at;
  }

  /** The spans that the diagnostics mark, by line, each `[from, to, severity]`. */
  function marks(lines, found) {
    const out = new Map();
    const add = (line, from, to, severity) => {
      if (!out.has(line)) out.set(line, []);
      out.get(line).push([from, Math.max(to, from + 1), severity]);
    };
    for (const d of found?.diagnostics ?? []) {
      const severity = d.code.startsWith("W") ? "warning" : "error";
      for (const label of d.labels.filter((l) => l.primary)) {
        const [[l1, c1], [l2, c2]] = label.range;
        for (let l = l1; l <= l2; l++) {
          const text = lines[l - 1] ?? "";
          const from = l === l1 ? unit(text, c1) : 0;
          add(l, from, l === l2 ? unit(text, c2) : text.length, severity);
        }
      }
    }
    return out;
  }

  /** The hints at the end of each line, by line, each `[class, text, title]`. */
  function hints(found) {
    const out = new Map();
    const add = (line, hint) => {
      if (!out.has(line)) out.set(line, []);
      out.get(line).push(hint);
    };
    for (const f of found?.functions ?? []) {
      if (f.broken) continue;
      for (const [line, pattern, type] of f.types) add(line, ["type", `${pattern}: ${type}`, ""]);
      if (f.facts.length && f.body) {
        const title = f.facts.map((fact) => `${fact.text}: ${fact.meaning}`).join("\n");
        add(f.body, ["facts", `[${f.facts.map((fact) => fact.text).join(", ")}]`, title]);
      }
      for (const [line, says] of f.notes) add(line, ["note", `// ${says}`, ""]);
    }
    return out;
  }

  /** A line's HTML: its pieces with their classes, the marks over them, then its hints. */
  function line(pieces, marked, hinted) {
    let html = "";
    let at = 0;
    for (const [text, cls] of pieces) {
      for (let i = 0; i < text.length; ) {
        const severity = (marked ?? []).find(([from, to]) => at + i >= from && at + i < to)?.[2];
        let j = i + 1;
        const same = (k) =>
          (marked ?? []).find(([from, to]) => at + k >= from && at + k < to)?.[2] === severity;
        while (j < text.length && same(j)) j++;
        const classes = [cls && `t-${cls}`, severity && `m-${severity}`].filter(Boolean).join(" ");
        const part = escape(text.slice(i, j));
        html += classes ? `<span class="${classes}">${part}</span>` : part;
        i = j;
      }
      at += text.length;
    }
    const end = Math.max(...(marked ?? []).map(([, to]) => to), at);
    if (end > at) html += `<span class="m-${marked.at(-1)[2]}">${" ".repeat(end - at)}</span>`;
    for (const [cls, text, title] of hinted ?? []) {
      const titled = title ? ` title="${escape(title).replaceAll('"', "&quot;")}"` : "";
      html += `<span class="hint h-${cls}"${titled}>${escape(text)}</span>`;
    }
    return html;
  }

  let found = null;

  /** Draws the editor's layer from the text, with the last diagnostics and facts. */
  function draw() {
    const text = source.value;
    const lines = text.split("\n");
    const marked = marks(lines, found);
    const hinted = hints(found);
    const html = highlighter
      .lines(text)
      .map((pieces, i) => line(pieces, marked.get(i + 1), hinted.get(i + 1)));
    layer.innerHTML = `${html.join("\n")}\n `;
  }

  /** Writes `text` into the element `id`. */
  function write(id, text) {
    $(id).textContent = text;
  }

  let checked = 0;
  let checking = null;

  /** Checks the text, unless a check runs, then draws what it found. */
  async function check() {
    const asked = ++checked;
    if (checking) return;
    const text = source.value;
    try {
      checking = checker.ask({ kind: "live", text });
      found = await checking;
    } catch (e) {
      found = { failed: String(e.message ?? e) };
    }
    checking = null;
    if (asked !== checked) return check();
    draw();
    write("diagnostics", found.failed ?? (found.rendered.join("\n") || "No errors or warnings."));
    $("diagnostics").classList.toggle("quiet", !found.failed && !found.rendered.length);
    shown = null;
    show();
  }

  let shown = null;

  /** The function whose declaration holds the cursor's line, if one does. */
  function functionAtCursor() {
    const line = source.value.slice(0, source.selectionStart).split("\n").length;
    return (found?.functions ?? []).find((f) => f.first <= line && line <= f.last);
  }

  /** Shows what `stilt show` prints of the function at the cursor, or of module `main`. */
  async function show() {
    if (!found || found.failed) return;
    const f = functionAtCursor();
    const address = f ? f.address : "main";
    if (shown === address) return;
    shown = address;
    const done = await checker.ask({ kind: "show", address, text: source.value });
    if (shown !== address) return;
    write("shown-command", `stilt show ${address}`);
    write("shown", done.stdout + done.stderr);
    const facts = f && !f.broken ? f.facts : [];
    $("meanings").innerHTML = facts
      .map((fact) => {
        const lines = fact.causes.map(([l]) => l).join(", ");
        const meaning = escape(fact.meaning).replace(/`([^`]*)`/g, "<code>$1</code>");
        const at = lines ? ` <span class="lines">line ${lines}</span>` : "";
        return `<dt><span class="fact">${escape(fact.text)}</span>${at}</dt><dd>${meaning}</dd>`;
      })
      .join("");
  }

  /** Runs the program, and writes what it wrote and its exit status. */
  async function run() {
    const out = $("output");
    out.textContent = "Running…";
    $("run").disabled = true;
    $("stop").hidden = !runner.stop;
    try {
      const done = await runner.ask({ kind: "run", text: source.value });
      out.innerHTML = done.output
        .map(([stream, text]) => `<span class="${stream}">${escape(text)}</span>`)
        .join("");
      out.insertAdjacentHTML("beforeend", `<span class="status">exit status ${done.status}</span>`);
    } catch (e) {
      out.textContent = String(e.message ?? e);
    }
    $("run").disabled = false;
    $("stop").hidden = true;
  }

  /** The program of a link's fragment, if it holds one. */
  function fromLink() {
    const given = new URLSearchParams(location.hash.slice(1)).get("code");
    if (!given) return null;
    try {
      const b64 = given.replaceAll("-", "+").replaceAll("_", "/");
      const bytes = Uint8Array.from(atob(b64), (c) => c.charCodeAt(0));
      return new TextDecoder().decode(bytes);
    } catch {
      return null;
    }
  }

  /** The link to the playground with the program in its fragment. */
  function link() {
    let binary = "";
    for (const b of new TextEncoder().encode(source.value)) binary += String.fromCharCode(b);
    const code = btoa(binary).replaceAll("+", "-").replaceAll("/", "_").replace(/=+$/, "");
    return `${location.href.split("#")[0]}#code=${code}`;
  }

  async function share() {
    history.replaceState(null, "", link());
    try {
      await navigator.clipboard.writeText(location.href);
      write("shared", "The link is copied.");
    } catch {
      write("shared", "The link is in the address bar.");
    }
  }

  let typing = null;
  source.addEventListener("input", () => {
    draw();
    clearTimeout(typing);
    typing = setTimeout(() => {
      check();
      history.replaceState(null, "", link());
    }, 150);
  });
  source.addEventListener("keydown", (e) => {
    if (e.key === "Tab" && !e.shiftKey) {
      e.preventDefault();
      if (!document.execCommand("insertText", false, "  ")) {
        source.setRangeText("  ", source.selectionStart, source.selectionEnd, "end");
      }
      draw();
    } else if (e.key === "Enter" && (e.metaKey || e.ctrlKey)) {
      e.preventDefault();
      run();
    }
  });
  for (const event of ["click", "keyup"]) source.addEventListener(event, () => show());
  $("run").addEventListener("click", run);
  $("stop").addEventListener("click", () => runner.stop?.());
  $("share").addEventListener("click", share);
  window.addEventListener("hashchange", () => {
    const given = fromLink();
    if (given !== null && given !== source.value) {
      source.value = given;
      draw();
      check();
    }
  });

  source.value = fromLink() ?? source.value;
  draw();
  check();
}
