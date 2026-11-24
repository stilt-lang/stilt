// A fenced block as the site renders it: highlighted, with a caption that says what the block
// is, a button that copies it and, for a program, a link that opens it in the playground. The
// words of an example's info string (tools/runner/src/examples.rs) show on it: a diagnostic it
// expects marks its line and links to the error's page, a test's expected result marks the
// test's line, and an expected exit status shows in the caption. What a program or a command
// prints is set apart from it, and is never what Copy copies.

import { escape, span, tokens } from "./highlight";

/** What the words after `stilt` in an info string expect of the program. */
interface Expected {
  fragment: boolean;
  /** The marks of lines, by line: a diagnostic's code, or a test's `pass` or `fail`. */
  marks: Map<number, string[]>;
  exit: string | null;
}

/** What the words of an example's info string expect. */
function expected(words: string[]): Expected {
  const out: Expected = { fragment: words.includes("fragment"), marks: new Map(), exit: null };
  for (const word of words) {
    const exit = /^exit:(\d+)$/.exec(word);
    if (exit) out.exit = exit[1];
    const mark = /^([EW]\d{4}|pass|fail):(\d+)$/.exec(word);
    if (!mark) continue;
    const line = Number(mark[2]);
    out.marks.set(line, [...(out.marks.get(line) ?? []), mark[1]]);
  }
  return out;
}

/** `bytes` in base64url without padding (RFC 4648), as a URL holds it. */
export function base64url(text: string): string {
  return Buffer.from(text, "utf8").toString("base64url");
}

/** The playground's page, opened on the program `code`. */
export function playground(code: string): string {
  return `/playground/#code=${base64url(code)}`;
}

/** The HTML of one mark at the end of a line. */
function mark(word: string): string {
  if (word === "pass" || word === "fail") return `<span class="mark mark-${word}">${word}</span>`;
  const href = `/errors/${word}/`;
  return `<a class="mark mark-${word[0] === "W" ? "warning" : "error"}" href="${href}">${word}</a>`;
}

/** The highlighted lines of `code`, each line with the marks that `marks` gives it. */
function body(code: string, lang: string, marks: Map<number, string[]>): string {
  return tokens(code, lang)
    .map((line, i) => {
      const words = marks.get(i + 1) ?? [];
      const kind = words.find((w) => /^[EW]/.test(w)) ? "marked" : words.length ? "tested" : "";
      const text = line.map((t) => span(t)).join("");
      return `<span class="line${kind ? ` ${kind}` : ""}">${text}${words.map(mark).join("")}</span>`;
    })
    .join("\n");
}

/** A terminal session: each `$ ` line a command, highlighted as a shell's, whose prompt the
 * stylesheet draws so that copying takes the command alone, and each other line what the
 * commands print, set apart, which Copy leaves out. */
function session(code: string): string {
  return code
    .split("\n")
    .map((text) => {
      if (!text.startsWith("$ ")) return `<span class="line out">${escape(text)}</span>`;
      const command = (tokens(text.slice(2), "sh")[0] ?? []).map((t) => span(t)).join("");
      return `<span class="line cmd">${command}</span>`;
    })
    .join("\n");
}

/** The caption's buttons: copy, and, for a program, open in the playground. */
function actions(code: string, runnable: boolean): string {
  const copy = `<button type="button" class="code-action" data-copy>Copy</button>`;
  const run = runnable
    ? `<a class="code-action code-run" href="${playground(code)}">Run in the playground</a>`
    : "";
  return `<span class="code-actions">${copy}${run}</span>`;
}

/** The HTML of the fenced block `code` whose info string is `lang` and `meta`. */
export function block(code: string, lang: string | null, meta: string | null, opens: boolean): string {
  const words = (meta ?? "").split(/\s+/).filter(Boolean);
  const name = lang ?? "text";
  if (name === "output" || name === "stderr") {
    const label = name === "output" ? "Output" : "Standard error";
    return (
      `<figure class="code code-${name}"><figcaption><span class="code-label">${label}</span>` +
      `</figcaption><pre><code>${escape(code.replace(/\n$/, ""))}</code></pre></figure>`
    );
  }
  const example = name === "stilt" ? expected(words) : null;
  const program = example !== null && !example.fragment;
  const label = program
    ? `main.lt${example.exit ? `, exits with ${example.exit}` : ""}`
    : "";
  const text = code.replace(/\n$/, "");
  if (name === "console" || name === "shellsession") {
    return (
      `<figure class="code code-session"><figcaption><span class="code-label">terminal</span>` +
      `${actions(code, false)}</figcaption><pre><code>${session(text)}</code></pre></figure>`
    );
  }
  return (
    `<figure class="code" data-lang="${escape(name)}"><figcaption>` +
    `<span class="code-label">${escape(label)}</span>${actions(code, program && opens)}` +
    `</figcaption><pre><code>${body(text, name, example?.marks ?? new Map())}</code></pre></figure>`
  );
}
