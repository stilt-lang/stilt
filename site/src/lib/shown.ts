// The front page's example as `stilt show` prints it, with each piece that `show` adds to the
// source marked: the module's header with its tier, the facts after a signature, the types of
// bindings and the comments that name the operation behind each fact. The marks come from
// comparing the source with what `show` prints, word by word, so they are what the compiler
// adds, never a copy of it.

import type { Shown } from "./stilt";
import { escape, span, tokens } from "./highlight";

/** The words of `text`: runs of letters and digits, runs of blanks, ends of lines and marks. */
function words(text: string): string[] {
  return text.match(/\w+|[ \t]+|\n|[^\w\s]/g) ?? [];
}

/** For each word of `shown`, whether `show` added it to `source`, from their longest common
 * subsequence, matched from the end, so that each addition comes out in one piece. */
function added(source: string[], shown: string[]): boolean[] {
  const [n, m] = [source.length, shown.length];
  const best = Array.from({ length: n + 1 }, () => new Int32Array(m + 1));
  for (let i = 1; i <= n; i++) {
    for (let j = 1; j <= m; j++) {
      best[i][j] =
        source[i - 1] === shown[j - 1] ? best[i - 1][j - 1] + 1 : Math.max(best[i - 1][j], best[i][j - 1]);
    }
  }
  const out: boolean[] = new Array(m).fill(true);
  let [i, j] = [n, m];
  while (i > 0 && j > 0) {
    if (source[i - 1] === shown[j - 1]) {
      out[j - 1] = false;
      i--;
      j--;
    } else if (best[i - 1][j] >= best[i][j - 1]) i--;
    else j--;
  }
  return out;
}

/** The ranges of characters of `shown` that `show` added to `source`, each `[from, to)`, none
 * across the end of a line. */
function ranges(source: string, shown: string): [number, number][] {
  const each = words(shown);
  const marks = added(words(source), each);
  const out: [number, number][] = [];
  let at = 0;
  each.forEach((word, k) => {
    const end = at + word.length;
    const last = out.at(-1);
    if (marks[k] && word !== "\n") {
      if (last && last[1] === at) last[1] = end;
      else out.push([at, end]);
    }
    at = end;
  });
  return out;
}

/** The class of an addition: a function's facts, a comment, or a type. */
function kind(text: string): string {
  if (/^\s*\[[\w, ]+\]/.test(text)) return "added facts";
  if (/^\s*\/\//.test(text)) return "added comment";
  return "added";
}

/** A line of code, highlighted, with the characters of `marks`, offsets in the line, wrapped. */
function line(code: string, marks: [number, number][]): string {
  const parts: string[] = [];
  let at = 0;
  for (const token of tokens(code, "stilt")[0] ?? []) {
    const end = at + token.content.length;
    const cuts = [...marks.flat().filter((c) => c > at && c < end), end];
    let start = at;
    for (const cut of cuts) {
      const text = code.slice(start, cut);
      const mark = marks.find(([a, b]) => start >= a && cut <= b);
      if (!mark) parts.push(span(token, text));
      else {
        const label = kind(code.slice(mark[0], mark[1]));
        parts.push(`<span class="${label}">${escape(text)}</span>`);
      }
      start = cut;
    }
    at = end;
  }
  return `<span class="line">${parts.join("")}</span>`;
}

/** The HTML of the example as `show` prints it: the module's header, then each function. */
export function annotated(source: string, functions: Shown[]): string {
  const blocks = source.trim().split(/\n\n+/);
  const out: string[] = [];
  functions.forEach(({ shown }, k) => {
    const [header, ...body] = shown.replace(/\n$/, "").split("\n");
    if (k === 0) {
      const head = tokens(header, "stilt")[0].map((t) => span(t)).join("");
      out.push(`<span class="line">${head}</span>`);
    } else out.push(`<span class="line"></span>`);
    const text = body.join("\n");
    const marks = ranges(blocks[k] ?? "", text);
    let at = 0;
    for (const code of body) {
      const inLine = marks
        .map(([a, b]): [number, number] => [Math.max(a, at) - at, Math.min(b, at + code.length) - at])
        .filter(([a, b]) => a < b);
      out.push(line(code, inLine));
      at += code.length + 1;
    }
  });
  return out.join("\n");
}
