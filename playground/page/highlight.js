// The playground's highlighting: the TextMate grammar that the editors' extension uses, which
// tools/grammar generates from the Reference's lexicon, read by a small TextMate tokenizer. It
// reads a text a line at a time, and gives each line as pieces of text, each with the class of
// the most specific scope that has one. It reads what the grammar uses: `match` and
// `begin`/`end` rules, their captures, with patterns of their own, `include`, and `\G`, the
// position where the rule that encloses a match began.

"use strict";

{
  /** The class of a scope, by the scope's prefix, the longest of which a scope starts with. */
  const CLASSES = [
    ["comment", "comment"],
    ["string", "string"],
    ["constant.character.escape", "escape"],
    ["storage.type.format", "escape"],
    ["constant.numeric", "number"],
    ["constant.language", "constant"],
    ["variable.other.constant", "constant"],
    ["variable.other.enummember", "variant"],
    ["variable.language", "keyword"],
    ["keyword.control", "control"],
    ["keyword.operator", "operator"],
    ["keyword", "keyword"],
    ["entity.name.function", "function"],
    ["entity.name.type", "type"],
    ["support.type", "type"],
    ["entity.name.namespace", "module"],
    ["invalid", "invalid"],
  ].sort((a, b) => b[0].length - a[0].length);

  /** The class of the innermost of `scopes` that has one. */
  function classOf(scopes) {
    for (let i = scopes.length - 1; i >= 0; i--) {
      for (const scope of scopes[i].split(" ").reverse()) {
        const found = CLASSES.find(([prefix]) => scope === prefix || scope.startsWith(prefix + "."));
        if (found) return found[1];
      }
    }
    return "";
  }

  /**
   * A grammar's regular expression for JavaScript: as written where `\G` can't match, and, if it
   * holds `\G`, as it reads at the position where `\G` matches.
   */
  function regex(source) {
    const free = new RegExp(source.replaceAll("\\G", "(?!)"), "dg");
    if (!source.includes("\\G")) return { free, anchored: null };
    return { free, anchored: new RegExp(source.replaceAll("\\G", "(?:)"), "dy") };
  }

  /** The first match of `re` in `line` from `pos`, where `\G` matches at `anchor`. */
  function search(re, line, pos, anchor) {
    if (re.anchored && pos === anchor) {
      re.anchored.lastIndex = pos;
      const here = re.anchored.exec(line);
      if (here) return here;
      if (pos >= line.length) return null;
      re.free.lastIndex = pos + 1;
    } else {
      re.free.lastIndex = pos;
    }
    return re.free.exec(line);
  }

  /** The grammar's rules, compiled once each, with their includes resolved. */
  function compile(grammar) {
    const compiled = new Map();
    const rule = (r) => {
      if (compiled.has(r)) return compiled.get(r);
      const c = { name: r.name, contentName: r.contentName, include: r.include };
      compiled.set(r, c);
      if (r.match) c.match = regex(r.match);
      if (r.begin) {
        c.begin = regex(r.begin);
        c.end = regex(r.end);
      }
      c.captures = captures(r.match ? r.captures : r.beginCaptures ?? r.captures);
      c.endCaptures = captures(r.endCaptures ?? r.captures);
      c.patterns = (r.patterns ?? []).map(rule);
      return c;
    };
    const captures = (given) => {
      const out = [];
      for (const [i, c] of Object.entries(given ?? {})) {
        out[Number(i)] = { name: c.name, patterns: (c.patterns ?? []).map(rule) };
      }
      return out;
    };
    const top = rule({ patterns: grammar.patterns });
    const named = (name) =>
      name === "$self" || name === "$base" ? top : rule(grammar.repository[name.slice(1)]);
    // The rules that match, from a list that holds includes and groups of patterns.
    const flat = (patterns, seen = new Set()) =>
      patterns.flatMap((p) => {
        const r = p.include ? named(p.include) : p;
        if (r.match || r.begin) return [r];
        if (seen.has(r)) return [];
        seen.add(r);
        return flat(r.patterns, seen);
      });
    return { top, flat: (r) => (r.flat ??= flat(r.patterns)) };
  }

  // Paints each character from `from` to `to` with the class of `scopes`.
  function paint(classes, from, to, scopes) {
    const cls = classOf(scopes);
    for (let i = from; i < to; i++) classes[i] = cls;
  }

  /** Tokenizes texts by `grammar`, a TextMate grammar's JSON. */
  class Highlighter {
    constructor(grammar) {
      const { top, flat } = compile(grammar);
      this.top = top;
      this.flat = flat;
    }

    /** The lines of `text`, each as its pieces, `[text, class]`. */
    lines(text) {
      let stack = [{ rule: this.top, scopes: [], content: [] }];
      return text.split("\n").map((line) => {
        const classes = new Array(line.length).fill("");
        stack = this.scan(line, classes, stack);
        const pieces = [];
        for (let i = 0; i < line.length; ) {
          let j = i + 1;
          while (j < line.length && classes[j] === classes[i]) j++;
          pieces.push([line.slice(i, j), classes[i]]);
          i = j;
        }
        return pieces;
      });
    }

    // Scans `line` from `pos` with `stack`, painting `classes`; gives the stack at the end.
    scan(line, classes, stack, pos = 0) {
      let anchor = stack.at(-1).anchor ?? -1;
      let stuck = 0;
      while (pos <= line.length) {
        const frame = stack.at(-1);
        const best = this.earliest(frame, line, pos, anchor);
        if (!best) {
          paint(classes, pos, line.length, frame.content);
          break;
        }
        const { m } = best;
        const stop = m.index + m[0].length;
        paint(classes, pos, m.index, frame.content);
        if (this.take(best, line, classes, stack)) anchor = stop;
        // A match of nothing moves on by a character, once it has matched a few times here.
        if (stop === pos && ++stuck > 8) {
          paint(classes, pos, pos + 1, stack.at(-1).content);
          pos += 1;
          stuck = 0;
        } else if (stop > pos) {
          pos = stop;
          stuck = 0;
        }
        if (pos >= line.length && stop === line.length && m[0].length === 0) break;
      }
      for (const f of stack) f.anchor = -1;
      return stack;
    }

    // The earliest match from `pos` of the end of `frame` or of a rule it holds, the end first.
    earliest(frame, line, pos, anchor) {
      let best = null;
      if (frame.end) {
        const m = search(frame.end, line, pos, anchor);
        if (m) best = { m, end: true };
      }
      for (const r of frame.rule.flat ?? this.flat(frame.rule)) {
        const m = search(r.match ?? r.begin, line, pos, anchor);
        if (m && (!best || m.index < best.m.index)) best = { m, rule: r };
      }
      return best;
    }

    // Paints the match `best`, and ends or begins a frame of `stack` for it: gives whether it
    // began one, whose `\G` matches where the match ends.
    take(best, line, classes, stack) {
      const { m, rule } = best;
      const stop = m.index + m[0].length;
      const frame = stack.at(-1);
      if (best.end) {
        paint(classes, m.index, stop, frame.scopes);
        this.capture(line, classes, m, frame.rule.endCaptures, frame.scopes);
        if (stack.length > 1) stack.pop();
        return false;
      }
      const scopes = rule.name ? [...frame.content, rule.name] : frame.content;
      paint(classes, m.index, stop, scopes);
      this.capture(line, classes, m, rule.captures, scopes);
      if (!rule.begin) return false;
      const content = rule.contentName ? [...scopes, rule.contentName] : scopes;
      stack.push({ rule, end: rule.end, scopes, content, anchor: stop });
      return true;
    }

    // Paints the captures of match `m`, by `caps`, within `scopes`.
    capture(line, classes, m, caps, scopes) {
      caps.forEach((c, i) => {
        const at = m.indices[i];
        if (!c || !at || at[0] === at[1]) return;
        const inner = c.name ? [...scopes, c.name] : scopes;
        if (c.name) paint(classes, at[0], at[1], inner);
        if (c.patterns.length) {
          const rule = { flat: this.flat({ patterns: c.patterns }) };
          this.scan(line.slice(0, at[1]), classes, [{ rule, scopes: inner, content: inner }], at[0]);
        }
      });
    }
  }

  if (typeof module === "object" && module.exports) module.exports = { Highlighter };
  else globalThis.StiltHighlight = { Highlighter };
}
