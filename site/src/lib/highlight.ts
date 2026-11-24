// Highlighting, as the site renders code: Shiki, with Stilt's TextMate grammar from the editors'
// extension, the one the playground reads, and a theme whose colours are the stylesheet's
// variables, so a block follows the reader's light or dark theme and the playground's colours.

import { type BundledLanguage, createHighlighter, type ThemedToken, type ThemeRegistration } from "shiki";
import { read } from "./repo";

/** The grammar the editors and the playground highlight Stilt with. */
export const GRAMMAR = "editors/vscode/syntaxes/stilt.tmLanguage.json";

/** The languages of the repository's other blocks and files. */
const OTHERS = [
  "rust", "go", "python", "typescript", "javascript", "json", "toml", "c", "sh", "ocaml",
  "yaml", "diff", "lean4",
] as const;

/** Each scope and the stylesheet's variable for its colour. */
const SCOPES: [string[], string, string?][] = [
  [["comment", "punctuation.definition.comment"], "--t-comment", "italic"],
  [["keyword.control"], "--t-control"],
  [["keyword", "storage", "keyword.other"], "--t-keyword"],
  [["keyword.operator", "punctuation.accessor"], "--t-operator"],
  [["entity.name.type", "support.type", "entity.name.class", "storage.type"], "--t-type"],
  [["entity.name.function", "support.function", "meta.function-call"], "--t-function"],
  [["string", "punctuation.definition.string", "constant.character.escape"], "--t-string"],
  [["constant.numeric", "constant.language", "constant.other"], "--t-number"],
  [["entity.name.namespace", "entity.name.module"], "--t-module"],
  [["invalid"], "--t-invalid"],
];

const THEME: ThemeRegistration = {
  name: "stilt",
  type: "light",
  colors: { "editor.foreground": "var(--t-text)", "editor.background": "transparent" },
  settings: [
    { settings: { foreground: "var(--t-text)", background: "transparent" } },
    ...SCOPES.map(([scope, variable, fontStyle]) => ({
      scope,
      settings: { foreground: `var(${variable})`, ...(fontStyle ? { fontStyle } : {}) },
    })),
  ],
};

const stilt = { ...JSON.parse(read(GRAMMAR)), name: "stilt", aliases: ["lt"] };

const highlighter = await createHighlighter({ themes: [THEME], langs: [stilt, ...OTHERS] });

/** The language Shiki knows `lang` as, or `null` for plain text. */
function known(lang: string): string | null {
  const name = lang === "console" || lang === "shell" ? "sh" : lang;
  return highlighter.getLoadedLanguages().includes(name) ? name : null;
}

/** `text` escaped for HTML. */
export function escape(text: string): string {
  return text.replaceAll("&", "&amp;").replaceAll("<", "&lt;").replaceAll(">", "&gt;");
}

/** The tokens of each line of `code` in `lang`, each as its text and its HTML style. */
export function tokens(code: string, lang: string): ThemedToken[][] {
  const name = known(lang);
  if (!name) return code.split("\n").map((content) => [{ content, offset: 0 }]);
  return highlighter.codeToTokensBase(code, { lang: name as BundledLanguage, theme: THEME });
}

/** The HTML of one token: its text in a span of its colour. */
export function span(token: ThemedToken, text = token.content, extra = ""): string {
  const style = [
    token.color ? `color:${token.color}` : "",
    token.fontStyle === 1 ? "font-style:italic" : "",
  ].filter(Boolean);
  const attrs = (style.length ? ` style="${style.join(";")}"` : "") + extra;
  return attrs ? `<span${attrs}>${escape(text)}</span>` : escape(text);
}

/** The highlighted lines of `code` in `lang`, each line a `span.line`, without the `pre`. */
export function lines(code: string, lang: string): string {
  const body = code.endsWith("\n") ? code.slice(0, -1) : code;
  return tokens(body, lang)
    .map((line) => `<span class="line">${line.map((t) => span(t)).join("")}</span>`)
    .join("\n");
}

/** Whether a file named `name` is highlighted, and in what language. */
export function language(name: string): string {
  const ext = name.slice(name.lastIndexOf(".") + 1);
  const byExt: Record<string, string> = {
    lt: "stilt", rs: "rust", ml: "ocaml", mli: "ocaml", py: "python", ts: "typescript",
    js: "javascript", mjs: "javascript", json: "json", toml: "toml", c: "c", h: "c", sh: "sh",
    yml: "yaml", yaml: "yaml", lean: "lean4", diff: "diff", go: "go",
  };
  return byExt[ext] ?? "text";
}
