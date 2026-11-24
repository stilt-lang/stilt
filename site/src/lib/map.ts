// The site's map: which documents of the repository are pages, where each one is on the site,
// the order and the groups their parts list them in, and what a link written in the repository
// leads to on the site.

import { documents, kind, normalize, parent, read } from "./repo";

/** The part of the site that a page belongs to, which the header marks. */
export type Section =
  | "home"
  | "learn"
  | "reference"
  | "errors"
  | "library"
  | "design"
  | "playground"
  | "source";

/** A document of the repository that is a page of the site. */
export interface Doc {
  /** Its path in the repository, as `docs/guide/02-values.md`. */
  source: string;
  /** Its path on the site, as `/learn/values/`. */
  url: string;
  section: Section;
  title: string;
}

/** The directories whose documents are pages, each with where its pages go and their part. */
const DIRECTORIES: [string, string, Section][] = [
  ["docs/guide", "/learn/", "learn"],
  ["reference", "/reference/", "reference"],
  ["reference/rationale", "/reference/rationale/", "reference"],
  ["docs/errors", "/errors/", "errors"],
  ["docs/design", "/design/", "design"],
];

/** The documents outside those directories that are pages. */
const SINGLES: Doc[] = [
  { source: "README.md", url: "/", section: "home", title: "Stilt" },
  { source: "docs/commands.md", url: "/learn/commands/", section: "learn", title: "" },
];

/** The text of a document's first heading of level 1, without its Markdown. */
export function title(text: string): string | null {
  const line = text.split("\n").find((l) => l.startsWith("# "));
  return line ? line.slice(2).replaceAll("`", "").trim() : null;
}

/** The page of the document `stem` of a directory whose pages go under `base`. */
function url(base: string, stem: string): string {
  return stem === "README" ? base : `${base}${stem.replace(/^\d+-/, "")}/`;
}

let all: Map<string, Doc> | null = null;

/** Every document that is a page, by its path in the repository. */
export function docs(): Map<string, Doc> {
  if (all) return all;
  all = new Map();
  for (const single of SINGLES) {
    const text = read(single.source);
    all.set(single.source, { ...single, title: single.title || (title(text) ?? single.source) });
  }
  for (const [dir, base, section] of DIRECTORIES) {
    for (const stem of documents(dir)) {
      const source = `${dir}/${stem}.md`;
      const name = title(read(source)) ?? source;
      all.set(source, { source, url: url(base, stem), section, title: name });
    }
  }
  return all;
}

/** The documents of `section`, but the front page, in the order of their paths. */
export function inSection(section: Section): Doc[] {
  return [...docs().values()].filter((d) => d.section === section && d.url !== "/");
}

/** A row of a table of contents: the document it links and what the table says of it. */
export interface Entry {
  doc: Doc;
  /** The text of the row's link, the document's name in the index. */
  label: string;
  blurb: string;
}

/** A group of a part's contents: a heading of an index and the documents its table links. */
export interface Group {
  heading: string;
  entries: Entry[];
}

/**
 * The groups of the index `readme`: each section of it, of level 2 or 3, whose table links
 * documents, with each row's document and the text of the cell after the link, in the order the
 * index lists them. A row may start with a number, as the Reference's chapters do.
 */
export function groups(readme: string): Group[] {
  const out: Group[] = [];
  const dir = parent(readme);
  let heading = "";
  for (const line of read(readme).split("\n")) {
    const title = /^#{2,3} (.+)$/.exec(line);
    if (title) heading = title[1].trim();
    const row = /^\|(?:\s*\d+\s*\|)?\s*\[([^\]]+)\]\(([^)#]+)[^)]*\)\s*\|(.*)$/.exec(line);
    if (!row) continue;
    const doc = docs().get(normalize(dir + row[2]) ?? "");
    if (!doc) continue;
    const cells = row[3].split(/(?<!\\)\|/).map((c) => c.trim()).filter(Boolean);
    let group = out.at(-1);
    if (!group || group.heading !== heading) out.push((group = { heading, entries: [] }));
    group.entries.push({ doc, label: row[1].replaceAll("`", ""), blurb: cells.at(-1) ?? "" });
  }
  return out;
}

/** The pages of `section` in reading order: its index, then its groups', then any other. */
export function ordered(section: Section): Doc[] {
  const index = inSection(section).find((d) => d.source.endsWith("/README.md"));
  const listed = index ? groups(index.source).flatMap((g) => g.entries.map((e) => e.doc)) : [];
  const out: Doc[] = [];
  for (const doc of [...(index ? [index] : []), ...listed, ...inSection(section)]) {
    if (!out.includes(doc)) out.push(doc);
  }
  return out;
}

/** What a link resolves to: where it leads on the site, or that it leads nowhere. */
export interface Resolved {
  href: string;
  broken: boolean;
}

/**
 * What the link `href`, written in the repository's file `from`, leads to: the page of the
 * document it names, or the page of the source of any other file or directory of the
 * repository, with its fragment. A link to another site or to a fragment of the page is kept.
 */
export function resolve(from: string, href: string): Resolved {
  if (/^([a-z]+:|#|\/)/i.test(href)) return { href, broken: false };
  const at = href.indexOf("#");
  const [file, fragment] = at < 0 ? [href, ""] : [href.slice(0, at), href.slice(at)];
  const repo = normalize(parent(from) + decodeURI(file));
  const target = repo === null ? null : place(repo);
  return target ? { href: target + fragment, broken: false } : { href, broken: true };
}

/** The site's path for the repository's file or directory `repo`, or `null` if there is none. */
export function place(repo: string): string | null {
  const doc = docs().get(repo);
  if (doc) return doc.url;
  const what = kind(repo);
  if (what === "directory") {
    const index = docs().get(repo === "" ? "README.md" : `${repo}/README.md`);
    return index ? index.url : `/source/${repo}/`;
  }
  return what === "file" ? `/source/${repo}/` : null;
}
