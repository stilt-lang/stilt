// The pages of the repository's files and directories that a page links to and that are no page
// themselves, such as the conformance tests that the Reference's paragraphs list: a file's text,
// or a directory's files, each linked to its own page. A directory lists its files with those of
// its subdirectories when it holds few enough, and its own files only when it holds more.

import { file, library } from "./stilt";
import { docs, place } from "./map";
import { links } from "./markdown";
import { modelFiles } from "./proofmap";
import { entries, kind, normalize, parent, read } from "./repo";

/** A directory of at most this many files lists all of them, those below it included. */
const LISTED = 200;

/** An entry of a directory's page: its path below the directory, and its page, if it has one. */
export interface Listed {
  name: string;
  href: string | null;
}

/** The files under the repository's directory `dir`, as paths below it, or with `deep` off, its
 * own files and each subdirectory as its name and `/`. */
function walk(dir: string, deep: boolean, below = ""): string[] {
  const out: string[] = [];
  for (const entry of entries(dir + below)) {
    const name = below + entry.name;
    if (!entry.dir) out.push(name);
    else if (deep) out.push(...walk(dir, true, `${name}/`));
    else out.push(`${name}/`);
  }
  return out;
}

/** The entries of the page of the repository's directory `dir`. */
export function listing(dir: string): Listed[] {
  let files = walk(`${dir}/`, true);
  if (files.length > LISTED) files = walk(`${dir}/`, false);
  return files.map((name) => ({
    name,
    href: name.endsWith("/") ? null : place(`${dir}/${name}`),
  }));
}

/** The repository's files and directories that a link of `text`, written in `from`, names. */
function named(from: string, text: string): string[] {
  const out: string[] = [];
  for (const href of links(text)) {
    if (/^([a-z]+:|#|\/)/i.test(href)) continue;
    const repo = normalize(parent(from) + decodeURI(href.split("#")[0]));
    if (repo !== null && kind(repo) !== null) out.push(repo);
  }
  return out;
}

let found: string[] | null = null;

/** Every file and directory whose page the site holds, as its path in the repository, a
 * directory's without its `/`: those its documents and the library link to, and the files that
 * these directories list, and the files of the Lean model's modules, which the proof map links to. */
export function sources(): string[] {
  if (found) return found;
  const queue: string[] = [];
  for (const doc of docs().values()) queue.push(...named(doc.source, read(doc.source)));
  for (const module of library()) {
    const texts = [module.description, ...module.items.flatMap(function docs(i): string[] {
      return [i.doc, ...i.members.flatMap(docs)];
    })];
    for (const text of texts) queue.push(...named(file(module), text));
  }
  queue.push(...modelFiles());
  const done = new Set<string>();
  while (queue.length) {
    const repo = queue.pop()!;
    const at = place(repo);
    if (done.has(repo) || !at?.startsWith("/source/")) continue;
    done.add(repo);
    if (kind(repo) === "directory") queue.push(...listing(repo).filter((e) => e.href).map((e) => `${repo}/${e.name}`));
  }
  found = [...done].sort();
  return found;
}
