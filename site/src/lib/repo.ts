// The repository the site is built from, and the tools it runs while it is built. The site's
// commands run from `site/`, so the repository is its parent unless `STILT_ROOT` names it.

import fs from "node:fs";
import path from "node:path";

/** The repository's root. */
export const ROOT = path.resolve(process.env.STILT_ROOT ?? path.join(process.cwd(), ".."));

/** The compiler, whose `check`, `show` and `doc --std` the pages print. */
export const STILT = path.resolve(ROOT, process.env.STILT ?? "target/bin/stilt");

/** The directory that holds the playground's compiler and interpreter (`just playground`). */
export const PLAYGROUND = path.resolve(ROOT, process.env.STILT_PLAYGROUND ?? "target/playground");

/** The text of the repository's file `file`. */
export function read(file: string): string {
  return fs.readFileSync(path.join(ROOT, file), "utf8");
}

/** Whether the repository holds `file`, and what it is. */
export function kind(file: string): "file" | "directory" | null {
  try {
    const stat = fs.statSync(path.join(ROOT, file));
    return stat.isDirectory() ? "directory" : stat.isFile() ? "file" : null;
  } catch {
    return null;
  }
}

/** The names of the entries of the repository's directory `dir`, hidden ones left out, sorted. */
export function entries(dir: string): { name: string; dir: boolean }[] {
  return fs
    .readdirSync(path.join(ROOT, dir), { withFileTypes: true })
    .filter((e) => !e.name.startsWith("."))
    .map((e) => ({ name: e.name, dir: e.isDirectory() }))
    .sort((a, b) => a.name.localeCompare(b.name));
}

/** The stems of the Markdown documents of the repository's directory `dir`, sorted. */
export function documents(dir: string): string[] {
  return entries(dir)
    .filter((e) => !e.dir && e.name.endsWith(".md"))
    .map((e) => e.name.slice(0, -3));
}

/** `p` without `.`, `..` and empty parts, or `null` if it leaves the repository. */
export function normalize(p: string): string | null {
  const parts: string[] = [];
  for (const part of p.split("/")) {
    if (part === "" || part === ".") continue;
    if (part === "..") {
      if (parts.length === 0) return null;
      parts.pop();
    } else parts.push(part);
  }
  return parts.join("/");
}

/** The directory of the repository's path `from`, with its `/`, or nothing for the root. */
export function parent(from: string): string {
  const at = from.lastIndexOf("/");
  return at < 0 ? "" : from.slice(0, at + 1);
}
