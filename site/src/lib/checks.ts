// The checks of a build, as an Astro integration. Before the pages are written: every link of the
// repository's documents must lead to a file of the repository, and every goal must name what
// checks it (claims.ts). After: every `href` and `src` of every page that leads to another file
// of the site must name a file that the site holds, and its fragment an `id` of that page,
// unless the fragment is a script's state, as the playground's `#code=` is.

import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import type { AstroIntegration } from "astro";
import { unchecked } from "./claims";
import { docs, resolve } from "./map";
import { links } from "./markdown";
import { read } from "./repo";

/** The directories that other tools write after Astro, whose files the pages may link. */
const WRITTEN_AFTER = ["/pagefind/"];

/** An error for each link of the repository's documents that leads nowhere. */
export function repository(): string[] {
  const errors: string[] = [];
  for (const doc of docs().values()) {
    for (const href of links(read(doc.source))) {
      if (resolve(doc.source, href).broken) errors.push(`${doc.source}: the link ${href} leads nowhere`);
    }
  }
  return errors;
}

/** The values of the attribute `name` of the tags of the HTML `text`, its scripts' text left
 * out, unescaped. Text between tags is never read, so code that shows a link links nothing. */
function attributes(text: string, name: string): string[] {
  const tags = text.replace(/<script\b[^>]*>[\s\S]*?<\/script>/g, "").match(/<[a-z][^>]*>/gi) ?? [];
  const pattern = new RegExp(`\\s${name}=(?:"([^"]*)"|'([^']*)'|([^\\s>]+))`, "g");
  return tags.flatMap((tag) =>
    [...tag.matchAll(pattern)].map((m) =>
      (m[1] ?? m[2] ?? m[3]).replaceAll("&quot;", '"').replaceAll("&lt;", "<")
        .replaceAll("&gt;", ">").replaceAll("&amp;", "&"),
    ),
  );
}

/** Every file under `dir`, as its path below it. */
function files(dir: string, below = ""): string[] {
  return fs.readdirSync(path.join(dir, below), { withFileTypes: true }).flatMap((e) =>
    e.isDirectory() ? files(dir, `${below}${e.name}/`) : [`${below}${e.name}`],
  );
}

/** The file of the site that the URL `url`, linked from the page at `at`, names. */
function target(at: string, url: string): string {
  const base = new URL(`https://site/${at}`);
  const name = decodeURIComponent(new URL(url, base).pathname).slice(1);
  return name === "" || name.endsWith("/") ? `${name}index.html` : name;
}

/** The links of the site written at `out` that lead to no file of it, or to no `id` of a page. */
export function site(out: string): string[] {
  const all = files(out);
  const ids = new Map<string, Set<string>>();
  const pages = all.filter((f) => f.endsWith(".html"));
  for (const page of pages) ids.set(page, new Set(attributes(fs.readFileSync(path.join(out, page), "utf8"), "id")));
  const held = new Set(all);
  const errors: string[] = [];
  for (const page of pages) {
    const text = fs.readFileSync(path.join(out, page), "utf8");
    for (const url of new Set([...attributes(text, "href"), ...attributes(text, "src")])) {
      if (/^[a-z]+:/i.test(url) || url.startsWith("//")) continue;
      const [file, fragment = ""] = url.split("#");
      const name = file === "" ? page : target(page, file);
      if (WRITTEN_AFTER.some((dir) => `/${name}`.startsWith(dir))) continue;
      if (!held.has(name)) {
        errors.push(`${page}: the link ${url} leads to no file of the site`);
      } else if (fragment && !fragment.includes("=") && name.endsWith(".html") && !ids.get(name)?.has(decodeURIComponent(fragment))) {
        errors.push(`${page}: the link ${url} leads to no \`id\` of its page`);
      }
    }
  }
  return errors;
}

/** Fails with every error, or does nothing if there is none. */
function fail(errors: string[]): void {
  if (errors.length) throw new Error(`\n${errors.map((e) => `ERROR ${e}`).join("\n")}`);
}

/** The integration that runs the checks around a build. */
export function checks(): AstroIntegration {
  return {
    name: "stilt-checks",
    hooks: {
      "astro:build:start": () => fail([...repository(), ...unchecked()]),
      "astro:build:done": ({ dir, logger }) => {
        const out = fileURLToPath(dir);
        fail(site(out));
        const count = files(out).filter((f) => f.endsWith(".html")).length;
        logger.info(`${count} pages, every internal link resolves`);
      },
    },
  };
}
