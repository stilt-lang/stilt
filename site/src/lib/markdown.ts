// Markdown as the site renders it: CommonMark with GitHub's tables, each heading given the ID
// that GitHub gives it, so a document's links to `#a-heading` open where they open there, each
// paragraph ID of the Reference shown as a link to its paragraph (reference/README.md, Paragraph
// IDs), each link's destination as the site's map resolves it, and each fenced block as
// `code.ts` renders it.

import type { Element, Root as Hast } from "hast";
import { toString } from "hast-util-to-string";
import type { Code, Root as Mdast } from "mdast";
import rehypeRaw from "rehype-raw";
import rehypeSlug from "rehype-slug";
import rehypeStringify from "rehype-stringify";
import remarkGfm from "remark-gfm";
import remarkParse from "remark-parse";
import remarkRehype from "remark-rehype";
import { unified } from "unified";
import { SKIP, visit } from "unist-util-visit";
import { block } from "./code";
import { resolve } from "./map";

/** A heading of a page, which its contents list. */
export interface Heading {
  depth: number;
  id: string;
  text: string;
}

/** A document as HTML, with its headings of levels 2 and 3. */
export interface Rendered {
  html: string;
  headings: Heading[];
}

/** How to render a document: the repository's file it is, and whether its programs open. */
export interface Options {
  from: string;
  opens?: boolean;
  /** Whether to leave out the first heading of level 1, which the page shows itself. */
  untitled?: boolean;
}

/** Each line that holds only a paragraph's anchor, as a link that shows its ID. */
function anchors(text: string): string {
  return text.replace(
    /^<a id="([^"]+)"><\/a>[ \t]*$/gm,
    (_, id: string) => `<a class="paragraph-id" id="${id}" href="#${id}">${id}</a>`,
  );
}

/** Rewrites each link's destination, and renders each fenced block. */
function repository(options: Options) {
  return (tree: Mdast) => {
    visit(tree, ["link", "definition", "image"], (node) => {
      const link = node as { url: string };
      link.url = resolve(options.from, link.url).href;
    });
    visit(tree, "code", (node: Code, index, parent) => {
      if (!parent || index === undefined) return;
      const value = block(node.value, node.lang ?? null, node.meta ?? null, !!options.opens);
      parent.children[index] = { type: "html", value };
      return SKIP;
    });
  };
}

/** Collects the headings, wraps tables to scroll, and drops comments and the title if asked. */
function page(options: Options, headings: Heading[]) {
  return (tree: Hast) => {
    let titled = false;
    visit(tree, (node, index, parent) => {
      if (node.type === "comment" && parent && index !== undefined) {
        parent.children.splice(index, 1);
        return [SKIP, index];
      }
      if (node.type !== "element") return;
      const element = node as Element;
      if (element.tagName === "h1" && options.untitled && !titled && parent && index !== undefined) {
        titled = true;
        parent.children.splice(index, 1);
        return [SKIP, index];
      }
      const depth = /^h([23])$/.exec(element.tagName);
      if (depth) {
        const id = String(element.properties.id ?? "");
        headings.push({ depth: Number(depth[1]), id, text: toString(element) });
      }
      const first = element.children[0];
      if (element.tagName === "p" && first?.type === "text" && first.value.startsWith("Tests: ")) {
        element.properties.className = ["tests"];
      }
      if (element.tagName === "table" && parent && index !== undefined) {
        const wrap: Element = {
          type: "element",
          tagName: "div",
          properties: { className: ["table-scroll"] },
          children: [element],
        };
        parent.children[index] = wrap;
        return SKIP;
      }
    });
  };
}

/** The document `text` as HTML, with its headings. */
export function render(text: string, options: Options): Rendered {
  const headings: Heading[] = [];
  const html = unified()
    .use(remarkParse)
    .use(remarkGfm)
    .use(() => repository(options))
    .use(remarkRehype, { allowDangerousHtml: true })
    .use(rehypeRaw)
    .use(rehypeSlug)
    .use(() => page(options, headings))
    .use(rehypeStringify)
    .processSync(anchors(text));
  return { html: String(html), headings };
}

/** The destinations of the links of `text`, as written. */
export function links(text: string): string[] {
  const out: string[] = [];
  const tree = unified().use(remarkParse).use(remarkGfm).parse(text);
  visit(tree, ["link", "definition", "image"], (node) => {
    out.push((node as { url: string }).url);
  });
  for (const match of text.matchAll(/<a [^>]*href="([^"]+)"/g)) out.push(match[1]);
  return out;
}
