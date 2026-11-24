// What a page's frame lists: the parts of the site that the header links, the pages of a page's
// part beside it, in the groups its index gives them, each group folded unless it holds the page,
// and the pages before and after it in reading order.

import { library } from "./stilt";
import { type Doc, groups, inSection, type Section } from "./map";
import { proofMap } from "./proofmap";

/** The parts of the site that the header links, each with its first page. */
export const PARTS: { name: string; href: string; section: Section }[] = [
  { name: "Learn", href: "/learn/", section: "learn" },
  { name: "Reference", href: "/reference/", section: "reference" },
  { name: "Library", href: "/library/", section: "library" },
  { name: "Errors", href: "/errors/", section: "errors" },
  { name: "Playground", href: "/playground/", section: "playground" },
];

/** A link of a part's list. */
export interface Link {
  title: string;
  href: string;
  /** What the list writes before the title, as a chapter's number or an error's code. */
  note?: string;
}

/** A group of a part's list, under its heading, or, for the part's overview, under none. */
export interface Block {
  heading: string;
  links: Link[];
}

/** The link to a document, named as its index names it, or by its title. */
const link = (doc: Doc, title = doc.title, note?: string): Link => ({ title, href: doc.url, note });

/** The overview's block: the part's first page, under no heading. */
const overview = (href: string, title = "Overview"): Block => ({ heading: "", links: [{ title, href }] });

/** The guide's list: its overview, the groups of its contents, and the command line. */
function learn(): Block[] {
  const all = inSection("learn");
  const index = all.find((d) => d.url === "/learn/")!;
  const listed = groups(index.source).map((g) => ({
    heading: g.heading,
    links: g.entries.map((e) => link(e.doc, e.label)),
  }));
  const commands = all.find((d) => d.source === "docs/commands.md")!;
  return [overview(index.url), ...listed, { heading: "Tools", links: [link(commands, "The command line")] }];
}

/** The Reference's list: its overview, its chapters in their groups, then the rationale and
 * the documents beside the chapters. */
function reference(): Block[] {
  const all = inSection("reference");
  const index = all.find((d) => d.url === "/reference/")!;
  const chapters = groups(index.source).map((g) => ({
    heading: g.heading,
    links: g.entries.map((e) => link(e.doc, e.label, /^(\d+)\./.exec(e.doc.title)?.[1])),
  }));
  const listed = new Set(chapters.flatMap((b) => b.links.map((l) => l.href)));
  const rationale = all.filter((d) => d.url.startsWith("/reference/rationale/"));
  const others = all.filter((d) => d !== index && !listed.has(d.url) && !rationale.includes(d));
  return [
    overview(index.url),
    ...chapters,
    { heading: "Beside the chapters", links: others.map((d) => link(d)) },
    {
      heading: "Rationale",
      links: rationale.map((d) => link(d, d.title.replace(/^Rationale:\s*/i, "").replace(/^\d+\.\s*/, ""), /(\d+)/.exec(d.source)?.[1]?.replace(/^0/, ""))),
    },
  ];
}

/** The error index's list: its groups, each code with its title. */
function errors(): Block[] {
  const index = inSection("errors").find((d) => d.url === "/errors/")!;
  return [
    overview(index.url, "All codes"),
    ...groups(index.source).map((g) => ({
      heading: g.heading,
      links: g.entries.map((e) => link(e.doc, e.blurb.replaceAll("`", ""), e.label)),
    })),
  ];
}

/** The library's list: its overview and each module, grouped by its tier. */
function modules(): Block[] {
  const tiers = ["core", "advanced", "meta", "systems"];
  const blocks = tiers
    .map((tier) => ({
      heading: `The ${tier} tier`,
      links: library().filter((m) => m.tier === tier).map((m) => ({ title: m.address, href: `/library/${m.address}/` })),
    }))
    .filter((b) => b.links.length);
  return [overview("/library/"), ...blocks];
}

/** The list beside the pages of `section`. */
export function sidebar(section: Section): Block[] {
  switch (section) {
    case "learn":
      return learn();
    case "reference":
      return reference();
    case "errors":
      return errors();
    case "library":
      return modules();
    case "design":
      return [{
        heading: "",
        links: [
          ...inSection("design").map((d) => link(d)),
          ...(proofMap() ? [{ href: "/design/proof-map/", title: "Proof map" }] : []),
        ],
      }];
    default:
      return [];
  }
}

/** The pages before and after the page at `href` in its part's list. */
export function neighbours(blocks: Block[], href: string): { previous?: Link; next?: Link } {
  const all = blocks.flatMap((b) => b.links);
  const at = all.findIndex((l) => l.href === href);
  if (at < 0) return {};
  return { previous: all[at - 1], next: all[at + 1] };
}

/** The heading of the group that lists the page at `href`, if it has one. */
export function group(blocks: Block[], href: string): string {
  return blocks.find((b) => b.links.some((l) => l.href === href))?.heading ?? "";
}
