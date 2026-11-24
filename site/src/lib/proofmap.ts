// The proof map: what `just proof-map` writes of the Lean model (tools/proof-map), read as the
// pages show it. The model is never described by hand here: every name, statement, citation and
// count comes from the compiled model, so the page can't drift from it.

import fs from "node:fs";
import path from "node:path";
import { place } from "./map";
import { ROOT } from "./repo";

/** Where `just proof-map` writes the map. */
export const MAP = path.join(ROOT, "target/proof-map/map.json");

/** A written declaration of the model. */
export interface Decl {
  /** Its name, without the namespace `Stilt`. */
  n: string;
  /** Its kind: theorem, def, structure, inductive, instance, opaque. */
  k: string;
  /** Its module, and its file in the repository and line there. */
  m: string;
  f: string;
  l: number;
  /** The declarations its statement uses and its proof or body uses, as indexes. */
  s: number[];
  b: number[];
  /** The paragraphs of the Reference its doc cites. */
  c: string[];
  /** Whether `soundness` reaches it. */
  r: boolean;
  d?: string;
  /** Its statement as Lean prints it, for the theorems `soundness` reaches. */
  t?: string;
  a?: string[];
}

/** A field of `Program.Accepted` or `Program.Promises`. */
export interface Field {
  n: string;
  t: string;
  c: string[];
  from: number[];
  d?: string;
}

export type Status = "theorem" | "model" | "described" | "none";

export interface Paragraph {
  id: string;
  text: string;
  by: number[];
  status: Status;
}

export interface Chapter {
  file: string;
  title: string;
  paragraphs: Paragraph[];
}

export interface Module {
  n: string;
  f: string;
  decls: number;
  r: number;
  d?: string;
}

export interface ProofMap {
  decls: Decl[];
  soundness: number;
  accepted: Field[];
  promises: Field[];
  chapters: Chapter[];
  modules: Module[];
  problems: string[];
}

let loaded: ProofMap | null | undefined;

/** The map, or null when `just proof-map` hasn't written it. */
export function proofMap(): ProofMap | null {
  if (loaded === undefined) loaded = fs.existsSync(MAP) ? JSON.parse(fs.readFileSync(MAP, "utf8")) : null;
  return loaded ?? null;
}

/** The page of a paragraph of the Reference. */
export function paragraphHref(map: ProofMap, id: string): string {
  const chapter = map.chapters.find((c) => c.paragraphs.some((p) => p.id === id));
  return chapter ? `${place(`reference/${chapter.file}`) ?? "/reference/"}#${id}` : "/reference/";
}

/** The source page of a declaration, at its line. */
export function sourceHref(d: { f: string; l?: number }): string {
  return `${place(d.f) ?? `/source/${d.f}`}${d.l ? `#L${d.l}` : ""}`;
}

/** The chapters whose subject is what programs mean, which the model sets out to cover, and
 * the others: the text of programs, the tools and the builds. */
export function meaningChapters(map: ProofMap): { meaning: Chapter[]; outside: Chapter[] } {
  const number = (c: Chapter) => Number.parseInt(c.file, 10);
  const meaning = map.chapters.filter((c) => number(c) >= 4 && number(c) <= 17);
  return { meaning, outside: map.chapters.filter((c) => !meaning.includes(c)) };
}

/** The counts of a chapter's paragraphs by status. */
export function counts(paragraphs: Paragraph[]): Record<Status, number> {
  const out: Record<Status, number> = { theorem: 0, model: 0, described: 0, none: 0 };
  for (const p of paragraphs) out[p.status]++;
  return out;
}

/** The modules that `soundness` doesn't reach, by what they hold: counterexamples, which show
 * that a check is needed; examples, which run programs; and results proved apart. */
export function beside(map: ProofMap): { title: string; about: string; modules: Module[] }[] {
  const apart = map.modules.filter((m) => m.r === 0);
  const under = (prefix: string) => apart.filter((m) => m.n === prefix || m.n.startsWith(`${prefix}.`));
  const counter = under("Counterexamples");
  const examples = [...under("Examples"), ...apart.filter((m) => m.n.endsWith(".Examples"))];
  const rest = apart.filter((m) => !counter.includes(m) && !examples.includes(m));
  return [
    { title: "Results proved apart", about: "Theorems of their own: what `without panic` and `without div` promise, and the calculi that state a part of the language on its own.", modules: rest },
    { title: "Counterexamples", about: "Programs that a check rejects, run without the check, showing that each check is needed.", modules: counter },
    { title: "Examples", about: "Programs the model runs and checks by evaluation.", modules: examples },
  ];
}

/** The files of the model's modules, which get source pages. */
export function modelFiles(): string[] {
  return proofMap()?.modules.map((m) => m.f) ?? [];
}

/** A part of the model: the modules under one name below `Stilt`, as `Moves` or `Syntax`. */
export interface Part {
  name: string;
  decls: number;
  reached: number;
  modules: string[];
}

/** The part a module belongs to. */
export const partOf = (module: string): string => module.split(".")[0];

/** The parts of the model and the uses between them: how many declarations of one use one of
 * the other, by statement or proof. */
export function territory(map: ProofMap): { parts: Part[]; uses: [number, number, number][] } {
  const index = new Map<string, number>();
  const parts: Part[] = [];
  for (const m of map.modules) {
    const name = partOf(m.n);
    if (!index.has(name)) { index.set(name, parts.length); parts.push({ name, decls: 0, reached: 0, modules: [] }); }
    const p = parts[index.get(name)!];
    p.decls += m.decls;
    p.reached += m.r;
    p.modules.push(m.n);
  }
  const weight = new Map<string, number>();
  for (const d of map.decls) {
    const from = index.get(partOf(d.m))!;
    for (const j of new Set([...d.s, ...d.b])) {
      const to = index.get(partOf(map.decls[j].m))!;
      if (to !== from) weight.set(`${from},${to}`, (weight.get(`${from},${to}`) ?? 0) + 1);
    }
  }
  const uses = [...weight].map(([k, w]) => { const [a, b] = k.split(",").map(Number); return [a, b, w] as [number, number, number]; });
  return { parts, uses };
}
