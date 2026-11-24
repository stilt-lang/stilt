// What the compiler says, as the site is built: what `stilt show` prints for each function of the
// front page's example, and the standard library's documentation from `stilt doc --std --json`
// (docs.std). The pages print what the compiler prints, never a copy of it.

import { execFileSync } from "node:child_process";
import { STILT, ROOT, read } from "./repo";

/** The example the front page shows, a program of one file. */
export const EXAMPLE = "site/example.lt";

/** The output of `stilt ARGS`, which must succeed and write nothing on stderr. */
function stilt(args: string[]): string {
  try {
    return execFileSync(STILT, args, {
      cwd: ROOT,
      encoding: "utf8",
      maxBuffer: 64 << 20,
      stdio: ["ignore", "pipe", "pipe"],
    });
  } catch (error) {
    const stderr = (error as { stderr?: string }).stderr ?? String(error);
    throw new Error(`stilt ${args.join(" ")} failed: ${stderr}`);
  }
}

/** A function of the example, with what `stilt show` prints for it. */
export interface Shown {
  name: string;
  shown: string;
}

/** The example's text, and what `stilt show main.NAME` prints for each of its functions. */
export function example(): { source: string; functions: Shown[] } {
  const source = read(EXAMPLE);
  const checked = stilt(["check", EXAMPLE]);
  if (checked !== "") throw new Error(`${EXAMPLE} has diagnostics:\n${checked}`);
  const names = [...source.matchAll(/^fn ([A-Za-z_][A-Za-z0-9_]*)/gm)].map((m) => m[1]);
  const functions = names.map((name) => ({ name, shown: stilt(["show", `main.${name}`, EXAMPLE]) }));
  return { source, functions };
}

/** A declaration of the library, as `stilt doc --json` gives it. */
export interface Item {
  kind: string;
  name: string;
  signature: string;
  facts: string[] | null;
  doc: string;
  examples: string[];
  members: Item[];
}

/** A module of the library. */
export interface Module {
  address: string;
  tier: string;
  description: string;
  items: Item[];
}

let modules: Module[] | null = null;

/** The standard library's modules. */
export function library(): Module[] {
  modules ??= (JSON.parse(stilt(["doc", "--std", "--json"])) as { modules: Module[] }).modules;
  return modules;
}

/** The module's file in the repository, which its documentation's links are written from. */
export function file(module: Module): string {
  return `std/${module.address.replace(/^std\./, "").replaceAll(".", "/")}.lt`;
}

/** The command of `install.sh` that installs the newest release, from its header. */
export function install(): string {
  const line = read("install.sh")
    .split("\n")
    .filter((l) => l.startsWith("#"))
    .map((l) => l.slice(1).trim())
    .find((l) => l.startsWith("curl ") && l.endsWith("| sh"));
  if (!line) throw new Error("install.sh: its header shows no command that installs Stilt");
  return line;
}
