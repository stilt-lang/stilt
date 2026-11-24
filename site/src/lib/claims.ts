// The goals page, `docs/design/goals.md`, is the site's list of claims: each goal with its target
// and what measures it. A goal of a table with a `Measured by` column must link to what checks
// it, a test, a suite, a recipe or a budget, unless people measure it, in a study, a survey or a
// review, as its cell says. A goal with neither is a claim that nothing checks, and fails the
// build, so a claim on the site has a test behind it or says who judges it.

import { read } from "./repo";

/** The page of the goals, from the repository's root. */
export const GOALS = "docs/design/goals.md";

/** The words of a cell that says people measure the goal, not the repository's checks. */
const BY_PEOPLE = ["study", "survey", "review"];

/** The cells of a table's row, trimmed, split at each `|` that no `\` escapes. */
export function cells(line: string): string[] {
  const inner = line.trim().replace(/^\|/, "").replace(/\|$/, "");
  return inner.split(/(?<!\\)\|/).map((c) => c.trim());
}

/** The goals of `text` whose `Measured by` cell holds no link and names no study, survey or
 * review. */
export function unbacked(text: string): string[] {
  const found: string[] = [];
  // The column of `Measured by` in the table being read, once its header is read.
  let column: number | null | undefined;
  for (const raw of text.split("\n")) {
    const line = raw.trim();
    if (!line.startsWith("|")) {
      column = undefined;
      continue;
    }
    const row = cells(line);
    if (column === undefined) {
      const at = row.indexOf("Measured by");
      column = at < 0 ? null : at;
      continue;
    }
    const goal = row[0];
    if (column === null || goal === undefined || goal.startsWith("---")) continue;
    const measured = row[column] ?? "";
    const byPeople = BY_PEOPLE.some((w) => measured.toLowerCase().includes(w));
    if (!measured.includes("](") && !byPeople) found.push(goal.replace(/^`|`$/g, ""));
  }
  return found;
}

/** An error for each goal that names nothing that checks it. */
export function unchecked(): string[] {
  return unbacked(read(GOALS)).map(
    (goal) =>
      `${GOALS}: the goal \`${goal}\` links to nothing that checks it, and no study, survey or ` +
      "review measures it",
  );
}
