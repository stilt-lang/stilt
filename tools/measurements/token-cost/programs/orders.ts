import { readFileSync } from "node:fs";

/** One validated row of the orders file. */
type Order = { customer: string; qty: number; price: number };

/** Parses one `customer,qty,price` row. */
function parseLine(n: number, text: string): Order {
  const fields = text.split(",");
  if (fields.length !== 3) throw new Error(`line ${n}: expected 3 fields`);
  const [customer, q, p] = fields;
  const qty = Number(q);
  if (q === "" || !Number.isInteger(qty)) throw new Error(`line ${n}: bad qty ${q}`);
  const price = Number(p);
  if (p === "" || Number.isNaN(price)) throw new Error(`line ${n}: bad price ${p}`);
  if (qty <= 0) throw new Error(`line ${n}: qty must be positive`);
  return { customer, qty, price };
}

/** Revenue per customer, largest first. */
function totals(orders: Order[]): [string, number][] {
  const sums = new Map<string, number>();
  for (const o of orders) sums.set(o.customer, (sums.get(o.customer) ?? 0) + o.qty * o.price);
  return [...sums.entries()].sort((a, b) => b[1] - a[1]);
}

function main(): void {
  let orders: Order[];
  try {
    const path = process.argv[2];
    if (path === undefined) throw new Error("usage: orders <file>");
    let text: string;
    try {
      text = readFileSync(path, "utf8");
    } catch {
      throw new Error(`cannot read ${path}`);
    }
    const lines = text.replace(/\n$/, "").split("\n");
    orders = lines.slice(1).map((l, i) => parseLine(i + 2, l));
  } catch (e) {
    console.error(`error: ${(e as Error).message}`);
    process.exit(1);
  }
  for (const [c, t] of totals(orders).slice(0, 3)) console.log(`${c}: ${t.toFixed(2)}`);
}

main();
