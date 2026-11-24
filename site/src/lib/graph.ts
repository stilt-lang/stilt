// A layered drawing of a graph whose edges point from what uses to what is used, so a
// theorem sits above what it rests on: the strongly connected parts are merged, each node is
// put one layer below the lowest node that uses it, the edges that other paths already imply
// are dropped, and each layer is ordered by its neighbours' places. Used by the proof map,
// at build time and in the browser.

export interface GraphNode {
  id: string;
  label: string;
  /** How wide the node is drawn, in pixels. */
  width: number;
}

export interface Placed extends GraphNode {
  x: number;
  y: number;
  layer: number;
}

export interface Drawn {
  nodes: Placed[];
  /** The edges kept, from user to used, as indexes into `nodes`. */
  edges: [number, number][];
  width: number;
  height: number;
}

const ROW = 92;
const GAP = 18;
const HEIGHT = 46;

/** The strongly connected components of a graph given as successor lists (Tarjan). */
function components(next: number[][]): number[] {
  const n = next.length;
  const comp = new Array<number>(n).fill(-1);
  const low = new Array<number>(n).fill(0);
  const seen = new Array<number>(n).fill(-1);
  const stack: number[] = [];
  const on = new Array<boolean>(n).fill(false);
  let time = 0;
  let count = 0;
  const visit = (v: number) => {
    seen[v] = low[v] = time++;
    stack.push(v);
    on[v] = true;
    for (const w of next[v]) {
      if (seen[w] < 0) { visit(w); low[v] = Math.min(low[v], low[w]); }
      else if (on[w]) low[v] = Math.min(low[v], seen[w]);
    }
    if (low[v] === seen[v]) {
      let w: number;
      do { w = stack.pop()!; on[w] = false; comp[w] = count; } while (w !== v);
      count++;
    }
  };
  for (let v = 0; v < n; v++) if (seen[v] < 0) visit(v);
  return comp;
}

/** The edges of a DAG that no other path implies. */
function reduce(next: number[][]): [number, number][] {
  const reach = next.map(() => new Set<number>());
  const walk = (v: number, from: number, out: Set<number>) => {
    for (const w of next[v]) if (!out.has(w)) { out.add(w); walk(w, from, out); }
  };
  next.forEach((_, v) => walk(v, v, reach[v]));
  const kept: [number, number][] = [];
  next.forEach((succ, u) => {
    for (const v of succ) if (!succ.some((w) => w !== v && reach[w].has(v))) kept.push([u, v]);
  });
  return kept;
}

/** Each node's layer: one below the lowest node that uses it, the unused ones at the top. */
function layers(next: number[][]): number[] {
  const order: number[] = [];
  const done = new Array<boolean>(next.length).fill(false);
  const visit = (v: number) => { if (done[v]) return; done[v] = true; next[v].forEach(visit); order.push(v); };
  next.forEach((_, v) => visit(v));
  const layer = new Array<number>(next.length).fill(0);
  for (const u of order.reverse()) for (const v of next[u]) layer[v] = Math.max(layer[v], layer[u] + 1);
  return layer;
}

/** The nodes of each layer, ordered by the mean place of their neighbours, swept down and up. */
function order(rows: number[][], edges: [number, number][]): number[][] {
  const up = new Map<number, number[]>();
  const down = new Map<number, number[]>();
  for (const [u, v] of edges) { (down.get(u) ?? down.set(u, []).get(u)!).push(v); (up.get(v) ?? up.set(v, []).get(v)!).push(u); }
  const place = new Map<number, number>();
  rows.forEach((r) => r.forEach((v, i) => place.set(v, i / Math.max(1, r.length - 1))));
  const sweep = (r: number[], by: Map<number, number[]>) => {
    const mean = (v: number) => { const ns = by.get(v) ?? []; return ns.length ? ns.reduce((s, w) => s + place.get(w)!, 0) / ns.length : place.get(v)!; };
    r.sort((a, b) => mean(a) - mean(b));
    r.forEach((v, i) => place.set(v, i / Math.max(1, r.length - 1)));
  };
  for (let pass = 0; pass < 12; pass++) {
    if (pass % 2 === 0) for (let i = 1; i < rows.length; i++) sweep(rows[i], up);
    else for (let i = rows.length - 2; i >= 0; i--) sweep(rows[i], down);
  }
  return rows;
}

/** Lays out `nodes` with `uses`, edges from user to used, as indexes. */
export function layout(nodes: GraphNode[], uses: [number, number][]): Drawn {
  const comp = components(nodes.map((_, i) => uses.filter(([u]) => u === i).map(([, v]) => v)));
  const k = Math.max(-1, ...comp) + 1;
  const cnext = Array.from({ length: k }, () => new Set<number>());
  for (const [u, v] of uses) if (comp[u] !== comp[v]) cnext[comp[u]].add(comp[v]);
  const lists = cnext.map((s) => [...s]);
  const kept = reduce(lists);
  const clayer = layers(lists);
  const rep = new Map<number, number>();
  nodes.forEach((_, i) => { if (!rep.has(comp[i])) rep.set(comp[i], i); });
  const edges = kept.map(([a, b]) => [rep.get(a)!, rep.get(b)!] as [number, number]);
  const depth = Math.max(0, ...clayer) + 1;
  const rows: number[][] = Array.from({ length: depth }, () => []);
  nodes.forEach((_, i) => rows[clayer[comp[i]]].push(i));
  order(rows, edges);
  const widths = rows.map((r) => r.reduce((s, i) => s + nodes[i].width + GAP, -GAP));
  const width = Math.max(...widths, 200);
  const placed: Placed[] = nodes.map((n) => ({ ...n, x: 0, y: 0, layer: 0 }));
  rows.forEach((r, layer) => {
    let x = (width - widths[layer]) / 2;
    for (const i of r) { placed[i] = { ...nodes[i], x: x + nodes[i].width / 2, y: layer * ROW + HEIGHT / 2 + 8, layer }; x += nodes[i].width + GAP; }
  });
  return { nodes: placed, edges, width, height: depth * ROW };
}

/** The height of a drawn node. */
export const NODE_HEIGHT = HEIGHT;

/** An edge drawn from the bottom of `a` to the top of `b`. */
export function curve(a: Placed, b: Placed): string {
  const y1 = a.y + HEIGHT / 2;
  const y2 = b.y - HEIGHT / 2;
  const mid = (y1 + y2) / 2;
  return `M${a.x},${y1} C${a.x},${mid} ${b.x},${mid} ${b.x},${y2}`;
}
