// The proof map as the explorer of /design/proof-map/ reads it, copied from what
// `just proof-map` wrote (src/lib/proofmap.ts).
import type { APIRoute } from "astro";
import { proofMap } from "../../../lib/proofmap";

export const GET: APIRoute = () =>
  new Response(JSON.stringify(proofMap() ?? { decls: [] }), {
    headers: { "content-type": "application/json" },
  });
