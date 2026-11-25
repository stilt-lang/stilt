// The images that other sites and systems fetch: the icon of a home screen, and the picture that
// a link to the site shows.

import fs from "node:fs";
import path from "node:path";
import type { APIRoute } from "astro";
import { ROOT } from "../lib/repo";

export function getStaticPaths() {
  return ["apple-touch-icon", "social"].map((image) => ({ params: { image } }));
}

export const GET: APIRoute = ({ params }) =>
  new Response(fs.readFileSync(path.join(ROOT, "brand", `${params.image}.png`)), {
    headers: { "Content-Type": "image/png" },
  });
