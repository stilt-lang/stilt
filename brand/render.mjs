// Writes what is derived from this folder's drawings: the PNGs, and the file icons that VS Code's
// extension ships. Run from the repository's root once the site's dependencies are installed:
//
//     node brand/render.mjs

import { copyFileSync, mkdirSync } from "node:fs";
import { createRequire } from "node:module";
import { fileURLToPath } from "node:url";

const root = fileURLToPath(new URL("..", import.meta.url));
const sharp = createRequire(`${root}site/package.json`)("sharp");

/** Each PNG, from the drawing it shows, at its width and height in pixels. */
const images = [
  ["brand/icon.svg", "brand/icon.png", 512, 512],
  ["brand/icon.svg", "brand/apple-touch-icon.png", 180, 180],
  ["brand/icon.svg", "editors/vscode/icon.png", 256, 256],
  ["brand/social.svg", "brand/social.png", 1280, 640],
];
for (const [from, to, width, height] of images) {
  await sharp(root + from, { density: 288 }).resize(width, height).png({ compressionLevel: 9 }).toFile(root + to);
}

// A file's icon is at most 32 px wide, so it is the mark's small cut.
mkdirSync(`${root}editors/vscode/icons`, { recursive: true });
copyFileSync(`${root}brand/mark-small.svg`, `${root}editors/vscode/icons/stilt-light.svg`);
copyFileSync(`${root}brand/mark-small-on-dark.svg`, `${root}editors/vscode/icons/stilt-dark.svg`);
