// The drawings of brand/ as the pages inline them: what is inside each SVG, with its ink replaced
// by the text's colour, so a mark follows the theme, and its accent by the site's token.

import { read } from "./repo";

const INK = "#0F1114";
const ACCENT = "#FF4A2E";

/** The elements of the drawing `brand/NAME.svg`. */
function inside(name: string): string {
  const svg = read(`brand/${name}.svg`);
  const body = svg.slice(svg.indexOf(">") + 1, svg.lastIndexOf("</svg>"));
  return body.replaceAll(INK, "currentColor").replaceAll(ACCENT, "var(--accent)").trim();
}

/** The mark's cut for 32 px and less, in a square of 1000. */
export const smallMark = inside("mark-small");

/** The mark beside the word, in the box `LOGO_BOX`. */
export const logo = inside("logo");
export const LOGO_BOX = "-6 -546 1164.95 558";

/** The word alone, where it stands in the logo. */
export const word = logo.slice(logo.lastIndexOf("<g "));

/** The site's icon, as a data URL: the small mark, which follows the system's theme. */
export function favicon(): string {
  const shapes = smallMark.replaceAll('fill="currentColor"', 'class="i"').replaceAll("var(--accent)", ACCENT);
  const style = `<style>.i{fill:${INK}}@media(prefers-color-scheme:dark){.i{fill:#F4F4EF}}</style>`;
  const svg = `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 1000 1000">${style}${shapes}</svg>`;
  return "data:image/svg+xml," + encodeURIComponent(svg);
}
