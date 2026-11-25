# Brand

Stilt's logo, and the images made from it. The mark is a stilt that stoops to feed, drawn under one straight edge from its tail to the tip of its bill.

| File | Use it for |
| --- | --- |
| `logo.svg`, `logo-on-dark.svg` | The mark beside the word, on a light or a dark ground |
| `mark.svg`, `mark-on-dark.svg` | The mark alone, above 32 px |
| `mark-small.svg`, `mark-small-on-dark.svg` | The mark at 32 px and less: no bands on the wing, and a thicker head, bill and legs |
| `icon.svg`, `icon.png` | The mark on a dark tile, for an avatar or an application's icon |
| `apple-touch-icon.png` | The same tile, for the site's icon on a home screen |
| `social.svg`, `social.png` | The picture that a link to the site or the repository shows |

## Colors

The drawings use three colors:

| Color | Value | Where |
| --- | --- | --- |
| Ink | `#0F1114` | The bird and the word on a light ground, and the dark ground |
| Paper | `#F4F4EF` | The bird and the word on a dark ground, and the light ground |
| Coral | `#FF4A2E` | The legs, on either ground |

Coral is for the legs alone. On white it has too little contrast for text, and it is close to the color of an error.

## Construction

The mark is drawn in a square whose side is 14 times the radius `h` of the head:

- The spine, from tail to bill, is the square's diagonal. The feet and the tip of the bill stand on its base, and the left foot is under the tail.
- The head, the body and the back of the wing are arcs of circles whose radii are `h`, `φ²h` and `φ⁷h`, where `φ` is the golden ratio. The throat is the arc that joins head to body and leaves a neck `φh` wide.
- The legs lean 22.5°. The wing's bands are as wide as a leg, and the slits between them half the gap between the legs.

## Change a drawing

Edit the SVG, then write the PNGs and the file icons of VS Code's extension, which are made from it. The site's dependencies must be installed, which `just site` does:

```sh
node brand/render.mjs
```
