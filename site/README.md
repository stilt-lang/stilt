# Site

Stilt's website, built with [Astro](https://astro.build) and Tailwind CSS from the repository into `target/site`. Every page is static HTML, written from the repository's documents and from what the compiler prints as the site is built, so the site can't drift from either.

| Part | From |
| --- | --- |
| The front page | [`example.lt`](example.lt), with what `stilt show` prints for each of its functions, the command of [`install.sh`](../install.sh), and numbers counted from the repository |
| Learn, `/learn/` | The guide, [`docs/guide/`](../docs/guide/), in the order and groups of its README, and [`docs/commands.md`](../docs/commands.md) |
| The Reference, `/reference/` | [`reference/`](../reference/) and its rationale, with a link on each paragraph's ID |
| The library, `/library/` | `stilt doc --std --json`: each declaration with its signature, the facts beside it, its doc and its examples |
| The error index, `/errors/` | [`docs/errors/`](../docs/errors/) |
| Design, `/design/` | [`docs/design/`](../docs/design/), the goals among them |
| The proof map, `/design/proof-map/` | What [`tools/proof-map`](../tools/proof-map/) reads of the compiled Lean model (`just proof-map`): its parts as a map, the soundness theorem's checks and promises, which paragraphs of the Reference it covers, and every declaration with what it uses |
| The playground, `/playground/` | [`playground/`](../playground/): its scripts as they are, and the builds of `just playground` |
| Sources, `/source/` | Each file and directory of the repository that a page links to and that is no page |

A link written in a document leads where it leads in the repository: to the page of the document it names, or to the page of a file's source. A program of the guide or of the error index opens in the playground, and the words of its info string show on it: the diagnostics it expects mark their lines and link to their codes' pages. Search runs over [Pagefind](https://pagefind.app)'s index, written after the pages.

| Path | Holds |
| --- | --- |
| `src/lib/` | What the pages are made from: the site's map and how links resolve (`map.ts`), Markdown (`markdown.ts`), code blocks (`code.ts`) and their highlighting with the editors' TextMate grammar (`highlight.ts`), what the compiler prints (`stilt.ts`, `shown.ts`), the sources' pages (`sources.ts`), the parts' lists (`nav.ts`), the front page's numbers (`stats.ts`), the proof map's data and drawing (`proofmap.ts`, `graph.ts`), and the checks (`checks.ts`, `claims.ts`) |
| `src/pages/` | A route for each part |
| `src/layouts/`, `src/components/` | The frame of every page and of the documents, and its pieces |
| `src/styles/` | The one stylesheet, light and dark, and its parts for documents, code and the playground |

## Building

`just site` builds the compiler and the playground, installs the site's dependencies from `package-lock.json` when they changed, and runs `npm run build`. It needs Node 22.12 or later. The build fails on any link of a document that leads nowhere in the repository, any link of a page that leads to no file or `id` of the site, and any goal of [`docs/design/goals.md`](../docs/design/goals.md) that names nothing that checks it.

From `site/`, `npm run dev` serves the site as it is edited, and `npm run preview` serves what `npm run build` wrote. `STILT` names the compiler, `target/bin/stilt` by default, and `STILT_PLAYGROUND` the playground's builds, `target/playground` by default.
