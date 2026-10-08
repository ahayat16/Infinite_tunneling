# Infinite Zero — manuscript and Lean

This website accompanies the Lean formalization of a fixed magnetic
double-well potential with infinitely many vanishing tunneling coefficients.
It presents the manuscript alongside the formal statements and proofs,
with a dependency explorer and documentation of the three classical admissions.

Start with `thm_main` for the main theorem, follow the reading guide to inspect
the explicit potential and spectral definitions, or open **Admissions** for
the precise statements, justifications, and references of the admitted results.

## Run locally

Requirements: **Node.js 22.13 or later**, npm, and Python 3.9 or later.

```sh
cd website
npm ci
npm run dev
```

Open the address printed by the server, normally <http://localhost:3000>.

The data snapshot is regenerated automatically before development and builds.
The landing page is `thm_main`. The sidebar provides a reading guide and a
search across every declaration in the repository's Lean audit.

## What readers can inspect

- **Side-by-side reading:** explanations of the main statements and definitions,
  labelled manuscript excerpts, verbatim Lean source, and expandable proofs.
- **Definitions:** follow linked names to read their definitions, documentation,
  and dependencies. Each excerpt links to the complete source file.
- **Dependency graph and tree:** adjustable depth, zoom, admission-path filter,
  expandable branches and DOT export. Clicking a graph node changes the root;
  clicking a tree entry opens its source. The graph shows at most 70 nodes and
  reports truncation. From `thm_main`, select depth 10 and the admission filter
  to see all three classical admissions. The full graph is also downloadable.
- **Admissions:** three admission contracts with their mathematical
  justifications and references, the admission register, and the statement
  audit, with links to the corresponding source files.
- **Shareable links:** fragments preserve the view and declaration, for example
  `#read/InfiniteZero.groundEnergy` or `#graph/InfiniteZero.thm_main`.

The “TeX source” tab shows the original manuscript excerpt.

## Refresh after a Lean change

From the repository root:

```sh
lake build
python3 scripts/update_status.py
cd website
npm run data
```

The repository's `update_status.py` queries the Lean environment. The website
generator consumes that audit and extracts code from the current source files.
Run these commands after changing a proof to refresh the dependencies and excerpts.

Graph edges come from `docs/declarations.json`, which records
references in elaborated types and bodies. Generated projections and constants
are grouped under their source declaration. The graph covers declarations in
this repository.

In the interactive graph and its DOT export, **A → B means “A uses B”**.
The separately downloadable `docs/dependencies.dot` uses the reverse
convention: dependency → user.

“No admissions” means no `sorryAx` in the declaration or its dependencies.

English review-note copies are stored in `content/notes/en/`. Their manifest
pins the hash of each repository source note. When a source changes, synchronize
the review copy and update that hash before regenerating the website.

## Build and share a static export

```sh
npm run build
npm run preview
```

The complete static site is in **`dist/client/`**. The preview server serves it
at <http://localhost:4173>, with Lean modules loaded on demand.

Publish the contents of `dist/client/`, including `.nojekyll`, to any static
host or a GitHub Pages subdirectory. Relative asset and data URLs let the same
export work under a repository path.

## Share an offline HTML file

```sh
npm run build
node scripts/export-share.mjs
```

The files are written to `outputs/share/`:

- `infinite-zero.html`: open directly in a browser, with the reader, sources,
  mathematical fonts, and dependency graph included.
- `infinite-zero-offline.zip`: the same HTML file compressed for sharing.
- `infinite-zero-site.zip`: the static website for publishing on a web host.

## Layout and checks

```text
content/reading.json          English notices and reading guides
content/notes/en/             English review-note copies
scripts/generate_data.py      Source extraction and audit snapshot
scripts/finalize_export.py    Portable static asset references
components/review-site.tsx    Reader, search, graph and admissions
lib/model.ts                 Graph neighbourhoods and admission ancestry
lib/math.ts                  Manuscript macros and reading renderer
public/data/                 Generated catalogue and per-module source
public/sources/              Generated original sources and notes
public/notes/en/             Generated copies of English notes
content/generated/           Generated initial-page data
dist/client/                Generated publishable export
```

```sh
npm run data
npm test
npm run typecheck
npm run lint
npm run build
```

Tests check verbatim Lean extraction, manuscript excerpts, reading-guide links,
audited edges, graph limits and cycles, the three admissions reachable from
`thm_main`, and mathematical formula parsing. Lint covers the application code;
type checking also includes the shared UI components.

Built with React, TypeScript, Vinext/Vite, shadcn and KaTeX.

## AI acknowledgement

Most of this website building on top of the formalization and the explanations associated were generated by GPT-6-Astra.
