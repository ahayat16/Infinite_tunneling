# Manuscript

The article source is [Infinite_Zero_Tunneling_Lean_oriented_V2.tex](Infinite_Zero_Tunneling_Lean_oriented_V2.tex).
Its image assets are in `figures/`; the bibliography is included in the source.
The blue passages are the formalization expansions containing the sublemmas.

Compile from the repository root with a TeX installation that includes `latexmk`:

```sh
latexmk -cd -pdf -interaction=nonstopmode -halt-on-error article/Infinite_Zero_Tunneling_Lean_oriented_V2.tex
```

The PDF and auxiliary files are written beside the source and ignored by Git.
The PDF is named `Infinite_Zero_Tunneling_Lean_oriented_V2.pdf`.

After changing the manuscript, refresh the sublemma index and website excerpts:

```sh
python3 scripts/blueprint_index.py
cd website
npm run data
```

The [review website](../website/README.md) compares the manuscript with Lean;
the [statement audit](../docs/STATEMENT_AUDIT.md) explains the correspondence
between `thm:main` and the formal theorem.
