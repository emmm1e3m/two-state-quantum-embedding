# Proof audit

[ResetAudit.lean](../lean/ResetAudit.lean) directly checks the two sharp reset laws as limits of the original probability-closure gain functions. It also audits stationary-state saturation and the two displayed matching constructions. Their correspondence to the paper is listed in the [theorem map](../reset-theorem-map.md).

After building the library, run from `lean/`:

```sh
lake env lean ResetAudit.lean
```

The expected output is recorded in [reset-final-audit.log](reset-final-audit.log). Each of the five principal declarations depends only on `propext`, `Classical.choice`, and `Quot.sound`.

Lean is pinned to `v4.35.0`; `lake-manifest.json` fixes dependencies. The paper's literature discussion and numerical figures have their own references and [figure data](../paper/README_figures.md).
