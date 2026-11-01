# Two-state quantum embedding

The latest paper is **Sharp reset-error asymptotics for time-homogeneous qubit dynamics**, by **Tingyu Zhang and Yan Cen**. Corresponding author: **Yan Cen**.

[English paper](paper/reset_manuscript.pdf) · [中文论文](paper/reset_manuscript_zh.pdf) · [Reset theorem map](reset-theorem-map.md) · [中文说明](README.zh-CN.md)

For fixed-basis qubit reset, let `ε = P(0|1)` be the actual disturbance and `G(ε) = max(ε-a)`, where `a = P(0|0)`. Over all time-independent qubit GKSL generators and their probability closure, the sharp law is

$$G(\epsilon)\sim\frac{4}{e}\frac{\epsilon}{\log(1/\epsilon)}.$$

For generators admitting a stationary state diagonal in the preparation–measurement basis, the sharp law is

$$G_{\mathrm{diag}}(\epsilon)\sim\frac{64}{e^2}\frac{\epsilon}{\log^2(1/\epsilon)}.$$

The Lean development proves both laws, the stationary coherence and purity constraints for saturating sequences, and the two displayed single-jump matching constructions. The bilingual paper has seven main sections, including separate **Discussion** and **Conclusions** sections; acknowledgments, data and code availability, and declarations await author completion. Both versions share English figure captions and a BibTeX database; see the [author review and build notes](paper/reset_author_review.md).

## Earlier swap-endpoint paper

**Sharp swap-endpoint geometry and an analytic boundary for two-state quantum embedding**, by **Tingyu Zhang**.

[English paper](paper/manuscript.pdf) · [中文论文](paper/manuscript_zh.pdf) · [Swap theorem map](theorem-map.md)

This paper proves the exact swap-endpoint tangent cone and local real analyticity of the actual lower boundary. Its papers, proofs, and audit remain available. The exact finite-error reset boundary, higher-order asymptotics, and complete middle boundary remain open; see [research status](research-status.md).

## Check the proofs

Install [elan](https://github.com/leanprover/elan). For a memory-bounded build, set `LEAN_NUM_THREADS=2` (`$env:LEAN_NUM_THREADS='2'` in PowerShell), then run:

```sh
cd lean
lake exe cache get
lake build TwoStateQuantumEmbedding QICLean
lake env lean ResetAudit.lean
lake env lean ../verification/PublicationAudit.lean
```

Lean is pinned to `v4.35.0`; `lean/lake-manifest.json` fixes Mathlib and its dependencies. The principal audited results use only `propext`, `Classical.choice`, and `Quot.sound`. [Verification evidence](verification/README.md) distinguishes the earlier 9149-job public-package build from the recorded 9182-job integrated build containing the reset results.

## Build the reset papers

Use a LaTeX distribution with REVTeX 4.2, AMS packages, `ctex`, and Fandol fonts. Keep the shared `reset_captions.tex`, `reset_references.bib`, and the two figure PDFs beside the manuscript sources. REVTeX selects `apsrev4-2` automatically; `longbibliography` retains article titles.

```sh
cd paper
pdflatex -interaction=nonstopmode -halt-on-error reset_manuscript.tex
bibtex reset_manuscript
pdflatex -interaction=nonstopmode -halt-on-error reset_manuscript.tex
pdflatex -interaction=nonstopmode -halt-on-error reset_manuscript.tex
xelatex -interaction=nonstopmode -halt-on-error reset_manuscript_zh.tex
bibtex reset_manuscript_zh
xelatex -interaction=nonstopmode -halt-on-error reset_manuscript_zh.tex
xelatex -interaction=nonstopmode -halt-on-error reset_manuscript_zh.tex
```

The [figure data and redraw script](paper/README_figures.md) reproduce the plots from the saved data.

The vendored QICLean sources retain their upstream authorship and Apache-2.0 license; see [provenance](lean/vendor/QICLean/README.md) and [NOTICE.md](NOTICE.md).
