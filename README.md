# Sharp reset-error asymptotics for time-homogeneous qubit dynamics

**Tingyu Zhang and Yan Cen** · Corresponding author: **Yan Cen**

[English paper](paper/reset_manuscript.pdf) · [中文论文](paper/reset_manuscript_zh.pdf) · [中文说明](README.zh-CN.md)

At fixed actual disturbance `ε = P(0|1)`, the largest population-order reversal is `G(ε) = max(ε-a)`, with `a = P(0|0)`. Over time-independent qubit GKSL dynamics and its probability closure,

$$G(\epsilon)\sim\frac{4}{e}\frac{\epsilon}{\log(1/\epsilon)}.$$

For generators admitting a stationary state diagonal in the preparation–measurement basis,

$$G_{\mathrm{diag}}(\epsilon)\sim\frac{64}{e^2}\frac{\epsilon}{\log^2(1/\epsilon)}.$$

## Paper and figures

The [English source](paper/reset_manuscript.tex) and [Chinese source](paper/reset_manuscript_zh.tex) share [captions](paper/reset_captions.tex), a [BibTeX database](paper/reset_references.bib), and two figure PDFs. Acknowledgments, data/code availability, and declarations contain placeholders for author completion.

Use a TeX distribution with REVTeX 4.2, AMS packages, `ctex`, and Fandol fonts:

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

The [figure guide](paper/README_figures.md) describes the supplied data and `plot_reset_figures.py`. Running the script with Python, NumPy, and Matplotlib redraws both figures from the saved CSV files.

## Formal proofs

The [theorem map](reset-theorem-map.md) links the two laws, stationary-state saturation, and explicit attaining constructions to Lean declarations. Build and audit them with:

```sh
cd lean
lake exe cache get
lake build TwoStateQuantumEmbedding QICLean
lake env lean ResetAudit.lean
```

Lean is pinned to `v4.35.0`; the manifest fixes dependencies. Set `LEAN_NUM_THREADS=2` to limit concurrency. See the [audit guide](verification/README.md) and [third-party notices](NOTICE.md).
