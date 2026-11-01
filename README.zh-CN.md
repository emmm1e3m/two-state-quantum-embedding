# 时间齐次量子比特动力学的尖锐重置误差渐近律

**Tingyu Zhang、Yan Cen** · 通讯作者：**Yan Cen**

[中文论文](paper/reset_manuscript_zh.pdf) · [English paper](paper/reset_manuscript.pdf) · [English](README.md)

固定实际扰动 `ε = P(0|1)`，记 `a = P(0|0)`，最大布居排序反转量为 `G(ε) = max(ε-a)`。在全部时间无关量子比特 GKSL 动力学及其概率闭包上，

$$G(\epsilon)\sim\frac{4}{e}\frac{\epsilon}{\log(1/\epsilon)}.$$

若生成元存在制备—测量基中的对角稳态，则

$$G_{\mathrm{diag}}(\epsilon)\sim\frac{64}{e^2}\frac{\epsilon}{\log^2(1/\epsilon)}.$$

## 论文与图表

[中文源码](paper/reset_manuscript_zh.tex)和[英文源码](paper/reset_manuscript.tex)共用[英文图注](paper/reset_captions.tex)、[BibTeX 书目](paper/reset_references.bib)及两幅 PDF 图。致谢、数据与代码可用性、声明保留占位，供作者核定。

TeX 环境需含 REVTeX 4.2、AMS 宏包、`ctex` 和 Fandol 字体：

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

[图表说明](paper/README_figures.md)包含随附数据及 `plot_reset_figures.py` 的用法。在含 NumPy、Matplotlib 的 Python 环境中运行该脚本，即可从 CSV 重绘两幅图。

## 形式化证明

[定理映射](reset-theorem-map.md)对应两条渐近律、达到首项最优值时的稳态结构及显式达到构造。构建并审计：

```sh
cd lean
lake exe cache get
lake build TwoStateQuantumEmbedding QICLean
lake env lean ResetAudit.lean
```

Lean 固定为 `v4.35.0`，依赖由 manifest 固定。可设 `LEAN_NUM_THREADS=2` 限制并发。见[审计说明](verification/README.md)及[第三方声明](NOTICE.md)。
