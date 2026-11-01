# 两态量子嵌入

最新论文为 **《时间齐次量子比特动力学的尖锐重置误差渐近律》**，作者 **Tingyu Zhang、Yan Cen**，通讯作者 **Yan Cen**。

[中文论文](paper/reset_manuscript_zh.pdf) · [English paper](paper/reset_manuscript.pdf) · [重置定理映射](reset-theorem-map.md) · [English](README.md)

固定制备—测量基，记实际扰动 `ε = P(0|1)`、`a = P(0|0)`，并定义最大布居排序反转量 `G(ε) = max(ε-a)`。在全部时间无关量子比特 GKSL 生成元及其概率闭包上，尖锐渐近律为

$$G(\epsilon)\sim\frac{4}{e}\frac{\epsilon}{\log(1/\epsilon)}.$$

若生成元存在一个在制备—测量基中对角的稳态，则

$$G_{\mathrm{diag}}(\epsilon)\sim\frac{64}{e^2}\frac{\epsilon}{\log^2(1/\epsilon)}.$$

Lean 已覆盖两条规律、饱和序列的稳态相干与纯度约束，以及论文展示的两组单跳跃匹配构造。中英文稿正文均为七节，包含独立的**讨论**与**结论**；致谢、数据与代码可用性和声明保留统一占位，供作者核定。两版共用英文图注和 BibTeX 书目，见[作者校阅说明](paper/reset_author_review.md)。

## 此前的交换端点论文

**Sharp swap-endpoint geometry and an analytic boundary for two-state quantum embedding**，作者 **Tingyu Zhang**。

[中文论文](paper/manuscript_zh.pdf) · [English paper](paper/manuscript.pdf) · [交换端点定理映射](theorem-map.md)

该论文证明交换端点的精确切锥及真实下边界的局部实解析性。原论文、证明和审计均保留。有限误差下的精确重置边界、高阶渐近项及完整中段边界仍待解决，见[研究状态](research-status.md)。

## 验证证明

安装 [elan](https://github.com/leanprover/elan)。为限制构建并发，先设 `LEAN_NUM_THREADS=2`（PowerShell：`$env:LEAN_NUM_THREADS='2'`），然后运行：

```sh
cd lean
lake exe cache get
lake build TwoStateQuantumEmbedding QICLean
lake env lean ResetAudit.lean
lake env lean ../verification/PublicationAudit.lean
```

使用 Lean `v4.35.0`，Mathlib 及依赖版本固定在 `lean/lake-manifest.json`。主要结果的公理依赖仅为 `propext`、`Classical.choice` 和 `Quot.sound`。[验证记录](verification/README.md)分别说明此前 9149 项公开包构建，以及包含重置结果的已记录 9182 项整合构建。

## 编译重置论文

LaTeX 环境需包含 REVTeX 4.2、AMS 宏包、`ctex` 和 Fandol 字体。源码旁需保留 `reset_captions.tex`、`reset_references.bib` 及两幅 PDF 图。PRA 类自动选用 `apsrev4-2`，`longbibliography` 保留文献题名。

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

图表的既有数据、精度说明和便携重绘脚本见[图表说明](paper/README_figures.md)。

第三方 QICLean 源码保留原作者及 Apache-2.0 许可，详见[来源说明](lean/vendor/QICLean/README.md)与 [NOTICE.md](NOTICE.md)。
