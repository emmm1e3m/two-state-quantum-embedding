# 作者校阅说明

本论文研究固定实际扰动下，时间无关量子比特动力学所能产生的最大布居排序反转。主线是两条尖锐渐近律、对应的相干机制，以及达到不受限首项最优值所需的稳态结构。题目已明确“渐近”范围；讨论解释物理意义与已有工作的关系，结论集中回答这一问题。

中英文共享英文图注、两幅图和参考文献库。图1以圆形和方形标记区分构造，图2改为上下两面板，以保持单栏尺寸下的可读性。技术附录补充其与正文的联系，保留原有论证。

## 作者待填

两版均在结论后保留以下可检索占位符：

- `[ACKNOWLEDGMENTS AND FUNDING TO BE COMPLETED]`：致谢与资助。
- `[DATA AND CODE AVAILABILITY TO BE CONFIRMED]`：核定公开数据、代码的范围及正式声明。
- `[DECLARATIONS TO BE CONFIRMED]`：核定适用的期刊披露声明及最终位置；参见 [PRA 作者指南](https://journals.aps.org/pra/authors)及 [APS 披露要求](https://journals.aps.org/authors/appropriate-use-ai-tools)。

此次文字整理未发现需要改变科学结论的明确矛盾。上述占位符需在正式投稿前由作者补全。

## 实际检查

两版均已实际编译并逐页检查：英文12页、中文11页。原有显示公式及六个定理类陈述保持不变，133个标签保留，107个带标签公式与双语编号一致。五条文献由同一 BibTeX 库生成，保留题名与 DOI 链接；无未定义引用、缺失字形或越栏内容。图表数据沿用既有计算，只调整呈现。此次未重新运行 Lean 构建。

## 重建论文

需要含 REVTeX 4.2、AMS 宏包、`ctex` 和 Fandol 字体的 TeX 环境。将两份 `.tex`、`reset_captions.tex`、`reset_references.bib` 及两幅 PDF 图放在同一目录，运行：

```sh
pdflatex -interaction=nonstopmode -halt-on-error reset_manuscript.tex
bibtex reset_manuscript
pdflatex -interaction=nonstopmode -halt-on-error reset_manuscript.tex
pdflatex -interaction=nonstopmode -halt-on-error reset_manuscript.tex
xelatex -interaction=nonstopmode -halt-on-error reset_manuscript_zh.tex
bibtex reset_manuscript_zh
xelatex -interaction=nonstopmode -halt-on-error reset_manuscript_zh.tex
xelatex -interaction=nonstopmode -halt-on-error reset_manuscript_zh.tex
```

`pra` 文档类自动选择 `apsrev4-2`，`longbibliography` 保留文献题名。若首次编译仍提示标签变化，再运行一次对应引擎。

图表的已有数据、数值精度及重绘方法见 [图表说明](README_figures.md)。运行 `python plot_reset_figures.py` 可从随附 CSV 重绘两幅图，无需运行 Lean。
