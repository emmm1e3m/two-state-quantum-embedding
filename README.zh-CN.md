# 两态量子嵌入

**Tingyu Zhang**

[中文论文](paper/manuscript_zh.pdf) · [英文论文](paper/manuscript.pdf) · [English](README.md) · [定理与代码对应表](theorem-map.md)

本仓库研究固定制备、测量基下，由时间不变的量子比特 GKSL 生成元产生的两态概率表。主要结果是完全交换端点的精确切锥，以及该端点附近真实下边界的实解析性。Lean 证明从任意有限组跳跃算符和原始概率可达集的闭包定义出发。

论文还包含精确漂移几何与偏置区间、重置端点的对数阶合法构造，以及量子通道平方根层。公开稿的结论与已经核验的 Lean 声明逐项对应，见[定理映射](theorem-map.md)。完整中段边界仍然开放。

## 文件

- `paper/`：完整中英文论文，含 PDF 和 LaTeX 源文件。
- `lean/`：形式化源码、固定版本的依赖清单和 QICLean 基础库切片。
- `verification/`：主定理公理审计及构建证据。
- [研究状态](research-status.md)：本次公开范围及后续工作入口。

## 验证证明

安装 [elan](https://github.com/leanprover/elan)。为限制构建并发，先设 `LEAN_NUM_THREADS=2`（PowerShell：`$env:LEAN_NUM_THREADS='2'`），然后运行：

```sh
cd lean
lake exe cache get
lake build TwoStateQuantumEmbedding QICLean
lake env lean ../verification/PublicationAudit.lean
```

使用 Lean `v4.35.0`，Mathlib 的精确提交固定在 `lake-manifest.json`。公开主定理的公理审计只允许 `propext`、`Classical.choice` 和 `Quot.sound`。定理对应表同时说明形式化声明的数学含义与适用范围。

## 编译论文

LaTeX 环境需包含 `ctex`、Fandol 字体及通常的 AMS 宏包：

```sh
cd paper
latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex
latexmk -xelatex -interaction=nonstopmode -halt-on-error manuscript_zh.tex
```

## 署名与来源

论文及项目专用证明署名 Tingyu Zhang。第三方 QICLean 源文件保留原作者和 Apache-2.0 许可，详见[来源说明](lean/vendor/QICLean/README.md)及 [NOTICE.md](NOTICE.md)。
