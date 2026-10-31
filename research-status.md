# Research status / 研究状态

Snapshot: 31 October 2026 / 快照：2026 年 10 月 31 日

## Verified results

The latest [reset paper](paper/reset_manuscript.pdf), by Tingyu Zhang and Yan Cen (corresponding author), establishes the sharp unrestricted `4/e` and diagonal-stationary `64/e²` reset-gain laws. Both laws start from the original finite GKSL model and optimize at fixed actual disturbance over the probability closure. The complete Lean chain also covers the displayed single-jump matching constructions and the spectral, coherence, and purity constraints for any stationary-state sequence selected along a saturating finite-generator sequence. See the [reset theorem map](reset-theorem-map.md).

The [earlier swap-endpoint paper](paper/manuscript.pdf), by Tingyu Zhang, proves the exact tangent cone and local real analyticity of the actual lower boundary near swap, together with the supporting model, geometric, and finite-attainment results identified in its [theorem map](theorem-map.md). The earlier papers and proof development remain intact.

The reset papers in English and Chinese have seven main sections, including separate Discussion and Conclusions, with acknowledgment placeholders awaiting author completion. Recorded proof evidence is described in [verification/README.md](verification/README.md); the release-packaging work did not itself rerun either full build.

## Open questions

- The exact optimal reset boundary at finite, nonzero error; the plotted curves are attained constructions.
- Higher-order corrections to the sharp reset asymptotics and quantitative transition scales.
- The complete middle boundary of the two-state embedding region beyond the established endpoint results.

## 已验证范围与后续问题

最新[重置论文](paper/reset_manuscript_zh.pdf)署名 Tingyu Zhang、Yan Cen，Yan Cen 为通讯作者。原始有限 GKSL 模型下的两条尖锐重置规律、论文显示的两组达到构造，以及饱和序列任意稳态选择的谱、相干和纯度结构，均已接入完整 Lean 证明链。[旧交换端点论文](paper/manuscript_zh.pdf)及其真实局部解析边界证明继续保留。

重置上界及显示构造的形式化接合已完成。仍开放的是有限非零误差下的精确最优曲线、高阶渐近修正与定量过渡尺度，以及两个端点之外的完整中段边界。图中有限误差曲线展示具体可达到族，不代表完整最优边界。中英文重置稿包含七节正文、独立讨论与结论，以及待作者补充的致谢占位。
