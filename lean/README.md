# Lean proofs / Lean 证明

This shared library accompanies the latest reset paper and the earlier swap-endpoint paper. Exact statement coverage is listed in the [reset theorem map](../reset-theorem-map.md) and [swap theorem map](../theorem-map.md).

From this directory, run:

```sh
lake exe cache get
lake build TwoStateQuantumEmbedding QICLean
lake env lean ResetAudit.lean
lake env lean ../verification/PublicationAudit.lean
```

Set `LEAN_NUM_THREADS=2` for a memory-bounded build. Lean is `v4.35.0`; the manifest pins Mathlib to `56a005855ea17e0b0958f73ec801ae140b0a1679` and fixes its dependencies. Build caches are excluded.

`ResetAudit.lean` unfolds the two sharp reset laws to limits of the original maximum-gain functions and audits the laws, arbitrary-stationary-state saturation, and both displayed matching constructions. `PublicationAudit.lean` retains the earlier swap-paper audit. Principal results in both audits depend only on `propext`, `Classical.choice`, and `Quot.sound`.

[Verification evidence](../verification/README.md) separates the previous 9149-job public-package build from the recorded 9182-job integrated build containing the reset results. Preparing the updated package did not rerun these builds.

本库同时保留新重置论文与旧交换端点论文的证明。两份映射说明精确覆盖范围，两份审计分别检查相应主结果；库内辅助及条件性引理不自动构成论文主结论。

QICLean's 31 vendored modules retain upstream attribution and Apache-2.0 licensing. See [provenance and compatibility patch](vendor/QICLean/README.md).
