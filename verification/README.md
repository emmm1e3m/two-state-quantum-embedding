# Verification evidence / 验证证据

The [reset theorem map](../reset-theorem-map.md) and [swap theorem map](../theorem-map.md) specify which mathematical statements the two papers share with the Lean development.

| Recorded evidence | Build | Audit |
| --- | --- | --- |
| Earlier swap-paper public package | [9149 jobs, exit 0](build.log) | [70 declarations](PublicationAudit.log), checked by [PublicationAudit.lean](PublicationAudit.lean) |
| Integrated source project including the reset results | [9182 jobs, exit 0](reset-final-build.log) | [Five principal endpoints](reset-final-audit.log), checked by [ResetAudit.lean](../lean/ResetAudit.lean) |

Both recorded audits use only `propext`, `Classical.choice`, and `Quot.sound`. The reset audit directly unfolds both sharp laws to limits of the original closed-region gain functions; it also checks arbitrary-stationary-state saturation and the two displayed matching constructions.

These logs record separate completed builds. Preparing the updated release checked the source inventory and dependency closure; it did **not** rerun either full build. The earlier [results.json](results.json) and [bilingual checks](bilingual-checks.json) describe the swap-paper release. The reset evidence has its own [verification note](reset-verification.md) and [machine-readable summary](reset-verification.json).

To reproduce both proof audits from `lean/`:

```sh
lake exe cache get
lake build TwoStateQuantumEmbedding QICLean
lake env lean ResetAudit.lean
lake env lean ../verification/PublicationAudit.lean
```

Use Lean `v4.35.0` and the fixed `lake-manifest.json`; set `LEAN_NUM_THREADS=2` to bound concurrency. Paper layout, literature discussion, and plotted numerical curves are separate from the Lean endpoint certificates.

旧 9149 项日志来自交换端点公开包的重建；新 9182 项日志来自已完成的重置成果整合工程构建。本轮仅整理公开包，未重新执行这两次构建。旧 JSON 与双语检查继续描述旧论文，新重置证据单独保存，避免混用验证范围。
