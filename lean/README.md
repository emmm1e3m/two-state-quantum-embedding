# Lean proofs / Lean 证明

This is the checked source accompanying the English and Chinese manuscripts in `../paper/`. For the exact statement coverage, see [theorem-map.md](../theorem-map.md). The library includes supporting and conditional lemmas as well as the paper's main results; the latter are identified explicitly in the map and audit.

本目录为公开中英文论文所用的已验证源码。定理覆盖范围见[对应表](../theorem-map.md)；库中还保留辅助及条件性引理，论文主结果由映射表与公理审计明确列出。

```sh
lake exe cache get
lake build TwoStateQuantumEmbedding QICLean
lake env lean ../verification/PublicationAudit.lean
```

Lean `v4.35.0`; Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`, fixed by the manifest. Build caches are excluded from this repository.

QICLean's 31 source modules retain upstream attribution and Apache-2.0 licensing. See [provenance and compatibility patch](vendor/QICLean/README.md).
