# Verification evidence / 验证证据

The checked declarations and their precise paper statements are listed in [theorem-map.md](../theorem-map.md).

From `lean/`, run:

```sh
lake build TwoStateQuantumEmbedding QICLean
lake env lean ../verification/PublicationAudit.lean
```

`PublicationAudit.lean` prints the types and transitive axiom dependencies of the principal results and semantic bridges. Only `propext`, `Classical.choice`, and `Quot.sound` are admitted in the release audit. The sources contain no `sorry`, `admit`, added axioms, or `native_decide` shortcuts.

The build uses Lean `v4.35.0` and the dependency revisions in `lean/lake-manifest.json`. `LEAN_NUM_THREADS=2` was used for the rebuild of the publication package. The dependency cache was reused; the project-specific and vendored QICLean modules were rebuilt in the publication directory. Build caches are not distributed.

The source is also reviewed for correspondence with the original fixed-basis, time-independent, single-qubit GKSL problem. In particular, the main theorems use the actual closure `Q2` and the actual slice minimum `lowerBoundary`; a candidate curve is not substituted into either definition.

论文与形式化声明的精确对应见[定理映射](../theorem-map.md)。公理审计检查主要结果及原始模型语义桥的传递依赖，仅允许三个标准基础公理。公开包重建使用固定版本的数学库缓存，并在公开目录重新编译项目自身与 QICLean 模块；缓存不随源码发布。

论文中的开放问题、后续方向及被明确列为未完成的研究不属于本次验证声明。定理表述和源代码的语义对应已经单独审阅，PDF 排版另行检查。

## This release / 本次结果

- [Build log](build.log): successful rebuild, 9149 jobs.
- [Axiom audit](PublicationAudit.log): 70 declarations, only the three standard axioms above.
- [Bilingual correspondence](bilingual-checks.json): matching mathematical content, labels, references, formal declaration names, and bibliography.
- Both PDFs have 20 pages; all 40 pages were visually inspected. The two source files compile without layout or reference warnings.
- [Machine-readable summary](results.json).
