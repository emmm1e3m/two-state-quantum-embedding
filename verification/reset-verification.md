# Reset-paper verification evidence

The [reset theorem map](../reset-theorem-map.md) identifies the exact statements covered by the formal development. The earlier swap-paper audit and logs remain separate and unchanged.

The retained [integrated build log](reset-final-build.log) reports **9182 jobs completed successfully**, with recorded exit code `0`. The retained [audit log](reset-final-audit.log), also with recorded exit code `0`, comes from [ResetAudit.lean](../lean/ResetAudit.lean). It checks the unrestricted and diagonal-stationary gain limits, arbitrary-stationary-state saturation, and both displayed finite matching constructions. All five printed axiom dependencies consist only of `propext`, `Classical.choice`, and `Quot.sound`.

These are prior integrated-source verification records. Preparing this release checked the source inventory, exact equality of the 100 existing Lean source modules, unchanged pinned dependencies, and the complete 76-module local import closure of `ResetAudit`. The release adds 33 library modules and the audit file; its library entrypoint retains all earlier imports and adds `ResetSharpLaws`. This packaging pass did not perform a new kernel build or a new axiom audit. The machine-readable distinction is recorded in [reset-verification.json](reset-verification.json).

From `lean/`, reproduce the proof checks with:

```sh
lake exe cache get
lake build TwoStateQuantumEmbedding QICLean
lake env lean ResetAudit.lean
```

Use `LEAN_NUM_THREADS=2` to bound build concurrency. Lean is `v4.35.0`, and the Mathlib revision is `56a005855ea17e0b0958f73ec801ae140b0a1679`. Dependency caches and personal workspace paths are not distributed.
