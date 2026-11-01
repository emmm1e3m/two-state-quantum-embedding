# Lean proofs

This library accompanies *Sharp reset-error asymptotics for time-homogeneous qubit dynamics*. The [theorem map](../reset-theorem-map.md) lists the exact statement coverage.

From this directory:

```sh
lake exe cache get
lake build TwoStateQuantumEmbedding QICLean
lake env lean ResetAudit.lean
```

Lean is `v4.35.0`, and `lake-manifest.json` fixes Mathlib and its dependencies. Set `LEAN_NUM_THREADS=2` to limit build concurrency.

`TwoStateQuantumEmbedding.lean` imports the final reset theorem module. The accompanying source modules are its transitive dependencies. `ResetAudit.lean` checks the two gain limits, arbitrary-stationary-state saturation, and both displayed matching constructions. The five audited endpoints use only `propext`, `Classical.choice`, and `Quot.sound`.

The vendored QICLean foundations retain their upstream attribution and Apache-2.0 license. See [provenance](vendor/QICLean/README.md) and [notices](../NOTICE.md).
