# Reset-paper theorem map

This map accompanies *Sharp reset-error asymptotics for time-homogeneous qubit dynamics*, by Tingyu Zhang and Yan Cen: [English paper](paper/reset_manuscript.pdf), [Chinese paper](paper/reset_manuscript_zh.pdf), and [LaTeX source](paper/reset_manuscript.tex).

The model uses a fixed preparation–measurement basis and arbitrary finite collections of time-independent qubit GKSL jump operators, Hermitian Hamiltonians, and nonnegative times. For the output table `T(a,b) = [[a,1-b],[1-a,b]]`, the actual disturbance is `ε = 1-b` and the gain is `ε-a`. The two sharp laws optimize at fixed actual `ε` over the corresponding probability closures.

All declaration names below are under `TwoStateQuantumEmbedding`.

| Paper statement | Formal declaration and source | Coverage |
| --- | --- | --- |
| Theorem 1, `thm:main`: unrestricted `4/e` law | [`ResetFinal.reset_sharp_law`](lean/TwoStateQuantumEmbedding/ResetSharpLaws.lean) | The right limit of `log(1/ε) / ε * resetGain ε` is `4 / exp 1` for the original closure `Q2`. The theorem has no budget, comparison, uniform-envelope, or attainment hypothesis. |
| Theorem 2, `thm:diagonal`: diagonal-stationary `64/e²` law | [`ResetFinal.diagonal_reset_sharp_law`](lean/TwoStateQuantumEmbedding/ResetDiagonalActual.lean) | The right limit of `log(1/ε)^2 / ε * diagonalResetGain ε` is `64 / (exp 1)^2`. The class consists of generators admitting at least one measurement-basis diagonal stationary density matrix, and its probability closure. Transient coherence is retained. |
| Corollary `cor:saturation`: stationary spectral budget, coherence, and purity | [`ResetFinal.actual_stationary_saturation`](lean/TwoStateQuantumEmbedding/ResetSharpLaws.lean) | For every caller-specified sequence of stationary density matrices of a saturating finite-generator sequence, `ν/ε → 0`, `p/ε → 1`, stationary coherence squared divided by `ε` tends to `1`, and purity defect divided by `ε` tends to `0`. Stationarity is not required to be unique. |
| Displayed tilted pure-state single-jump construction, `sec:mechanisms` and `app:unrestricted-sharpness` | [`ResetDisplayedFamily.simple_output_exact`, `displayed_output_exact`, `displayed_pure_stationary`](lean/TwoStateQuantumEmbedding/ResetDisplayedFamily.lean); [`ResetDisplayedAsymptotics.displayed_finite_matching`](lean/TwoStateQuantumEmbedding/ResetDisplayedAsymptotics.lean) | The displayed `p,A,B` family has the stated exact finite output and pure stationary state. For every sufficiently small prescribed actual `ε`, a member of this same family gives a finite time-one output whose normalized gain approaches `4/e`. |
| Displayed diagonal mixed-stationary single-jump construction, `app:diagonal` | [Exact dynamics](lean/TwoStateQuantumEmbedding/ResetDiagonalFamily.lean); [`ResetDiagonalFamily.every_small_actual_error_unit`](lean/TwoStateQuantumEmbedding/ResetDiagonalAttainment.lean) | A Hermitian Hamiltonian, one jump, an actual diagonal generator-stationary density matrix, and a time-one output match every sufficiently small actual `ε` with normalized gain approaching `64/e²`. |
| Proposition `prop:envelope`: sharp uniform comparison envelope | [`ResetFinal.refined_envelope_exact`](lean/TwoStateQuantumEmbedding/ResetSharpLaws.lean), using [uniform envelope bounds](lean/TwoStateQuantumEmbedding/ResetEnvelopeUniform.lean) | The quantified comparison bound is proved uniformly in the envelope parameters and is connected to actual finite GKSL outputs through [actual upper bounds](lean/TwoStateQuantumEmbedding/ResetActualSharpBounds.lean). |

The definitions `ResetLaw`, `DiagonalResetLaw`, `resetGain`, and `diagonalResetGain` are in [ResetEndpoint.lean](lean/TwoStateQuantumEmbedding/ResetEndpoint.lean). In particular, `Qdiag` is the closure of actual finite outputs satisfying `HasDiagonalStationary`; it is not defined by an abstract comparison system. [ResetAudit.lean](lean/ResetAudit.lean) directly unfolds the two headline statements into limits of these original maximum-gain functions and prints the types and axiom dependencies of the five principal endpoints.

## Reproduction

Install [elan](https://github.com/leanprover/elan), then run from the repository root:

```sh
cd lean
lake exe cache get
lake build TwoStateQuantumEmbedding QICLean
lake env lean ResetAudit.lean
```

Lean is pinned to `v4.35.0`; [lake-manifest.json](lean/lake-manifest.json) fixes Mathlib and its dependencies. For a memory-bounded build, set `LEAN_NUM_THREADS=2` before the commands (`$env:LEAN_NUM_THREADS='2'` in PowerShell). The audit can also be run with `lake env lean -j 1 ResetAudit.lean`.

The [audit guide](verification/README.md) describes the checks and records the expected endpoint output. All five audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

The formal map covers the mathematical endpoints above. Literature priority, conversion to earlier parameterizations, the fixed-jump-norm interpretation, and the plotted numerical curves are assessed separately in the manuscript.
