# Publication theorem map

This map accompanies *Sharp swap-endpoint geometry and an analytic boundary for two-state quantum embedding*, by Tingyu Zhang. The paper is `paper/manuscript.tex`; formal sources are under `lean/TwoStateQuantumEmbedding/`. The Chinese paper has the same mathematical statements and labels.

The main model is the original finite GKSL matrix exponential, followed by preparation and measurement in the same computational basis. `Q2` is the closure of those finite outputs. `lowerBoundary` is its actual minimum first coordinate at fixed second coordinate. No replacement region or conditional boundary identity is used in the final analytic theorem.

Except where a different namespace is written explicitly, prefixes below are under `TwoStateQuantumEmbedding`.

| Paper label | Formal declaration(s) | Exact scope and connection |
|---|---|---|
| `eq:gksl`–`eq:Qdefinition` | `OriginalProblem.original_Q2_four_entry_iff`; `OriginalProblem.all_four_probabilities` | The two-coordinate output agrees with all four entries of the original stochastic table, with the original GKSL action and its exponential. |
| `eq:scalar-gauge`–`eq:xz-readout` | `CanonicalBloch.finiteOutput_eq_canonicalOutput`; `CanonicalBloch.realGeneralizedState_evolution`; `CanonicalBloch.exists_evolution_for_canonical`; `CanonicalBloch.finiteOutputs_eq_canonicalOutputs` | Both directions of the canonical Bloch representation are proved, including arbitrary original jump scalar parts, time rescaling, PSD Gram factorization, and actual exponential evolution. |
| `thm:drift-ellipsoid` | **`TwoState.GeneralGeometry.physicalCanonical_posSemidef_iff_ball`** | Actual canonical matrix `S + (i/4)[c]×`; all real PSD `S`, including singular matrices. This namespace is not `TwoStateQuantumEmbedding.GeneralGeometry`. |
| `prop:fixed-drift` | **`TwoState.GeneralGeometry.physicalCanonical_linear_image`**; **`TwoState.GeneralGeometry.physicalCanonical_max_attained`**; `OptimalDrift.explicit_endpoint_output` | Exact signed interval of linear bias at fixed real damping and Hamiltonian, with a realizable maximizing drift. |
| `prop:filling` | `CanonicalBias.Q2_antidiagonal_filling`; `CanonicalBias.Q2_swap` | Every bias contraction `η ∈ [-1,1]` at fixed `a+b` stays in the actual closed region. This is a generator construction, not an assumption of convexity of `Q2`. |
| `thm:envelope` | `Envelope.Q2_envelope_iff`; `Envelope.F_isGreatest`; `Envelope.F_upperSemicontinuousOn`; `Envelope.F_classical`; `Envelope.relaxed_variational_limit` | Closed filled sections; nonnegative envelope bounded by the diamond; upper semicontinuity; `F(x)=1-x` on `[0,1]`; neighborhood-relaxed variational limit. No global continuity or exact finite attainment at every negative `x` is asserted. |
| `lem:rigidity` | `Rigidity.canonicalOutput_dissipative_rigidity`; `Rigidity.finiteOutput_dissipative_rigidity` | Actual generators with `a+b ≤ 1/16` satisfy `tr K ≤ -log(1-4(a+b))/2 ≤ 8(a+b)/3`. No Hamiltonian bound is assumed. |
| `lem:uniform-swap` | `SwapComparison.canonical_near_swap_comparison_all_axes`; `SwapComparison.finite_near_swap_comparison` | Actual all-axis generators, normalized by the measurement-preserving azimuth gauge. Supplies the integer rotation number, the actual common unitary probability, angle/axis estimates, and actual errors bounded by `34 d sqrt(p)+8 d²`. |
| Exact integrals used in `lem:uniform-swap` and `lem:analytic-system` | `SwapComparison.firstOrderReturn_single_a`; `SwapComparison.firstOrderReturn_single_b` in `FirstOrderBridge.lean`; actual PSD extension and derivative bridges | Arbitrary complex jump vectors and arbitrary reference odd half-turns. These are integrals of the actual generator perturbation, not assumed quadratic forms. |
| `lem:spectrum` | **`Swap.all_frequency_sharp`**; **`Swap.higher_frequency_gap`**; **`Swap.first_frequency_gap`**; **`Swap.all_frequency_real_spectrum`** | Exact complex quadratic forms, true `Real.pi` and `Real.sqrt 2`, the first-frequency null direction, and a gap for every higher rotation number. `Swap` is a top-level namespace. |
| `lem:matching` | `SwapMatching.lowerBoundary_small_upper_strict`; matching-output and exact-ordinate lemmas in `SwapMatching.lean` | Legal traceless jumps `V₋ = -i sqrt(2) X/4 + Z/2` and `V₊ = V₋†`, fixed `H=πX/2`; actual remainder estimates and IVT give every sufficiently small second coordinate. No scalar-restored outer-product jump is used. |
| `thm:swap-cone` | `SwapCone.Q2_quadratic_outer`; `SwapCone.Q2_posTangentConeAt_zero` | Unconditional statements about original `Q2`: quadratic outer errors with constant 2600 for sum at most `1/256`; exact positive Bouligand tangent cone. The inner directions are actual finite two-jump constructions. |
| `lem:localization` | `NearSwap.canonical_near_localization`; `NearSwap.canonical_normalized_parameters_tendsto` | Uniform in arbitrary moving families of near minimizers with one fixed quadratic competitor constant. Includes exclusion of all higher rotation numbers, `p=O(b²)`, transverse noise `O(b²)`, and limits of normalized parameters. |
| `lem:attainment` | `SwapFiniteAttainment.exists_swapMinimizer`; `SwapFiniteAttainment.all_minimizers_localized` | Actual finite attainment for every positive `b` below a positive radius; closure approximants may have varying second coordinate. All minimizers are localized. The three-jump representation follows from the canonical Gram realization. |
| `lem:rank-one` | `SwapRankOne.eventually_rank_one_of_tendsto`; `SwapRankOne.multiplier_tendsto_slope`; `GlobalSwapArc.minimizing_rank_one_eventually` in `MinimizerCoordinates.lean` | The neighborhood rank-reduction theorem has explicit local-minimum and convergence inputs. `MinimizerCoordinates` supplies these inputs for arbitrary families of actual minimizers, discharging the localization and radial regularity requirements. Convergence to the fixed dual matrix is after azimuth normalization. |
| `eq:rank-one-chart`–`eq:chart-base` | `RankOneChart.lean`; `GlobalSwapArc.minimizing_parameters_tendsto`; `GlobalSwapArc.minimizing_scale_eventually_pos` | Full complex rank-one noise chart, including all four real direction variables; actual chart scale is positive eventually and converges to zero. `rank K=1` is not the claim `rank V=1` for a traceless 2×2 jump. |
| Actual stationarity needed for `thm:analytic-boundary` | `ActualSwapOptimality.stationarity_chart_of_lowerBoundary`; `GlobalSwapArc.minimizing_stationarity_eventually` | The actual lower-boundary minimum gives all seven equations for `G`; the third row is the dissipative-scale derivative, not the derivative in the Lagrange multiplier. |
| `lem:analytic-system` | `ActualSwapSystem.actual_analytic_stationary_branch`; `ActualSwapSystem.actual_stationary_arc_reparameterized` | Actual analytic system with the divided direction equations extended at zero; nonsingular full seven-variable derivative; fixed-neighborhood uniqueness; actual second-probability derivative `β*>0`; analytic local inverse with both scalar inverse identities. |
| `thm:analytic-boundary` | **`GlobalSwapArc.lowerBoundary_analytic_near_swap`** | Unconditional endpoint: there exist `farc : ℝ → ℝ` and `b0>0`, with `AnalyticOnNhd ℝ farc (Ioo (-b0) b0)` and `∀ b∈Ico 0 b0, farc b=lowerBoundary b`. The actual finite-minimizer, rank-one, stationarity, uniqueness, and inverse bridges are all inside the proved dependency chain. |
| `prop:planarity` | `ActualSwapSystem.unique_stationary_branch_eventually_planar`; `ActualSwapSystem.actual_planar_analytic_stationary_branch` | Exact reflection covariance of the actual system plus local uniqueness makes coordinates `h,ξ,ζ` zero. Combined with the preceding actual boundary identification, positive-small-`b` realizations have `H=ωX/2`, `V=√k(ivX+qY-Z)`. The invariant plane follows immediately by substituting these coordinates in the actual augmented generator. No physical positive-scale claim is made for negative `b` in the analytic extension. |
| `thm:reset` | **`ResetFamily.reset_every_small_epsilon_uniform`**, declared in `ResetUniform.lean`; `ResetFamily.actual_unit_curve_output` | For every sufficiently small prescribed `ε>0`, one actual zero-Hamiltonian, time-one, rank-one 2×2 jump realizes `(a,1-ε)`, with `0<a<ε` and one uniform `C loglog(1/ε)/log²(1/ε)` error. Actual jump is `√T U_r [[-m,0],[n,0]] U_r†`, with the real rotation shown in the paper. The file name `ResetUniform` is not the theorem's namespace. |
| `thm:square-roots` | **`TwoStateRoots.rootLayer_two_eq_square`** | Actual CPTP channels, composed twice with themselves, realize the entire stochastic square. No claim about the complete higher-root hierarchy is made. |

## Verification contract

The listed endpoints have a successful kernel build in Lean/mathlib `v4.35.0`. Their axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`; there is no `sorryAx` or additional mathematical axiom. The semantic channel foundation is vendored QICLean at the revision identified in the paper, with license and the version-compatibility patch retained.

From the public package root:

```text
cd lean
lake exe cache get
lake build TwoStateQuantumEmbedding QICLean
lake env lean ../verification/PublicationAudit.lean
```

The readable proofs sometimes combine several formal declarations in one lemma. In particular, rank reduction for actual minimizers and the physical interpretation of branch planarity are combinations of the explicitly listed bridges; a conditional neighborhood theorem is never presented as an unconditional global endpoint on its own.

## Deliberately absent claims

This publication does not assert a formally checked second-order curvature coefficient for the true swap boundary, an explicit numerical analytic radius, a universal pure-steady-state reset upper bound, finite realization at every negative envelope coordinate, global envelope continuity, or a complete strict hierarchy of channel-root regions. It also does not relabel the matching family's slope limit as a separately exported theorem about `f'(0)`. The exact slope information is stated through the proved tangent cone and the actual upper/outer bounds.
