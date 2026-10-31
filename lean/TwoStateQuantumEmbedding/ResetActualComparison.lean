import TwoStateQuantumEmbedding.ResetMixedAlgebra
import TwoStateQuantumEmbedding.ResetPositiveComparison

noncomputable section
open Matrix Complex
open scoped BigOperators Matrix.Norms.Operator ComplexOrder

namespace TwoStateQuantumEmbedding.ResetActual

open PureStationary ResetMixed

/-- 共同制备/测量在规范基中的真实差态。 -/
def initialDifference (p : ℝ) : QubitMatrix :=
  state 0 (1 - 2*p) (2*Real.sqrt (p*(1-p)))

theorem initialDifference_isHermitian (p : ℝ) : (initialDifference p).IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [initialDifference, state, Matrix.conjTranspose_apply]

theorem initialDifference_trace (p : ℝ) : (initialDifference p).trace = 0 := by
  simp [initialDifference, state, Matrix.trace, Fin.sum_univ_two]

/-- 所有频率、零速率和纯态端点统一进入真实正矩阵指数比较。 -/
theorem canonical_comparison {n : ℕ} (x y z : Fin n → ℂ) (ω ν p t : ℝ) (h : ℂ)
    (hs : gkslAction (hamiltonian ω h) (jumps x y z) (state 1 ν 0) = 0)
    (hν0 : 0 ≤ ν) (hν : ν < 1/2) (hp0 : 0 ≤ p) (hp : p ≤ 1/2) (ht : 0 ≤ t) :
    2 * (1-2*p)^2 * Real.exp (-alpha z (chi ν)*t) -
      dotProduct ![1-2*p, 2*Real.sqrt (p*(1-p))]
        (NormedSpace.exp (t • ResetComparison.comparisonMatrix
          (alpha z (chi ν)) (rBound x z (chi ν))
          (cBound x z (chi ν)) (lam x z (chi ν))) *ᵥ
          ![1-2*p, 2*Real.sqrt (p*(1-p))]) ≤
      (1-2*p) * population (hamiltonian ω h) (jumps x y z) (initialDifference p) t +
      2*Real.sqrt (p*(1-p)) *
        (coherence (hamiltonian ω h) (jumps x y z) (initialDifference p) t).re := by
  obtain ⟨hc0,hc1,_,_⟩ := chi_properties ν hν0 hν
  obtain ⟨hΓ,hC,hR⟩ := stationary_coefficient_bounds x y z ω ν h hs hν0 hν
  have hden : 0 < 1-chi ν := by linarith
  have hc : 0 ≤ cBound x z (chi ν) := by unfold cBound; positivity
  have hr : 0 ≤ rBound x z (chi ν) := by unfold rBound; positivity
  have hα : rate z + rate y = alpha z (chi ν) := by
    rw [stationary_scaled_U x y z ω ν h hs hν0 hν]
    unfold alpha
    ring
  apply ResetComparison.positive_comparison
    (alpha z (chi ν)) (rBound x z (chi ν)) (cBound x z (chi ν))
    (lam x z (chi ν)) (gamma x y z) ω (1-2*p) (2*Real.sqrt (p*(1-p)))
    (feedback x y z ν) (cTilde x y z ν) (coeffE y z)
    (by linarith) (by positivity) hr hc hR hC hΓ
  · intro s hs0
    simpa only [hα] using actual_population_hasDerivAt x y z ω ν h hs
      (by linarith : 1-2*ν ≠ 0) (initialDifference p)
      (initialDifference_isHermitian p) (initialDifference_trace p) s hs0
  · intro s hs0
    exact actual_coherence_hasDerivAt x y z ω ν h hs
      (by linarith : 1-2*ν ≠ 0) (initialDifference p)
      (initialDifference_isHermitian p) (initialDifference_trace p) s hs0
  · simp [population, actualState_zero, initialDifference, state]
  · simp [coherence, actualState_zero, initialDifference, state]
  · exact ht

#print axioms canonical_comparison

end TwoStateQuantumEmbedding.ResetActual
