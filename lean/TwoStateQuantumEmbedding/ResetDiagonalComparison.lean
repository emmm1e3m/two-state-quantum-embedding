import TwoStateQuantumEmbedding.ResetDiagonalEnvelope
import TwoStateQuantumEmbedding.ResetMetzlerKernel
import TwoStateQuantumEmbedding.ResetWeightedBarrier

noncomputable section
open Filter Topology
open scoped Matrix.Norms.Operator
namespace TwoStateQuantumEmbedding.ResetDiagonalEnvelope

theorem flow_eq_positivePopulation (z h r c x : ℝ) (hprod : r * c = h) (hh : 0 < h) :
    ResetComparison.comparisonFlow 1 r c z 1 0 x 0 = positivePopulation z h x := by
  have hgap : ResetMetzler.gap 1 z r c = spectralGap z h := by
    unfold ResetMetzler.gap spectralGap
    congr 1
    nlinarith
  have hgp : 0 < ResetMetzler.gap 1 z r c := by
    rw [hgap]
    unfold spectralGap
    apply Real.sqrt_pos.2
    positivity
  have hβ : ResetMetzler.beta 1 z r c = slowRate z h := by
    unfold ResetMetzler.beta slowRate
    rw [hgap]
  have hγ : ResetMetzler.gamma 1 z r c = fastRate z h := by
    unfold ResetMetzler.gamma fastRate
    rw [hgap]
  have hw : (ResetMetzler.gamma 1 z r c - 1) / ResetMetzler.gap 1 z r c = slowWeight z h := by
    rw [hγ, hgap]
    unfold fastRate slowWeight
    have hn : spectralGap z h ≠ 0 := by rw [← hgap]; exact ne_of_gt hgp
    field_simp
    <;> ring
  have hm : ResetComparison.comparisonMatrix 1 r c z = ResetMetzler.matrix 1 z r c := rfl
  have hflow : ResetComparison.comparisonFlow 1 r c z 1 0 x 0 =
      NormedSpace.exp (x • ResetMetzler.matrix 1 z r c) 0 0 := by
    simp [ResetComparison.comparisonFlow, hm, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [hflow, ResetMetzler.exp_entry00_two_modes 1 z r c x (by rw [hprod]; exact hh.le) hgp,
    hw, hβ, hγ]
  unfold positivePopulation
  ring

/-- 从真实正比较矩阵人口得到全速率比包络，重根区由加权屏障处理。 -/
theorem comparison_population_bound (χ τ r c x q : ℝ)
    (hχ : 0 < χ) (hχs : χ ≤ 1 / 100) (hτ : 0 < τ)
    (hr : 0 ≤ r) (hc : 0 ≤ c) (hprod : r * c = feedback χ τ) (hx : 0 ≤ x)
    (hq : 2 * Real.exp (-x) - ResetComparison.comparisonFlow 1 r c (zeta χ τ) 1 0 x 0 ≤ q) :
    max (-q) 0 ≤ diagonalEnvelope χ τ := by
  by_cases hτh : τ ≤ 1 / 2
  · obtain ⟨hzl, hzu, hhp, hhu⟩ := actual_parameter_bounds χ τ hχ hχs hτ hτh
    have hze : 0 < zeta χ τ := by linarith
    have hz1 : zeta χ τ < 1 := by linarith
    have hhz : feedback χ τ < zeta χ τ := by linarith
    rw [flow_eq_positivePopulation _ _ r c x hprod hhp] at hq
    rw [diagonalEnvelope, if_pos hτh]
    exact positive_population_scalar_bound q _ _ x hze hz1 hhp hhz hx hq
  · have hτlarge : 1 / 2 ≤ τ := le_of_lt (lt_of_not_ge hτh)
    obtain ⟨hz, hnorm⟩ := weightedFeedback_eq_normalized χ τ hχ hχs hτlarge
    obtain ⟨_, _, hη1, hη100⟩ := weightedFeedback_bound χ τ hχ hχs hτlarge
    have hη : ResetComparison.feedbackRatio 1 r c (zeta χ τ) (2 / 3) = weightedFeedback χ τ := by
      unfold ResetComparison.feedbackRatio
      rw [hprod]
      exact hnorm
    have hηlt : ResetComparison.feedbackRatio 1 r c (zeta χ τ) (2 / 3) < 1 := by
      rw [hη]
      exact hη1
    have hf := ResetComparison.weighted_population_feedback_unit 1 r c (zeta χ τ) (2 / 3)
      hr hc (by norm_num) hz hηlt hx
    rw [hη] at hf
    have hex : -(2 / 3 : ℝ) * x = -(2 * x / 3) := by ring
    norm_num only [neg_one_mul] at hf
    rw [hex] at hf
    have hmul := mul_le_mul_of_nonneg_right hη100 (Real.exp_nonneg (-(2 * x / 3)))
    have hpop : Real.exp (-x) - 100 * χ * Real.exp (-(2 * x / 3)) ≤ q := by
      linarith
    rw [diagonalEnvelope, if_neg hτh]
    exact large_ratio_scalar_bound χ x q hχ.le hpop

/-- 最终实际矩阵比较统一界：所有总体时间和速率比均在量词内。 -/
theorem diagonal_comparison_uniform (η : ℝ) (hη : 0 < η) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν < ν₀ →
      ∀ τ r c x q : ℝ, 0 < τ → 0 ≤ r → 0 ≤ c →
      r * c = feedback (Real.sqrt (ν / (1 - ν))) τ → 0 ≤ x →
      2 * Real.exp (-x) - ResetComparison.comparisonFlow 1 r c
        (zeta (Real.sqrt (ν / (1 - ν))) τ) 1 0 x 0 ≤ q →
      max (-q) 0 * (Real.log (1 / ν)) ^ 2 / ν ≤ 64 / (Real.exp 1) ^ 2 + η := by
  obtain ⟨ν₁, hν₁, hbound⟩ := diagonalEnvelope_nu_uniform η hη
  refine ⟨min ν₁ (1 / 1000000), by positivity, ?_⟩
  intro ν hν hνu τ r c x q hτ hr hc hprod hx hq
  have hνsmall := (lt_min_iff.mp hνu).2
  have hden : 0 < 1 - ν := by linarith
  have hχ : 0 < Real.sqrt (ν / (1 - ν)) := Real.sqrt_pos.2 (by positivity)
  have hχsq := Real.sq_sqrt (show 0 ≤ ν / (1 - ν) by positivity)
  have hχsqb : (Real.sqrt (ν / (1 - ν))) ^ 2 ≤ 1 / 10000 := by
    rw [hχsq]
    apply (div_le_iff₀ hden).2
    nlinarith
  have hχs : Real.sqrt (ν / (1 - ν)) ≤ 1 / 100 := by nlinarith
  have hp := comparison_population_bound _ τ r c x q hχ hχs hτ hr hc hprod hx hq
  have hm := mul_le_mul_of_nonneg_right hp
    (show 0 ≤ (Real.log (1 / ν)) ^ 2 / ν by positivity)
  have hm' : max (-q) 0 * (Real.log (1 / ν)) ^ 2 / ν ≤
      diagonalEnvelope (Real.sqrt (ν / (1 - ν))) τ * (Real.log (1 / ν)) ^ 2 / ν := by
    simpa only [mul_div_assoc] using hm
  exact hm'.trans (hbound ν hν (lt_min_iff.mp hνu).1 τ hτ)

#print axioms flow_eq_positivePopulation
#print axioms comparison_population_bound
#print axioms diagonal_comparison_uniform
end TwoStateQuantumEmbedding.ResetDiagonalEnvelope
