import TwoStateQuantumEmbedding.ResetEnvelopeBridge
import TwoStateQuantumEmbedding.ResetLargeEnvelope
import TwoStateQuantumEmbedding.ResetWeightedBarrier

noncomputable section
open Filter Topology Matrix
namespace TwoStateQuantumEmbedding.ResetEnvelope

theorem weighted_coefficient_eq (p x τ : ℝ) :
    tiltV p * ResetComparison.populationFeedbackWeight (rateA x) (rateR x τ)
        (rateC x τ) (rateL x τ) (3 / 5) (tiltV p) (tiltW p) + tiltW p ^ 2 +
      tiltW p * ResetComparison.coherenceWeight (rateA x) (rateR x τ)
        (rateC x τ) (rateL x τ) (3 / 5) (tiltV p) (tiltW p) = largeCoefficient p x τ := by
  unfold ResetComparison.populationFeedbackWeight ResetComparison.coherenceWeight
    ResetComparison.populationWeight ResetComparison.feedbackRatio
    largeCoefficient barrierSize initialTransfer feedbackRatio coupling
  ring

/-- 加权正上解直接作用于真实比较矩阵，统一覆盖全部大比率。 -/
theorem envelope_large_ratio_bound (p ν A B ρ : ℝ) (hp : 0 ≤ p) (hpρ : p ≤ ρ)
    (hρ : ρ ≤ 1 / 8) (hx : chi ν ≤ 1 / 1000)
    (hxρ : chi ν ≤ 2 * Real.sqrt ρ) (hA : 0 < A) (hB : 0 ≤ B)
    (hτ : 1 / 2 ≤ B / A) :
    envelope p ν A B ≤
      max (512 * Real.sqrt ρ * Real.exp (-(3 / 5) * A) -
        (1 / 2) * Real.exp (-rateA (chi ν) * A)) 0 := by
  have hx0 : 0 ≤ chi ν := Real.sqrt_nonneg _
  have hx1 : chi ν < 1 := by linarith
  have hr : 0 ≤ rateR (chi ν) (B / A) := by unfold rateR; positivity
  have hc : 0 ≤ rateC (chi ν) (B / A) := by unfold rateC; positivity
  have hv : 0 ≤ tiltV p := by unfold tiltV; linarith
  have hw : 0 ≤ tiltW p := by unfold tiltW; positivity
  have hgap := large_rate_gaps (chi ν) (B / A) hx0 hx hτ
  have hrat := large_rate_ratios (chi ν) (B / A) hx0 hx hτ
  have hη : ResetComparison.feedbackRatio (rateA (chi ν)) (rateR (chi ν) (B / A))
      (rateC (chi ν) (B / A)) (rateL (chi ν) (B / A)) (3 / 5) < 1 := by
    change feedbackRatio (chi ν) (B / A) < 1
    linarith [hrat.2.1]
  have h := ResetComparison.weighted_quadratic_bound (rateA (chi ν)) (rateR (chi ν) (B / A))
    (rateC (chi ν) (B / A)) (rateL (chi ν) (B / A)) (3 / 5) (tiltV p) (tiltW p)
    hr hc hv hw (by linarith [hgap.1]) (by linarith [hgap.2]) hη hA.le
  rw [weighted_coefficient_eq] at h
  have hM : comparisonMatrix ν A B = A • ResetComparison.comparisonMatrix
      (rateA (chi ν)) (rateR (chi ν) (B / A))
      (rateC (chi ν) (B / A)) (rateL (chi ν) (B / A)) := by
    simpa only [ResetMetzler.matrix, ResetComparison.comparisonMatrix] using
      comparison_dimensionless ν A B hA hB
  have heA : -alpha ν A = -rateA (chi ν) * A := by unfold alpha rateA; ring
  have hcoeff := large_coefficient_bound p (chi ν) (B / A) ρ hp hpρ hρ hx0 hx hxρ hτ
  have hvhalf : (1 / 2 : ℝ) ≤ tiltV p ^ 2 := by
    unfold tiltV
    have hvp : 3 / 4 ≤ 1 - 2 * p := by linarith
    nlinarith
  have he1 := mul_le_mul_of_nonneg_right hcoeff (Real.exp_nonneg (-(3 / 5) * A))
  have he2 := mul_le_mul_of_nonneg_right hvhalf (Real.exp_nonneg (-rateA (chi ν) * A))
  unfold envelope quadratic
  rw [hM, heA]
  apply max_le_max _ (le_refl 0)
  nlinarith

theorem sqrt_exp_neg (L : ℝ) : Real.sqrt (Real.exp (-L)) = Real.exp (-L / 2) := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (Real.exp_nonneg _)).mp
  rw [Real.sq_sqrt (Real.exp_nonneg _), pow_two, ← Real.exp_add]
  congr 1
  ring

/-- 大比率真实包络的统一有限阈值低阶界。 -/
theorem envelope_large_ratio_uniform (η : ℝ) (hη : 0 < η) :
    ∃ L₀ : ℝ, ∀ L p ν A B : ℝ, L₀ ≤ L →
      0 ≤ p → p ≤ Real.exp (-L) → Real.exp (-L) ≤ 1 / 8 →
      chi ν ≤ 1 / 1000 → chi ν ≤ 2 * Real.exp (-L / 2) →
      0 < A → 0 ≤ B → 1 / 2 ≤ B / A →
      L * envelope p ν A B ≤ η * Real.exp (-L) := by
  obtain ⟨L₀, hL₀⟩ := large_ratio_scalar_uniform η hη
  refine ⟨max 0 L₀, ?_⟩
  intro L p ν A B hL hp hpρ hρ hx hxρ hA hB hτ
  have hL0 : 0 ≤ L := (le_max_left 0 L₀).trans hL
  have hbig := envelope_large_ratio_bound p ν A B (Real.exp (-L)) hp hpρ hρ hx
    (by rwa [sqrt_exp_neg]) hA hB hτ
  rw [sqrt_exp_neg] at hbig
  have ha : 1 ≤ rateA (chi ν) := by unfold rateA; nlinarith [sq_nonneg (chi ν)]
  have hx0 : 0 ≤ chi ν := Real.sqrt_nonneg _
  have ha1 : rateA (chi ν) ≤ 101 / 100 := by
    unfold rateA
    nlinarith [mul_nonneg hx0 (show 0 ≤ 1 / 1000 - chi ν by linarith)]
  exact (mul_le_mul_of_nonneg_left hbig hL0).trans
    (hL₀ L (rateA (chi ν)) A ((le_max_right 0 L₀).trans hL) ha ha1)


#print axioms envelope_large_ratio_bound
#print axioms envelope_large_ratio_uniform
end TwoStateQuantumEmbedding.ResetEnvelope
