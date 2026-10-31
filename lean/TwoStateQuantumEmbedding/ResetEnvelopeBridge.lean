import TwoStateQuantumEmbedding.ResetMixedEnvelope
import TwoStateQuantumEmbedding.ResetMetzlerKernel

noncomputable section
open Matrix
namespace TwoStateQuantumEmbedding.ResetEnvelope

/-- 正总体速率下的无量纲矩阵恒等式，直接使用真实 `sqrt(A B)`。 -/
theorem comparison_dimensionless (ν A B : ℝ) (hA : 0 < A) (hB : 0 ≤ B) :
    comparisonMatrix ν A B = A • ResetMetzler.matrix
      (rateA (chi ν)) (rateL (chi ν) (B / A))
      (rateR (chi ν) (B / A)) (rateC (chi ν) (B / A)) := by
  have hτ : 0 ≤ B / A := by positivity
  have hs : Real.sqrt (A * B) = A * Real.sqrt (B / A) := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt hτ]
    field_simp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [comparisonMatrix, ResetMetzler.matrix, alpha, lambda, up, down,
      rateA, rateL, rateR, rateC, hs]
  all_goals field_simp <;> ring

theorem metzler_gap_eq (x τ : ℝ) :
    ResetMetzler.gap (rateA x) (rateL x τ) (rateR x τ) (rateC x τ) = discriminant x τ := by
  unfold ResetMetzler.gap discriminant gap coupling
  ring_nf

theorem metzler_beta_eq (x τ : ℝ) :
    ResetMetzler.beta (rateA x) (rateL x τ) (rateR x τ) (rateC x τ) = beta x τ := by
  unfold ResetMetzler.beta beta
  rw [metzler_gap_eq]

theorem metzler_gamma_eq (x τ : ℝ) :
    ResetMetzler.gamma (rateA x) (rateL x τ) (rateR x τ) (rateC x τ) = gamma x τ := by
  unfold ResetMetzler.gamma gamma
  rw [metzler_gap_eq]

theorem metzler_weight_eq (p x τ : ℝ) :
    ResetMetzler.slowWeight (rateA x) (rateL x τ) (rateR x τ) (rateC x τ)
      (beta x τ) (gamma x τ) (tiltV p) (tiltW p) = slowWeight p x τ := by
  have hdiff : gamma x τ - beta x τ = discriminant x τ := by unfold gamma beta; ring
  unfold ResetMetzler.slowWeight slowWeight
  rw [hdiff]

/-- 真实比较矩阵指数的两率分解。 -/
theorem comparison_two_modes (p ν A B : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hA : 0 < A) (hB : 0 ≤ B) (hx : chi ν < 1) (hτ : B / A ≤ 1 / 2) :
    quadratic p (NormedSpace.exp (comparisonMatrix ν A B)) =
      slowWeight p (chi ν) (B / A) * Real.exp (-beta (chi ν) (B / A) * A) +
      (1 - slowWeight p (chi ν) (B / A)) * Real.exp (-gamma (chi ν) (B / A) * A) := by
  have hx0 : 0 ≤ chi ν := Real.sqrt_nonneg _
  have hh := coupling_nonneg (chi ν) (B / A) hx0 hx
  have hd : 0 < discriminant (chi ν) (B / A) :=
    lt_of_lt_of_le (by norm_num) (discriminant_low_ratio (chi ν) (B / A) hx0 hx hτ)
  rw [comparison_dimensionless ν A B hA hB]
  unfold quadratic
  have h := ResetMetzler.quadratic_two_modes (rateA (chi ν)) (rateL (chi ν) (B / A))
    (rateR (chi ν) (B / A)) (rateC (chi ν) (B / A)) (tiltV p) (tiltW p) A
    hh (by simpa only [metzler_gap_eq] using hd) (tilt_normalized p hp hp1)
  simpa only [metzler_beta_eq, metzler_gamma_eq, metzler_weight_eq] using h

theorem slow_weight_le_one (p x τ : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1 / 10000)
    (hx : 0 ≤ x) (hx1 : x ≤ 1 / 1000) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1 / 2) :
    slowWeight p x τ ≤ 1 := by
  have h := slow_weight_coarse p x τ hp (by linarith) hx (by linarith) hτ0 hτ1
  have hpτ : p * τ ≤ 1 / 10000 := by
    have hm := mul_le_mul hp1 hτ1 hτ0 (by norm_num : (0 : ℝ) ≤ 1 / 10000)
    linarith
  have hs : Real.sqrt (p * τ) ≤ 1 / 100 := by
    exact (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num; exact hpτ⟩
  have hxτ := mul_le_mul hx1 hτ1 hτ0 (by norm_num : (0 : ℝ) ≤ 1 / 1000)
  nlinarith

/-- 真实低比率包络接到163优化的正则化标量函数。 -/
theorem envelope_low_ratio_regularized (p ν A B ρ f : ℝ)
    (hp : 0 ≤ p) (hpρ : p ≤ ρ) (hρ : ρ ≤ 1 / 10000)
    (hx : chi ν ≤ 1 / 1000) (hA : 0 < A) (hB : 0 ≤ B)
    (hτ : B / A ≤ 1 / 2) (hf : 0 < f) :
    envelope p ν A B ≤ Reset.scalarEnvelope (1 - 8 * ρ)
      (slowWeight p (chi ν) (B / A) + f)
      (rateA (chi ν) / beta (chi ν) (B / A) - 1) := by
  have hx0 : 0 ≤ chi ν := Real.sqrt_nonneg _
  have hx1 : chi ν < 1 := by linarith
  have ht0 : 0 ≤ B / A := by positivity
  have hQ0 := slow_weight_nonneg p (chi ν) (B / A) hp (by linarith) hx0 hx1 hτ
  have hQ1 := slow_weight_le_one p (chi ν) (B / A) hp (by linarith) hx0 hx ht0 hτ
  have hb := beta_low_ratio_pos (chi ν) (B / A) hx0 (by linarith) ht0 hτ
  have hz := comparison_two_modes p ν A B hp (by linarith) hA hB hx1 hτ
  have hga : rateA (chi ν) ≤ gamma (chi ν) (B / A) := by
    have h := gamma_sub_a_nonneg (chi ν) (B / A)
      (coupling_nonneg (chi ν) (B / A) hx0 hx1)
    linarith
  have hnorm := tilt_normalized p hp (by linarith)
  have hw := tiltW_sq_le p hp (by linarith)
  have hP : 1 - 8 * ρ ≤ tiltV p ^ 2 - tiltW p ^ 2 + slowWeight p (chi ν) (B / A) := by
    linarith
  have h := two_modes_to_scalar (tiltV p ^ 2) (tiltW p ^ 2)
    (slowWeight p (chi ν) (B / A)) (rateA (chi ν)) (beta (chi ν) (B / A))
    (gamma (chi ν) (B / A)) A (quadratic p (NormedSpace.exp (comparisonMatrix ν A B)))
    hnorm hQ1 hga hA.le hz
  have heA : -alpha ν A = -rateA (chi ν) * A := by unfold alpha rateA; ring
  unfold envelope
  rw [heA]
  refine h.trans ((max_le_max ?_ (le_refl 0)).trans
    (two_rate_positive_bound (1 - 8 * ρ) (slowWeight p (chi ν) (B / A) + f)
      (rateA (chi ν)) (beta (chi ν) (B / A)) A (by linarith) (by linarith) hb.1 hb.2))
  have h1 := mul_le_mul_of_nonneg_right hP (Real.exp_nonneg (-rateA (chi ν) * A))
  have h2 := mul_nonneg hf.le (Real.exp_nonneg (-beta (chi ν) (B / A) * A))
  nlinarith

#print axioms comparison_dimensionless
#print axioms comparison_two_modes
#print axioms envelope_low_ratio_regularized
end TwoStateQuantumEmbedding.ResetEnvelope
