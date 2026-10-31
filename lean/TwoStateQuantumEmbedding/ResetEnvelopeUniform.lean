import TwoStateQuantumEmbedding.ResetEnvelopeLargeBridge
import TwoStateQuantumEmbedding.ResetLowRatio

noncomputable section
open Filter Topology Matrix
namespace TwoStateQuantumEmbedding.ResetEnvelope

/-- 一个共同阈值同时控制零速率、全部低比率及无界大比率。 -/
theorem envelope_log_scale_uniform (η : ℝ) (hη : 0 < η) :
    ∃ L₀ : ℝ, ∀ L p ν A B : ℝ, L₀ ≤ L →
      0 ≤ p → 0 ≤ ν → p + ν ≤ Real.exp (-L) → 0 ≤ A → 0 ≤ B →
      L * envelope p ν A B ≤ 4 * p / Real.exp 1 + η * Real.exp (-L) := by
  obtain ⟨Llow, hlow⟩ := low_ratio_regularized_uniform η hη
  obtain ⟨Llarge, hlarge⟩ := envelope_large_ratio_uniform η hη
  let L₀ : ℝ := max 1 (max Llow (max Llarge (Real.log 2000000)))
  refine ⟨L₀, ?_⟩
  intro L p ν A B hL hp hν hbudget hA hB
  have hL1 : 1 ≤ L := (le_max_left 1 _).trans hL
  have hLlow : Llow ≤ L := (le_max_left Llow _).trans ((le_max_right 1 _).trans hL)
  have hLlarge : Llarge ≤ L := (le_max_left Llarge _).trans
    ((le_max_right Llow _).trans ((le_max_right 1 _).trans hL))
  have hLlog : Real.log 2000000 ≤ L := (le_max_right Llarge _).trans
    ((le_max_right Llow _).trans ((le_max_right 1 _).trans hL))
  have hsmall : Real.exp (-L) ≤ 1 / 2000000 := by
    calc
      _ ≤ Real.exp (-Real.log 2000000) := Real.exp_le_exp.mpr (neg_le_neg hLlog)
      _ = _ := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2000000)]; norm_num
  have hpρ : p ≤ Real.exp (-L) := by linarith
  have hνρ : ν ≤ Real.exp (-L) := by linarith
  have hx0 : 0 ≤ chi ν := Real.sqrt_nonneg _
  have hxsq := chi_sq_budget ν (Real.exp (-L)) hν hνρ (by linarith)
  have hx : chi ν ≤ 1 / 1000 := by nlinarith
  have hxρ : chi ν ≤ 2 * Real.exp (-L / 2) := by
    have h := chi_le_budget ν (Real.exp (-L)) hν hνρ (by linarith)
    rwa [sqrt_exp_neg] at h
  by_cases hAz : A = 0
  · rw [hAz, envelope_zero_A p ν B hp (by linarith) hB, mul_zero]
    positivity
  have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
  by_cases hτ : B / A ≤ 1 / 2
  · have hbridge := envelope_low_ratio_regularized p ν A B (Real.exp (-L))
      (Real.exp (-3 * L / 4)) hp hpρ (by linarith) hx hAp hB hτ (Real.exp_pos _)
    exact (mul_le_mul_of_nonneg_left hbridge (by linarith : 0 ≤ L)).trans
      (hlow L hLlow p (chi ν) (B / A) hp hpρ hx0 hxρ (by positivity) hτ)
  · have h := hlarge L p ν A B hLlarge hp hpρ (by linarith) hx hxρ hAp hB (le_of_not_ge hτ)
    have hmain : 0 ≤ 4 * p / Real.exp 1 := by positivity
    linarith

/-- 真实四参数比较包络的精细统一有限阈值形式。 -/
theorem refined_envelope_uniform (η : ℝ) (hη : 0 < η) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ p ν A B : ℝ,
      0 < ρ → ρ < ρ₀ → 0 ≤ p → 0 ≤ ν → p + ν ≤ ρ → 0 ≤ A → 0 ≤ B →
      Real.log (1 / ρ) * envelope p ν A B ≤ 4 * p / Real.exp 1 + η * ρ := by
  obtain ⟨L₀, hL₀⟩ := envelope_log_scale_uniform η hη
  refine ⟨min (Real.exp (-L₀)) 1, lt_min (Real.exp_pos _) (by norm_num), ?_⟩
  intro ρ p ν A B hρ hρsmall hp hν hbudget hA hB
  have hbound : ρ ≤ Real.exp (-L₀) := hρsmall.le.trans (min_le_left _ _)
  have hlog := Real.log_le_log hρ hbound
  rw [Real.log_exp] at hlog
  have hL : L₀ ≤ Real.log (1 / ρ) := by
    simpa only [one_div, Real.log_inv, neg_neg] using neg_le_neg hlog
  have heρ : Real.exp (-Real.log (1 / ρ)) = ρ := by
    rw [one_div, Real.log_inv, neg_neg, Real.exp_log hρ]
  have h := hL₀ (Real.log (1 / ρ)) p ν A B hL hp hν (by rwa [heρ]) hA hB
  rwa [heρ] at h

#print axioms envelope_log_scale_uniform
#print axioms refined_envelope_uniform
end TwoStateQuantumEmbedding.ResetEnvelope
