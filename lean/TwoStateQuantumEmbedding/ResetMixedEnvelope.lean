import TwoStateQuantumEmbedding.ResetMixedEnvelopeDefs
import TwoStateQuantumEmbedding.ResetCore
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# 任务150：真实混合包络的标量化

仅个人目录中的工作模块。`envelope` 使用真实矩阵指数；以下精确标量引理不把
尚待建立的参数误差界假定为最终结论。
-/

noncomputable section
open Filter Topology Matrix

namespace TwoStateQuantumEmbedding.ResetEnvelope

/-- 倾角的真实平方模归一化。 -/
theorem tilt_normalized (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    tiltV p ^ 2 + tiltW p ^ 2 = 1 := by
  have hs := Real.sq_sqrt (show 0 ≤ p * (1 - p) by positivity)
  dsimp [tiltV, tiltW]
  nlinarith

theorem tiltW_sq_le (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    tiltW p ^ 2 ≤ 4 * p := by
  have hs := Real.sq_sqrt (show 0 ≤ p * (1 - p) by positivity)
  dsimp [tiltW]
  nlinarith [sq_nonneg p]

/-- 正部保留的双指数极值；总体速率 `s` 没有上界假设。 -/
theorem two_rate_positive_bound (P Q a b s : ℝ)
    (hP : 0 < P) (hQ : 0 < Q) (hb : 0 < b) (hba : b < a) :
    max (Q * Real.exp (-b * s) - P * Real.exp (-a * s)) 0 ≤
      Reset.scalarEnvelope P Q (a / b - 1) := by
  have hk : 0 < a / b - 1 := by
    have : 1 < a / b := (lt_div_iff₀ hb).2 (by simpa)
    linarith
  have hexp : Real.exp (-b * s) ^ (1 + (a / b - 1)) = Real.exp (-a * s) := by
    rw [← Real.exp_mul]
    congr 1
    field_simp
    ring
  have h := Reset.scalar_envelope_bound P Q (a / b - 1) (Real.exp (-b * s))
    hP hQ hk (Real.exp_nonneg _)
  rw [hexp] at h
  apply max_le h
  unfold Reset.scalarEnvelope
  positivity

/-- `Q=0` 不需要实幂的严格正底数条件。 -/
theorem two_rate_zero_weight (P a s : ℝ) (hP : 0 ≤ P) :
    max (0 * Real.exp (-s) - P * Real.exp (-a * s)) 0 = 0 := by
  simp only [zero_mul, zero_sub]
  exact max_eq_right (neg_nonpos.mpr (mul_nonneg hP (Real.exp_nonneg _)))

/-- 从真实两模分解到标量问题，慢模之外的快模只用单调指数。 -/
theorem two_modes_to_scalar (V W Q a b g s z : ℝ)
    (hVW : V + W = 1) (hQ : Q ≤ 1) (hga : a ≤ g) (hs : 0 ≤ s)
    (hz : z = Q * Real.exp (-b * s) + (1 - Q) * Real.exp (-g * s)) :
    max (z - 2 * V * Real.exp (-a * s)) 0 ≤
      max (Q * Real.exp (-b * s) - (V - W + Q) * Real.exp (-a * s)) 0 := by
  have he : Real.exp (-g * s) ≤ Real.exp (-a * s) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hga hs]
  have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ 1 - Q by linarith)
  apply max_le_max _ (le_refl 0)
  rw [hz]
  have hnorm := congrArg (fun t : ℝ => t * Real.exp (-a * s)) hVW
  nlinarith

/-- 两模标量化加全局最大值，仍对所有非负总体速率成立。 -/
theorem two_modes_positive_bound (V W Q a b g s z : ℝ)
    (hVW : V + W = 1) (hQ0 : 0 < Q) (hQ1 : Q ≤ 1)
    (hP : 0 < V - W + Q) (hb : 0 < b) (hba : b < a)
    (hga : a ≤ g) (hs : 0 ≤ s)
    (hz : z = Q * Real.exp (-b * s) + (1 - Q) * Real.exp (-g * s)) :
    max (z - 2 * V * Real.exp (-a * s)) 0 ≤
      Reset.scalarEnvelope (V - W + Q) Q (a / b - 1) :=
  (two_modes_to_scalar V W Q a b g s z hVW hQ1 hga hs hz).trans
    (two_rate_positive_bound (V - W + Q) Q a b s hP hQ0 hb hba)

theorem gap_exact (x τ : ℝ) : gap x τ = ((1 + x) ^ 2 - τ) / 2 := by
  dsimp [gap, rateA, rateL]
  ring

theorem gap_low_ratio (x τ : ℝ) (hx : 0 ≤ x) (hτ : τ ≤ 1 / 2) :
    1 / 4 ≤ gap x τ := by
  rw [gap_exact]
  nlinarith [sq_nonneg x]

theorem coupling_nonneg (x τ : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) :
    0 ≤ coupling x τ := by
  unfold coupling rateR rateC
  positivity

theorem discriminant_ge_gap (x τ : ℝ) (hh : 0 ≤ coupling x τ) :
    gap x τ ≤ discriminant x τ := by
  unfold discriminant
  exact (le_abs_self _).trans
    (by simpa only [Real.sqrt_sq_eq_abs] using
      Real.sqrt_le_sqrt (show gap x τ ^ 2 ≤ gap x τ ^ 2 + 4 * coupling x τ by linarith))

/-- 低比率区的谱间隔严格远离零。 -/
theorem discriminant_low_ratio (x τ : ℝ) (hx : 0 ≤ x) (hx1 : x < 1)
    (hτ : τ ≤ 1 / 2) : 1 / 4 ≤ discriminant x τ :=
  (gap_low_ratio x τ hx hτ).trans
    (discriminant_ge_gap x τ (coupling_nonneg x τ hx hx1))

theorem gamma_sub_a_nonneg (x τ : ℝ) (hh : 0 ≤ coupling x τ) :
    0 ≤ gamma x τ - rateA x := by
  have h := discriminant_ge_gap x τ hh
  dsimp [gamma, gap] at *
  linarith

theorem spectral_product (x τ : ℝ) (hh : 0 ≤ coupling x τ) :
    (gamma x τ - rateA x) * (discriminant x τ + gap x τ) / 2 = coupling x τ := by
  have hs := Real.sq_sqrt (show 0 ≤ gap x τ ^ 2 + 4 * coupling x τ by positivity)
  change discriminant x τ ^ 2 = gap x τ ^ 2 + 4 * coupling x τ at hs
  dsimp [gamma, gap] at *
  nlinarith

/-- 本征值偏移的除法估计，不假设偏移误差界。 -/
theorem gamma_shift_le (x τ : ℝ) (hg : 0 < gap x τ) (hh : 0 ≤ coupling x τ) :
    gamma x τ - rateA x ≤ coupling x τ / gap x τ := by
  have hd := discriminant_ge_gap x τ hh
  have hz := gamma_sub_a_nonneg x τ hh
  have he := spectral_product x τ hh
  apply (le_div_iff₀ hg).2
  nlinarith [mul_nonneg hz (sub_nonneg.mpr hd)]

theorem tilt_product_bounds (p : ℝ) (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2) :
    0 ≤ tiltV p * tiltW p ∧ tiltV p * tiltW p ≤ 2 * Real.sqrt p := by
  have hp1 : p ≤ 1 := by linarith
  have hv0 : 0 ≤ tiltV p := by unfold tiltV; linarith
  have hv1 : tiltV p ≤ 1 := by unfold tiltV; linarith
  have hw0 : 0 ≤ tiltW p := by unfold tiltW; positivity
  have hw : tiltW p ≤ 2 * Real.sqrt p := by
    unfold tiltW
    have h : p * (1 - p) ≤ p := by nlinarith [sq_nonneg p]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h) (by norm_num)
  exact ⟨mul_nonneg hv0 hw0, (mul_le_mul_of_nonneg_right hv1 hw0).trans (by simpa using hw)⟩

theorem rates_sum_nonneg (x τ : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) :
    0 ≤ rateR x τ + rateC x τ := by
  unfold rateR rateC
  positivity

/-- `Q` 的重排是恒等式，使用真实倾角归一化。 -/
theorem slow_weight_rearrange (p x τ : ℝ)
    (hd : discriminant x τ ≠ 0) :
    slowWeight p x τ = tiltW p ^ 2 +
      ((gamma x τ - rateA x) * (tiltV p ^ 2 - tiltW p ^ 2) +
        (rateR x τ + rateC x τ) * (tiltV p * tiltW p)) / discriminant x τ := by
  unfold slowWeight
  apply (div_eq_iff hd).2
  field_simp
  unfold gamma
  ring

/-- 131-(7) 的第一层真实参数界，未以慢模误差估计作前提。 -/
theorem slow_weight_bound (p x τ : ℝ) (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2)
    (hx : 0 ≤ x) (hx1 : x < 1) (hτ : τ ≤ 1 / 2) :
    slowWeight p x τ ≤ 4 * p + coupling x τ / gap x τ ^ 2 +
      2 * Real.sqrt p * (rateR x τ + rateC x τ) / gap x τ := by
  have hg : 0 < gap x τ := lt_of_lt_of_le (by norm_num) (gap_low_ratio x τ hx hτ)
  have hh := coupling_nonneg x τ hx hx1
  have hdg := discriminant_ge_gap x τ hh
  have hd : 0 < discriminant x τ := hg.trans_le hdg
  have hz := gamma_sub_a_nonneg x τ hh
  have hshift := gamma_shift_le x τ hg hh
  have hnorm := tilt_normalized p hp (by linarith)
  have hV : tiltV p ^ 2 - tiltW p ^ 2 ≤ 1 := by nlinarith [sq_nonneg (tiltW p)]
  have hR := (tilt_product_bounds p hp hp2).2
  have hrs := rates_sum_nonneg x τ hx hx1
  have hnum : (gamma x τ - rateA x) * (tiltV p ^ 2 - tiltW p ^ 2) +
      (rateR x τ + rateC x τ) * (tiltV p * tiltW p) ≤
      coupling x τ / gap x τ + (rateR x τ + rateC x τ) * (2 * Real.sqrt p) := by
    calc
      _ ≤ (gamma x τ - rateA x) * 1 +
          (rateR x τ + rateC x τ) * (2 * Real.sqrt p) := by gcongr
      _ ≤ _ := by linarith
  rw [slow_weight_rearrange p x τ (ne_of_gt hd)]
  calc
    _ ≤ 4 * p + (coupling x τ / gap x τ +
        (rateR x τ + rateC x τ) * (2 * Real.sqrt p)) / gap x τ := by
      exact add_le_add (tiltW_sq_le p hp (by linarith))
        (div_le_div₀ (by positivity) hnum hg hdg)
    _ = _ := by field_simp; ring

theorem coupling_exact (x τ : ℝ) (hτ : 0 ≤ τ) :
    coupling x τ = 2 * x * τ * (1 + x ^ 2) / (1 - x) ^ 2 := by
  have hs := Real.sq_sqrt hτ
  unfold coupling rateR rateC
  rw [div_mul_div_comm]
  calc
    _ = 2 * x * (Real.sqrt τ) ^ 2 * (1 + x ^ 2) / (1 - x) ^ 2 := by ring
    _ = _ := by rw [hs]

theorem rates_sum_exact (x τ : ℝ) :
    rateR x τ + rateC x τ = Real.sqrt τ * (1 + x) ^ 2 / (1 - x) := by
  unfold rateR rateC
  rw [← add_div]
  ring

theorem coupling_small (x τ : ℝ) (hx : 0 ≤ x) (hxsmall : x ≤ 1 / 100)
    (hτ : 0 ≤ τ) : coupling x τ ≤ 3 * x * τ := by
  have hx1 : 0 < 1 - x := by linarith
  have hden : 0 < (1 - x) ^ 2 := by positivity
  rw [coupling_exact x τ hτ]
  apply (div_le_iff₀ hden).2
  have hfac : 2 * (1 + x ^ 2) ≤ 3 * (1 - x) ^ 2 := by nlinarith [sq_nonneg x]
  have := mul_le_mul_of_nonneg_left hfac (mul_nonneg hx hτ)
  nlinarith

theorem rates_sum_small (x τ : ℝ) (hx : 0 ≤ x) (hxsmall : x ≤ 1 / 100) :
    rateR x τ + rateC x τ ≤ 2 * Real.sqrt τ := by
  have hden : 0 < 1 - x := by linarith
  have hx2 : x ^ 2 ≤ x / 100 := by nlinarith [mul_nonneg hx (show 0 ≤ 1 / 100 - x by linarith)]
  have hfac : (1 + x) ^ 2 ≤ 2 * (1 - x) := by nlinarith
  rw [rates_sum_exact]
  apply (div_le_iff₀ hden).2
  nlinarith [mul_le_mul_of_nonneg_left hfac (Real.sqrt_nonneg τ)]

/-- 低比率区的粗权重界，常数不依赖 `p,x,τ`。 -/
theorem slow_weight_coarse (p x τ : ℝ) (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2)
    (hx : 0 ≤ x) (hxsmall : x ≤ 1 / 100) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1 / 2) :
    slowWeight p x τ ≤ 4 * p + 48 * x * τ + 16 * Real.sqrt (p * τ) := by
  have hx1 : x < 1 := by linarith
  have hg := gap_low_ratio x τ hx hτ1
  have hgp : 0 < gap x τ := lt_of_lt_of_le (by norm_num) hg
  have hg2 : 1 / 16 ≤ gap x τ ^ 2 := by nlinarith
  have hh : coupling x τ / gap x τ ^ 2 ≤ 48 * x * τ := by
    calc
      _ ≤ (3 * x * τ) / (1 / 16) :=
        div_le_div₀ (by positivity) (coupling_small x τ hx hxsmall hτ0) (by norm_num) hg2
      _ = _ := by ring
  have hr : 2 * Real.sqrt p * (rateR x τ + rateC x τ) / gap x τ ≤
      16 * Real.sqrt (p * τ) := by
    calc
      _ ≤ (2 * Real.sqrt p * (2 * Real.sqrt τ)) / (1 / 4) :=
        div_le_div₀ (by positivity) (by gcongr; exact rates_sum_small x τ hx hxsmall)
          (by norm_num) hg
      _ = _ := by rw [Real.sqrt_mul hp]; ring
  exact (slow_weight_bound p x τ hp hp2 hx hx1 hτ1).trans (by linarith)

theorem beta_identity (x τ : ℝ) :
    beta x τ = rateL x τ - (gamma x τ - rateA x) := by
  unfold beta gamma
  ring

theorem rate_fraction_exact (x τ : ℝ) :
    rateL x τ / rateA x = (1 + τ) / 2 - x / (1 + x ^ 2) -
      τ * x ^ 2 / (2 * (1 + x ^ 2)) := by
  have ha : 1 + x ^ 2 ≠ 0 := by positivity
  unfold rateL rateA
  field_simp
  ring

/-- 混合慢率允许低于 `1/2`；此处直接证明论文使用的误差界。 -/
theorem theta_low_ratio (x τ : ℝ) (hx : 0 ≤ x) (hxsmall : x ≤ 1 / 100)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1 / 2) :
    (1 + τ) / 2 - 8 * x ≤ beta x τ / rateA x ∧
      beta x τ / rateA x ≤ (1 + τ) / 2 := by
  have hx1 : x < 1 := by linarith
  have ha : 0 < rateA x := by unfold rateA; positivity
  have ha1 : 1 ≤ rateA x := by unfold rateA; nlinarith [sq_nonneg x]
  have hg := gap_low_ratio x τ hx hτ1
  have hgp : 0 < gap x τ := lt_of_lt_of_le (by norm_num) hg
  have hh := coupling_nonneg x τ hx hx1
  have hz := gamma_sub_a_nonneg x τ hh
  have hshift : gamma x τ - rateA x ≤ 12 * x * τ := by
    calc
      _ ≤ coupling x τ / gap x τ := gamma_shift_le x τ hgp hh
      _ ≤ (3 * x * τ) / (1 / 4) :=
        div_le_div₀ (by positivity) (coupling_small x τ hx hxsmall hτ0) (by norm_num) hg
      _ = _ := by ring
  have hshiftdiv : (gamma x τ - rateA x) / rateA x ≤ 12 * x * τ := by
    calc
      _ ≤ (12 * x * τ) / 1 := div_le_div₀ (by positivity) hshift (by norm_num) ha1
      _ = _ := by ring
  have hxd : x / (1 + x ^ 2) ≤ x := by
    exact (div_le_self hx (by nlinarith [sq_nonneg x]))
  have hx2 : x ^ 2 ≤ x := by nlinarith [mul_nonneg hx (show 0 ≤ 1 - x by linarith)]
  have hlast : τ * x ^ 2 / (2 * (1 + x ^ 2)) ≤ τ * x / 2 := by
    calc
      _ ≤ (τ * x) / 2 := div_le_div₀ (by positivity)
        (mul_le_mul_of_nonneg_left hx2 hτ0) (by norm_num) (by nlinarith [sq_nonneg x])
      _ = _ := rfl
  rw [beta_identity, sub_div, rate_fraction_exact]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hτ1 hx]
  · have h1 : 0 ≤ x / (1 + x ^ 2) := by positivity
    have h2 : 0 ≤ τ * x ^ 2 / (2 * (1 + x ^ 2)) := by positivity
    have h3 : 0 ≤ (gamma x τ - rateA x) / rateA x := by positivity
    linarith

theorem beta_low_ratio_pos (x τ : ℝ) (hx : 0 ≤ x) (hxsmall : x ≤ 1 / 100)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1 / 2) :
    0 < beta x τ ∧ beta x τ < rateA x := by
  have ht := theta_low_ratio x τ hx hxsmall hτ0 hτ1
  have ha : 0 < rateA x := by unfold rateA; positivity
  constructor
  · have h : 0 < beta x τ / rateA x := by nlinarith
    exact (div_pos_iff.mp h).resolve_right (by intro h; linarith [h.2]) |>.1
  · have h : beta x τ / rateA x < 1 := by linarith
    exact (div_lt_one ha).mp h

/-- 精确系数形式保留领先常数，后续只需控制两个显式有理因子。 -/
theorem slow_weight_refined (p x τ : ℝ) (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2)
    (hx : 0 ≤ x) (hx1 : x < 1) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1 / 2) :
    slowWeight p x τ ≤ 4 * p +
      8 * x * τ * (1 + x ^ 2) / ((1 - x) ^ 2 * ((1 + x) ^ 2 - τ) ^ 2) +
      4 * Real.sqrt (p * τ) * (1 + x) ^ 2 / ((1 - x) * ((1 + x) ^ 2 - τ)) := by
  have h := slow_weight_bound p x τ hp hp2 hx hx1 hτ1
  rw [coupling_exact x τ hτ0, rates_sum_exact, gap_exact] at h
  have hxn : 1 - x ≠ 0 := by linarith
  have hdn : (1 + x) ^ 2 - τ ≠ 0 := by
    have hg := gap_low_ratio x τ hx hτ1
    rw [gap_exact] at hg
    linarith
  have he1 : (2 * x * τ * (1 + x ^ 2) / (1 - x) ^ 2) /
      (((1 + x) ^ 2 - τ) / 2) ^ 2 =
      8 * x * τ * (1 + x ^ 2) / ((1 - x) ^ 2 * ((1 + x) ^ 2 - τ) ^ 2) := by
    field_simp
    ring
  have he2 : 2 * Real.sqrt p * (Real.sqrt τ * (1 + x) ^ 2 / (1 - x)) /
      (((1 + x) ^ 2 - τ) / 2) =
      4 * Real.sqrt (p * τ) * (1 + x) ^ 2 / ((1 - x) * ((1 + x) ^ 2 - τ)) := by
    rw [Real.sqrt_mul hp]
    field_simp
    ring
  rwa [he1, he2] at h

/-- 精确标量极值中与 `Q` 无关的连续前因子。 -/
def modePrefactor (P θ : ℝ) : ℝ :=
  (1 / θ - 1) * P * (θ / P) ^ (1 / (1 - θ))

theorem scalar_envelope_factor (P Q θ : ℝ) (hP : 0 < P) (hQ : 0 ≤ Q)
    (hθ : 0 < θ) (hθ1 : θ < 1) :
    Reset.scalarEnvelope P Q (1 / θ - 1) =
      modePrefactor P θ * Q ^ (1 / (1 - θ)) := by
  have hθn : θ ≠ 0 := ne_of_gt hθ
  have hθn1 : 1 - θ ≠ 0 := by linarith
  have he : (1 + (1 / θ - 1)) / (1 / θ - 1) = 1 / (1 - θ) := by field_simp; ring
  have hb : Q / ((1 + (1 / θ - 1)) * P) = θ / P * Q := by field_simp; ring
  unfold Reset.scalarEnvelope modePrefactor
  rw [he, hb, Real.mul_rpow (by positivity : 0 ≤ θ / P) hQ]
  ring

theorem mode_prefactor_value : modePrefactor 1 (1 / 2) = 1 / 4 := by
  norm_num [modePrefactor]

/-- 该连续性直接来自真实极值公式。 -/
theorem mode_prefactor_continuous :
    ContinuousAt (fun z : ℝ × ℝ => modePrefactor z.1 z.2) (1, 1 / 2) := by
  unfold modePrefactor
  have hb : ContinuousAt (fun z : ℝ × ℝ => z.2 / z.1) (1, 1 / 2) := by
    fun_prop (disch := norm_num)
  have he : ContinuousAt (fun z : ℝ × ℝ => 1 / (1 - z.2)) (1, 1 / 2) := by
    fun_prop (disch := norm_num)
  have hr := hb.rpow he (Or.inl (by norm_num))
  exact (show ContinuousAt (fun z : ℝ × ℝ => (1 / z.2 - 1) * z.1) (1, 1 / 2) by
    fun_prop (disch := norm_num)).mul hr

/-- `θ` 的真实低比率界给出指数偏移的统一下界，包括负偏移。 -/
theorem power_exponent_lower (θ τ x : ℝ) (hx : 0 ≤ x) (hτ : 0 ≤ τ)
    (hτ1 : τ ≤ 1 / 2) (hθ : (1 + τ) / 2 - 8 * x ≤ θ) (hθ1 : θ ≤ 3 / 4) :
    2 * τ - 128 * x ≤ 1 / (1 - θ) - 2 := by
  have hd : 0 < 1 - θ := by linarith
  apply (le_sub_iff_add_le).2
  apply (le_div_iff₀ hd).2
  have h1 := mul_nonneg (show 0 ≤ τ by exact hτ) (show 0 ≤ θ - ((1 + τ) / 2 - 8 * x) by linarith)
  have h2 := mul_nonneg hx (show 0 ≤ 3 / 4 - θ by linarith)
  have h3 := mul_nonneg hx (show 0 ≤ 1 / 2 - τ by linarith)
  nlinarith [sq_nonneg τ]

/-- 给正权重加统一底限后使用的指数扰动界，允许 `t<2`。 -/
theorem rpow_split_bound (Q t τ x L C : ℝ) (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (hτ : 0 ≤ τ) (hx : 0 ≤ x) (ht : 2 * τ - 128 * x ≤ t - 2)
    (hloglo : -L ≤ Real.log Q) (hloghi : Real.log Q ≤ -L / 2 + C) :
    Q ^ t ≤ Q ^ 2 * Real.exp (-τ * L + 2 * C * τ + 128 * x * L) := by
  have hlog0 : Real.log Q ≤ 0 := Real.log_nonpos hQ.le hQ1
  have h1 := mul_le_mul_of_nonpos_right ht hlog0
  have h2 := mul_le_mul_of_nonneg_left hloghi (show 0 ≤ 2 * τ by positivity)
  have h3 := mul_le_mul_of_nonpos_left hloglo (show -128 * x ≤ 0 by linarith)
  have he : Real.log Q * (t - 2) ≤ -τ * L + 2 * C * τ + 128 * x * L := by
    nlinarith
  calc
    Q ^ t = Q ^ (2 : ℝ) * Q ^ (t - 2) := by
      rw [← Real.rpow_add hQ]
      congr 1
      ring
    _ ≤ Q ^ (2 : ℝ) * Real.exp (-τ * L + 2 * C * τ + 128 * x * L) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [Real.rpow_def_of_pos hQ]
      exact Real.exp_le_exp.mpr he
    _ = _ := by norm_num

def weightFactorH (x τ : ℝ) : ℝ :=
  (1 + x ^ 2) / ((1 - x) ^ 2 * ((1 + x) ^ 2 - τ) ^ 2)
def weightFactorC (x τ : ℝ) : ℝ :=
  (1 + x) ^ 2 / ((1 - x) * ((1 + x) ^ 2 - τ))

theorem weight_factors_continuous :
    ContinuousAt (fun z : ℝ × ℝ => weightFactorH z.1 z.2) (0, 0) ∧
      ContinuousAt (fun z : ℝ × ℝ => weightFactorC z.1 z.2) (0, 0) := by
  constructor
  · unfold weightFactorH
    fun_prop (disch := norm_num)
  · unfold weightFactorC
    fun_prop (disch := norm_num)

/-- 两个实际有理系数在同一个有限矩形上统一接近1。 -/
theorem weight_factors_uniform (η : ℝ) (hη : 0 < η) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 / 4 ∧ ∀ x τ : ℝ,
      0 ≤ x → x < d → 0 ≤ τ → τ < d →
      weightFactorH x τ ≤ 1 + η ∧ weightFactorC x τ ≤ 1 + η := by
  have hh := weight_factors_continuous.1.tendsto.eventually
    (eventually_lt_nhds (show weightFactorH 0 0 < 1 + η by simpa [weightFactorH] using hη))
  have hc := weight_factors_continuous.2.tendsto.eventually
    (eventually_lt_nhds (show weightFactorC 0 0 < 1 + η by simpa [weightFactorC] using hη))
  obtain ⟨d, hd, hf⟩ := Metric.eventually_nhds_iff.mp (hh.and hc)
  refine ⟨min d (1 / 4), lt_min hd (by norm_num), min_le_right _ _, ?_⟩
  intro x τ hx hxd hτ hτd
  have hxlt : x < d := hxd.trans_le (min_le_left _ _)
  have hτlt : τ < d := hτd.trans_le (min_le_left _ _)
  have hdist : dist (x, τ) ((0, 0) : ℝ × ℝ) < d := by
    simpa [Prod.dist_eq, Real.dist_eq, abs_of_nonneg hx, abs_of_nonneg hτ] using
      max_lt hxlt hτlt
  exact ⟨(hf hdist).1.le, (hf hdist).2.le⟩

/-- 领先系数4直接来自真实权重；统一阈值只依赖容差。 -/
theorem slow_weight_uniform_refined (η : ℝ) (hη : 0 < η) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 / 4 ∧ ∀ p x τ : ℝ,
      0 ≤ p → p ≤ 1 / 2 → 0 ≤ x → x < d → 0 ≤ τ → τ < d →
      slowWeight p x τ ≤ 4 * p + (1 + η) *
        (4 * Real.sqrt (p * τ) + 8 * x * τ) := by
  obtain ⟨d, hd, hd1, hf⟩ := weight_factors_uniform η hη
  refine ⟨d, hd, hd1, ?_⟩
  intro p x τ hp hp2 hx hxd hτ hτd
  have hx1 : x < 1 := by linarith
  have hτ1 : τ ≤ 1 / 2 := by linarith
  have h := slow_weight_refined p x τ hp hp2 hx hx1 hτ hτ1
  have hb := hf x τ hx hxd hτ hτd
  have he : 4 * p +
      8 * x * τ * (1 + x ^ 2) / ((1 - x) ^ 2 * ((1 + x) ^ 2 - τ) ^ 2) +
      4 * Real.sqrt (p * τ) * (1 + x) ^ 2 / ((1 - x) * ((1 + x) ^ 2 - τ)) =
      4 * p + 8 * x * τ * weightFactorH x τ +
        4 * Real.sqrt (p * τ) * weightFactorC x τ := by
    unfold weightFactorH weightFactorC
    ring
  rw [he] at h
  have h1 := mul_le_mul_of_nonneg_left hb.1 (show 0 ≤ 8 * x * τ by positivity)
  have h2 := mul_le_mul_of_nonneg_left hb.2 (show 0 ≤ 4 * Real.sqrt (p * τ) by positivity)
  nlinarith

theorem discriminant_ge_neg_gap (x τ : ℝ) (hh : 0 ≤ coupling x τ) :
    -gap x τ ≤ discriminant x τ := by
  unfold discriminant
  exact (neg_le_abs _).trans
    (by simpa only [Real.sqrt_sq_eq_abs] using
      Real.sqrt_le_sqrt (show gap x τ ^ 2 ≤ gap x τ ^ 2 + 4 * coupling x τ by linarith))

theorem slow_weight_nonneg (p x τ : ℝ) (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2)
    (hx : 0 ≤ x) (hx1 : x < 1) (hτ : τ ≤ 1 / 2) :
    0 ≤ slowWeight p x τ := by
  have hh := coupling_nonneg x τ hx hx1
  have hga := gamma_sub_a_nonneg x τ hh
  have hgl : 0 ≤ gamma x τ - rateL x τ := by
    have h := discriminant_ge_neg_gap x τ hh
    unfold gamma gap at *
    linarith
  have hr := (tilt_product_bounds p hp hp2).1
  have hrs := rates_sum_nonneg x τ hx hx1
  have hd : 0 < discriminant x τ :=
    lt_of_lt_of_le (by norm_num) (discriminant_low_ratio x τ hx hx1 hτ)
  unfold slowWeight
  positivity

theorem chi_sq_budget (ν ρ : ℝ) (hν : 0 ≤ ν) (hνρ : ν ≤ ρ)
    (hρ : ρ ≤ 1 / 2) : chi ν ^ 2 ≤ 2 * ρ := by
  have hn : 0 < 1 - ν := by linarith
  unfold chi
  rw [Real.sq_sqrt (by positivity)]
  apply (div_le_iff₀ hn).2
  nlinarith [mul_nonneg hν (show 0 ≤ ρ by linarith)]

theorem chi_le_budget (ν ρ : ℝ) (hν : 0 ≤ ν) (hνρ : ν ≤ ρ)
    (hρ : ρ ≤ 1 / 2) : chi ν ≤ 2 * Real.sqrt ρ := by
  have hρ0 : 0 ≤ ρ := hν.trans hνρ
  have hs := Real.sq_sqrt hρ0
  have hc := chi_sq_budget ν ρ hν hνρ hρ
  have hn : 0 ≤ chi ν := Real.sqrt_nonneg _
  nlinarith [Real.sqrt_nonneg ρ]

/-- 对全部大比率都适用的代数根下界，无谱隙正下界假设。 -/
theorem beta_ge_of_product (x τ t : ℝ)
    (ha : t ≤ rateA x) (hl : t ≤ rateL x τ)
    (hh : coupling x τ ≤ (rateA x - t) * (rateL x τ - t)) :
    t ≤ beta x τ := by
  have hsum : 0 ≤ rateA x + rateL x τ - 2 * t := by linarith
  have hs : gap x τ ^ 2 + 4 * coupling x τ ≤
      (rateA x + rateL x τ - 2 * t) ^ 2 := by
    unfold gap
    nlinarith
  have hd : discriminant x τ ≤ rateA x + rateL x τ - 2 * t := by
    unfold discriminant
    exact (Real.sqrt_le_iff).2 ⟨hsum, hs⟩
  unfold beta
  linarith

theorem beta_large_ratio (x τ : ℝ) (hx : 0 ≤ x) (hxsmall : x ≤ 1 / 1000)
    (hτ : 1 / 2 ≤ τ) : 7 / 10 ≤ beta x τ := by
  have ha : 1 ≤ rateA x := by unfold rateA; nlinarith [sq_nonneg x]
  have hl : 7 / 10 ≤ rateL x τ := by unfold rateL; nlinarith [sq_nonneg x]
  apply beta_ge_of_product x τ (7 / 10) (by linarith) hl
  have hc := coupling_small x τ hx (by linarith) (by linarith)
  have hprod := mul_le_mul_of_nonneg_right (show 3 / 10 ≤ rateA x - 7 / 10 by linarith)
    (show 0 ≤ rateL x τ - 7 / 10 by linarith)
  have hxt := mul_nonneg (show 0 ≤ 1 / 1000 - x by linarith) (show 0 ≤ τ - 1 / 2 by linarith)
  unfold rateL at hprod ⊢
  nlinarith [sq_nonneg x]

theorem matrix_zero_A (ν B : ℝ) :
    comparisonMatrix ν 0 B = Matrix.diagonal ![0, -B / 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [comparisonMatrix, alpha, up, down, lambda, Matrix.diagonal] <;> ring

theorem quadratic_zero_A (p ν B : ℝ) :
    quadratic p (NormedSpace.exp (comparisonMatrix ν 0 B)) =
      tiltV p ^ 2 + tiltW p ^ 2 * Real.exp (-B / 2) := by
  rw [matrix_zero_A, Matrix.exp_diagonal]
  simp [quadratic, Pi.exp_def, ← Real.exp_eq_exp_ℝ, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two, Matrix.diagonal]
  ring

/-- 总体速率为零的完整真实矩阵包络，包含 `B=0`。 -/
theorem envelope_zero_A (p ν B : ℝ) (hp : 0 ≤ p) (hp8 : p ≤ 1 / 8) (hB : 0 ≤ B) :
    envelope p ν 0 B = 0 := by
  have hnorm := tilt_normalized p hp (by linarith)
  have hw := tiltW_sq_le p hp (by linarith)
  have he : Real.exp (-B / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hm := mul_le_mul_of_nonneg_left he (sq_nonneg (tiltW p))
  unfold envelope
  rw [quadratic_zero_A]
  simp only [alpha, zero_mul, neg_zero, Real.exp_zero, mul_one]
  apply max_eq_right
  nlinarith

/-- Q平方的显式统一误差；无需给τ设置正下限。 -/
theorem weight_square_estimate (q p x τ ρ f : ℝ)
    (hq0 : 0 ≤ q) (hp : 0 ≤ p) (hpρ : p ≤ ρ) (hx : 0 ≤ x)
    (hxρ : x ≤ 2 * Real.sqrt ρ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hf : 0 ≤ f)
    (hq : q ≤ 4 * p + f * (4 * Real.sqrt (p * τ) + 8 * x * τ)) :
    q ^ 2 / 4 ≤ 4 * p * τ * f ^ 2 +
      32 * f ^ 2 * ρ * τ * Real.sqrt τ + 64 * f ^ 2 * ρ * τ ^ 2 +
      40 * f * ρ * Real.sqrt ρ + 4 * ρ ^ 2 := by
  have hρ : 0 ≤ ρ := hp.trans hpρ
  have hsρ := Real.sq_sqrt hρ
  have hspτ := Real.sq_sqrt (mul_nonneg hp hτ0)
  have hsqrtρ := Real.sqrt_nonneg ρ
  have hsp := Real.sqrt_nonneg p
  have hsτ := Real.sqrt_nonneg τ
  have hspρ := Real.sqrt_le_sqrt hpρ
  have hpτ : p * τ ≤ ρ := by nlinarith [mul_le_mul_of_nonneg_left hτ1 hp]
  have hsqrtpτ := Real.sqrt_le_sqrt hpτ
  have hx2 : x ^ 2 ≤ 4 * ρ := by
    nlinarith [sq_le_sq₀ hx (by positivity) |>.mpr hxρ]
  have hp2 : p ^ 2 ≤ ρ ^ 2 := (sq_le_sq₀ hp hρ).mpr hpρ
  have hxsqrt : x * Real.sqrt (p * τ) ≤ 2 * ρ * Real.sqrt τ := by
    rw [Real.sqrt_mul hp]
    have hm := mul_le_mul hxρ hspρ hsp (by positivity)
    have hm2 := mul_le_mul_of_nonneg_right hm hsτ
    nlinarith
  have hcross1 : p * Real.sqrt (p * τ) ≤ ρ * Real.sqrt ρ :=
    mul_le_mul hpρ hsqrtpτ (Real.sqrt_nonneg _) hρ
  have hcross2 : p * x * τ ≤ 2 * ρ * Real.sqrt ρ := by
    have h := mul_le_mul hpρ hxρ hx hρ
    have h' := mul_le_mul_of_nonneg_right h hτ0
    have h'' := mul_le_mul_of_nonneg_left hτ1 (show 0 ≤ 2 * ρ * Real.sqrt ρ by positivity)
    nlinarith
  have hsq := (sq_le_sq₀ hq0 (by positivity : 0 ≤ 4 * p + f *
    (4 * Real.sqrt (p * τ) + 8 * x * τ))).mpr hq
  have hb1 := mul_le_mul_of_nonneg_left hxsqrt (show 0 ≤ 16 * f ^ 2 * τ by positivity)
  have hb2 := mul_le_mul_of_nonneg_left hx2 (show 0 ≤ 16 * f ^ 2 * τ ^ 2 by positivity)
  have hb3 := mul_le_mul_of_nonneg_left hcross1 (show 0 ≤ 8 * f by positivity)
  have hb4 := mul_le_mul_of_nonneg_left hcross2 (show 0 ≤ 16 * f by positivity)
  have hroot := congrArg (fun z : ℝ => 4 * f ^ 2 * z) hspτ
  nlinarith

theorem mode_prefactor_bounded (P θ : ℝ) (hP : 1 / 2 ≤ P) (hP1 : P ≤ 1)
    (hθ : 2 / 5 ≤ θ) (hθ1 : θ ≤ 3 / 4) :
    0 ≤ modePrefactor P θ ∧ modePrefactor P θ ≤ 32 := by
  have hP0 : 0 < P := by linarith
  have hθ0 : 0 < θ := by linarith
  have hd : 0 < 1 - θ := by linarith
  have hk0 : 0 ≤ 1 / θ - 1 := by
    have h : 1 ≤ 1 / θ := (le_div_iff₀ hθ0).2 (by linarith)
    linarith
  have hk2 : 1 / θ - 1 ≤ 2 := by
    have h : 1 / θ ≤ 3 := (div_le_iff₀ hθ0).2 (by linarith)
    linarith
  have hb0 : 0 ≤ θ / P := by positivity
  have hb2 : θ / P ≤ 2 := (div_le_iff₀ hP0).2 (by linarith)
  have he0 : 0 ≤ 1 / (1 - θ) := by positivity
  have he4 : 1 / (1 - θ) ≤ 4 := (div_le_iff₀ hd).2 (by linarith)
  have hr : (θ / P) ^ (1 / (1 - θ)) ≤ 16 := by
    calc
      _ ≤ (2 : ℝ) ^ (1 / (1 - θ)) := Real.rpow_le_rpow hb0 hb2 he0
      _ ≤ (2 : ℝ) ^ (4 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) he4
      _ = _ := by norm_num
  unfold modePrefactor
  constructor
  · positivity
  · have hm : (1 / θ - 1) * P ≤ 2 := by nlinarith [mul_le_mul_of_nonneg_left hP1 hk0]
    calc
      _ ≤ 2 * 16 := mul_le_mul hm hr (by positivity) (by norm_num)
      _ = 32 := by norm_num

theorem mode_prefactor_uniform (η : ℝ) (hη : 0 < η) :
    ∃ d : ℝ, 0 < d ∧ ∀ P θ : ℝ, |P - 1| < d → |θ - 1 / 2| < d →
      modePrefactor P θ ≤ (1 + η) / 4 := by
  have he := mode_prefactor_continuous.tendsto.eventually
    (eventually_lt_nhds (show modePrefactor 1 (1 / 2) < (1 + η) / 4 by
      rw [mode_prefactor_value]
      linarith))
  obtain ⟨d, hd, hf⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨d, hd, ?_⟩
  intro P θ hP hθ
  have hdist : dist (P, θ) ((1, 1 / 2) : ℝ × ℝ) < d := by
    simpa only [Prod.dist_eq, Real.dist_eq] using max_lt hP hθ
  exact (hf hdist).le

#print axioms two_rate_positive_bound
#print axioms two_modes_positive_bound
#print axioms tilt_normalized
#print axioms discriminant_low_ratio
#print axioms gamma_shift_le
#print axioms slow_weight_bound
#print axioms slow_weight_coarse
#print axioms theta_low_ratio
#print axioms beta_low_ratio_pos
#print axioms slow_weight_refined
#print axioms scalar_envelope_factor
#print axioms mode_prefactor_continuous
#print axioms power_exponent_lower
#print axioms rpow_split_bound
#print axioms weight_factors_uniform
#print axioms slow_weight_uniform_refined
#print axioms slow_weight_nonneg
#print axioms chi_sq_budget
#print axioms beta_large_ratio
#print axioms envelope_zero_A
#print axioms weight_square_estimate
#print axioms mode_prefactor_bounded
#print axioms mode_prefactor_uniform

end TwoStateQuantumEmbedding.ResetEnvelope
