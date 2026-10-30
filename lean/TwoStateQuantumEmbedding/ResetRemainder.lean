import TwoStateQuantumEmbedding.ResetFamily
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-! 冻结核心之后的连续尾段与定量余项。 -/
noncomputable section
open Filter Topology
namespace TwoStateQuantumEmbedding.ResetFamily

/-- 比 1/L 更小的误差；用于隔离指数小修正。 -/
def Fast (f : ℝ → ℝ) (a : ℝ) : Prop :=
  Tendsto (fun L => L * (f L - a)) atTop (𝓝 0)

theorem Fast.add {f g : ℝ → ℝ} {a b : ℝ} (hf : Fast f a) (hg : Fast g b) :
    Fast (fun L => f L + g L) (a + b) := by
  unfold Fast at hf hg ⊢
  convert Filter.Tendsto.add hf hg using 1 <;> simp only [add_zero]
  ext L
  ring

theorem Fast.mul {f g : ℝ → ℝ} {a b : ℝ} (hf : Fast f a) (hg : Fast g b)
    (hgl : Tendsto g atTop (𝓝 b)) : Fast (fun L => f L * g L) (a * b) := by
  unfold Fast at hf hg ⊢
  have h := (Filter.Tendsto.mul hf hgl).add (hg.const_mul a)
  simp only [zero_mul, mul_zero, add_zero] at h
  convert h using 1
  ext L
  ring

theorem Fast.div {f g : ℝ → ℝ} {a b : ℝ} (hf : Fast f a) (hg : Fast g b)
    (hgl : Tendsto g atTop (𝓝 b)) (hb : b ≠ 0) :
    Fast (fun L => f L / g L) (a / b) := by
  unfold Fast at hf hg ⊢
  have h := ((hf.const_mul b).sub (hg.const_mul a)).div (hgl.const_mul b)
    (mul_ne_zero hb hb)
  simp only [mul_zero, sub_self, zero_div] at h
  apply h.congr'
  filter_upwards [hgl.eventually_ne hb] with L hL
  simp only [Pi.div_apply]
  field_simp
  ring

theorem Fast.comp {u : ℝ → ℝ} {a : ℝ} (hu : Fast u a)
    (hul : Tendsto u atTop (𝓝 a)) (f : ℝ → ℝ) (hf : DifferentiableAt ℝ f a) :
    Fast (fun L => f (u L)) (f a) := by
  unfold Fast at hu ⊢
  have hd := (continuousAt_dslope_same.mpr hf).tendsto.comp hul
  have h := Filter.Tendsto.mul hu hd
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards with L
  have he := sub_smul_dslope f a (u L)
  simp only [smul_eq_mul] at he
  rw [← he]
  simp only [Function.comp_def]
  ring

theorem radius_fast : Fast radius 0 := by
  simpa only [Fast, sub_zero, mul_comm] using radius_times_L_limit

theorem scaled_radius_fast (c : ℝ) : Fast (fun L => c * radius L) 0 := by
  have h := radius_fast.const_mul c
  simpa only [Fast, sub_zero, mul_left_comm c, mul_zero] using h

theorem sinc_error_bound (x : ℝ) (hx : 0 < x) : |Real.sinc x - 1| ≤ x ^ 2 / 6 := by
  rw [Real.sinc_of_ne_zero hx.ne', div_sub_one hx.ne', abs_div, abs_of_pos hx]
  apply (div_le_iff₀ hx).mpr
  have h := Real.abs_sub_sin_le x
  rw [abs_sub_comm, abs_of_pos hx] at h
  convert h using 1
  ring

theorem sinc_radius_fast (c : ℝ) (hc : 0 < c) :
    Fast (fun L => Real.sinc (c * radius L)) 1 := by
  have hu := (radius_times_L_limit.const_mul c).mul (radius_limit.const_mul c)
  have hh := hu.div_const 6
  simp only [mul_zero, zero_div] at hh
  apply squeeze_zero_norm' _ hh
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hL]
  have hb := sinc_error_bound (c * radius L) (mul_pos hc (radius_pos L))
  have h := mul_le_mul_of_nonneg_left hb hL
  convert h using 1
  ring

theorem cos_radius_fast (c : ℝ) : Fast (fun L => Real.cos (c * radius L)) 1 := by
  have h := (scaled_radius_fast c).comp (by simpa using radius_limit.const_mul c)
    Real.cos (Real.differentiable_cos.differentiableAt)
  simpa only [Real.cos_zero] using h

theorem sin_radius_fast (c : ℝ) : Fast (fun L => Real.sin (c * radius L)) 0 := by
  have h := (scaled_radius_fast c).comp (by simpa using radius_limit.const_mul c)
    Real.sin (Real.differentiable_sin.differentiableAt)
  simpa only [Real.sin_zero] using h

theorem radius_div_sigma_fast : Fast (fun L => radius L / sigma L) 0 := by
  have h₂ : Tendsto (fun L => radius L * L ^ 2) atTop (𝓝 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 (1 / 2) (by norm_num)
    simpa [radius, neg_div, div_eq_mul_inv, mul_comm, Real.rpow_two] using h
  unfold Fast
  simp only [sub_zero]
  apply squeeze_zero' _ _ h₂
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    exact mul_nonneg hL (div_nonneg (radius_pos L).le (Real.sqrt_nonneg _))
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with L hL
    have hL0 : 0 < L := by linarith
    have hσ := sigma_pos L (by linarith)
    have hbound := (div_le_iff₀ hL0).mp (sigma_lower L hL)
    have hd : radius L / sigma L ≤ radius L * L := by
      apply (div_le_iff₀ hσ).mpr
      nlinarith [mul_le_mul_of_nonneg_left hbound (radius_pos L).le]
    convert mul_le_mul_of_nonneg_left hd hL0.le using 1
    ring

theorem sin_div_sigma_fast : Fast (fun L => Real.sin (2 * radius L) / sigma L) 0 := by
  unfold Fast
  simp only [sub_zero]
  have hs : Tendsto (fun L => Real.sinc (2 * radius L)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, mul_zero, Real.sinc_zero] using
      Real.continuous_sinc.continuousAt.tendsto.comp (radius_limit.const_mul 2)
  have h := (radius_div_sigma_fast.const_mul 2).mul hs
  simp only [mul_zero, sub_zero, zero_mul] at h
  apply h.congr'
  filter_upwards with L
  rw [Real.sinc_of_ne_zero (mul_ne_zero (by norm_num) (radius_pos L).ne')]
  field_simp [ne_of_gt (radius_pos L)]

theorem correction_fast : Fast correction 1 := by
  have hsin : Fast (fun L => -(rateRatio L * Real.sin (2 * radius L) / sigma L)) 0 := by
    have h := (Filter.Tendsto.mul sin_div_sigma_fast rateRatio_limit).neg
    simp only [Fast, sub_zero, zero_mul, neg_zero] at h ⊢
    convert h using 1
    ext L
    ring
  have hinner := (cos_radius_fast 2).add hsin
  simp only [add_zero] at hinner
  have hinnerlim : Tendsto (fun L => Real.cos (2 * radius L) +
      -(rateRatio L * Real.sin (2 * radius L) / sigma L)) atTop (𝓝 1) := by
    have hcos := Real.continuous_cos.continuousAt.tendsto.comp (radius_limit.const_mul 2)
    have h := hcos.sub (rateRatio_limit.mul sin_div_sigma_limit)
    simpa [Function.comp_def, mul_div_assoc, sub_eq_add_neg] using h
  have h := (sinc_radius_fast 2 (by norm_num)).mul hinner hinnerlim
  simpa only [Fast, one_mul, add_zero, correction, sub_eq_add_neg] using h

theorem curveB_fast : Fast curveB 1 := by
  have hsin : Fast (fun L => sigma L / rateRatio L * Real.sin (2 * radius L)) 0 := by
    have hq := sigma_limit.div rateRatio_limit (by norm_num : (1 : ℝ) ≠ 0)
    have h := Filter.Tendsto.mul (sin_radius_fast 2) hq
    simp only [Fast, sub_zero, zero_mul] at h ⊢
    convert h using 1
    ext L
    simp only [Pi.div_apply]
    ring
  have h := (cos_radius_fast 2).add hsin
  simpa only [Fast, curveB, add_zero] using h

theorem curveA_fast : Fast curveA 1 := by
  have h := (cos_radius_fast 2).mul curveB_fast curveB_limit
  simpa only [Fast, curveA, one_mul] using h

theorem gainCorrection_fast : Fast gainCorrection 1 := by
  have hratio := correction_fast.div curveA_fast curveA_limit (by norm_num)
  have hrl := correction_limit.div curveA_limit (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at hratio hrl
  have hlog := hratio.comp hrl Real.log (Real.differentiableAt_log (by norm_num))
  simp only [Real.log_one] at hlog
  have hel := (rateRatio_limit.const_add 1).div rateRatio_limit (by norm_num : (1 : ℝ) ≠ 0)
  have hprod := Filter.Tendsto.mul hlog hel
  simp only [sub_zero, zero_mul] at hprod
  have hprodF : Fast (fun L => ((1 + rateRatio L) / rateRatio L) *
      Real.log (correction L / curveA L)) 0 := by
    unfold Fast
    simp only [sub_zero]
    convert hprod using 1
    ext L
    simp only [Pi.div_apply]
    ring
  have hprodL : Tendsto (fun L => ((1 + rateRatio L) / rateRatio L) *
      Real.log (correction L / curveA L)) atTop (𝓝 0) := by
    have h := hel.mul (hrl.log (by norm_num : (1 : ℝ) ≠ 0))
    simpa [Pi.div_apply] using h
  have hexp := hprodF.comp hprodL Real.exp Real.differentiable_exp.differentiableAt
  have hexpl := Real.continuous_exp.continuousAt.tendsto.comp hprodL
  simp only [Real.exp_zero] at hexp hexpl
  have h := curveA_fast.mul hexp (by simpa only [Function.comp_def] using hexpl)
  simp only [mul_one] at h
  apply h.congr'
  have hratioPos := hrl.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hratioPos] with L hL
  change 0 < correction L / curveA L at hL
  unfold gainCorrection
  rw [Real.rpow_def_of_pos hL]
  congr 3
  ring_nf

theorem curveScale_fast : Fast curveScale 0 := by
  have hb := Filter.Tendsto.div curveA_fast ((rateRatio_limit.const_add 1).mul curveA_limit)
    (by norm_num : ((1 : ℝ) + 1) * 1 ≠ 0)
  simp only [Fast, sub_zero, zero_div] at hb ⊢
  apply squeeze_zero' _ _ hb
  · filter_upwards [eventually_gt_atTop (2 : ℝ), curveA_eventually_gt_one] with L hL hA
    have hs := Reset.optimal_scale_pos (curveA L) (curveA L - 1) (rateRatio L)
      (by linarith) (by linarith) (rateRatio_bounds L hL).1
    exact mul_nonneg (by linarith) hs.le
  · filter_upwards [eventually_gt_atTop (2 : ℝ), curveA_eventually_gt_one] with L hL hA
    obtain ⟨hk, hk1⟩ := rateRatio_bounds L hL
    have hAp : 0 < curveA L := by linarith
    have hQ : 0 < curveA L - 1 := by linarith
    have hbase : 0 < (curveA L - 1) / ((1 + rateRatio L) * curveA L) := by positivity
    have hbase1 : (curveA L - 1) / ((1 + rateRatio L) * curveA L) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      nlinarith
    have he : 1 ≤ (rateRatio L)⁻¹ := by
      rw [inv_eq_one_div]
      exact (le_div_iff₀ hk).mpr (by linarith)
    have hS := Real.rpow_le_self_of_le_one hbase.le hbase1 he
    change L * curveScale L ≤ (L * (curveA L - 1)) / ((1 + rateRatio L) * curveA L)
    unfold curveScale Reset.optimalScale
    have h := mul_le_mul_of_nonneg_left hS (by linarith : 0 ≤ L)
    convert h using 1
    ring

theorem curveFast_fast : Fast curveFast 0 := by
  unfold Fast
  simp only [sub_zero]
  apply squeeze_zero' _ _ (show Tendsto (fun L => L * curveScale L) atTop (𝓝 0) by
    simpa only [Fast, sub_zero] using curveScale_fast)
  · filter_upwards [eventually_gt_atTop (2 : ℝ), curveA_eventually_gt_one] with L hL hA
    exact mul_nonneg (by linarith) (Real.rpow_nonneg (le_of_lt (Reset.optimal_scale_pos _ _ _
      (by linarith) (by linarith) (rateRatio_bounds L hL).1)) _)
  · filter_upwards [eventually_gt_atTop (2 : ℝ), curveA_eventually_gt_one] with L hL hA
    have hk := (rateRatio_bounds L hL).1
    have hs := Reset.optimal_scale_pos (curveA L) (curveA L - 1) (rateRatio L)
      (by linarith) (by linarith) hk
    have hs1 := Reset.optimal_scale_lt_one (curveA L) (curveA L - 1) (rateRatio L)
      (by linarith) (by linarith) (by linarith) hk
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_self_of_le_one hs.le hs1.le (by linarith))
      (by linarith)

theorem curveEpsilon_scaled_fast : Fast (fun L => curveEpsilon L / radius L ^ 2) 1 := by
  have hs : Tendsto (fun L => Real.sinc (radius L)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.sinc_zero] using
      Real.continuous_sinc.continuousAt.tendsto.comp radius_limit
  have hsF : Fast (fun L => Real.sinc (radius L)) 1 := by
    simpa only [one_mul] using sinc_radius_fast 1 (by norm_num)
  have hsSq := hsF.mul hsF hs
  have hbr : Fast (fun L => 1 - (1 + curveB L) * curveScale L +
      curveB L * curveFast L) 1 := by
    have h₁ := Filter.Tendsto.mul curveScale_fast (curveB_limit.const_add 1)
    have h₂ := Filter.Tendsto.mul curveFast_fast curveB_limit
    have h := h₂.sub h₁
    simp only [sub_zero, zero_mul] at h
    unfold Fast
    convert h using 1
    ext L
    ring
  have hbrL : Tendsto (fun L => 1 - (1 + curveB L) * curveScale L +
      curveB L * curveFast L) atTop (𝓝 1) := by
    have h := (((curveB_limit.const_add 1).mul curveScale_limit).const_sub 1).add
      (curveB_limit.mul curveFast_limit)
    simpa using h
  have h := hsSq.mul hbr hbrL
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards with L
  rw [Real.sinc_of_ne_zero (radius_pos L).ne']
  unfold curveEpsilon
  field_simp [ne_of_gt (radius_pos L)]

def shapeSmooth (δ : ℝ) : ℝ := Real.log 2 - (2 - δ) / 2 * Real.log (2 - δ) -
  Real.log (1 - δ)
def coreExponent (L : ℝ) : ℝ := Reset.shapeLogCorrection (2 / L) + 1 - 1 / rateRatio L
def relativeErrorScale (L : ℝ) : ℝ := Real.log L / L

theorem shapeSmooth_zero : shapeSmooth 0 = 0 := by simp [shapeSmooth]

theorem shapeSmooth_differentiable : DifferentiableAt ℝ shapeSmooth 0 := by
  unfold shapeSmooth
  fun_prop (disch := norm_num)

theorem shape_log_correction_rate :
    Tendsto (fun L => Reset.shapeLogCorrection (2 / L) / relativeErrorScale L)
      atTop (𝓝 (-1)) := by
  have hδ : Tendsto (fun L : ℝ => 2 / L) atTop (𝓝 0) := tendsto_id.const_div_atTop 2
  have hlogratio : Tendsto (fun L : ℝ => Real.log (2 / L) / Real.log L) atTop (𝓝 (-1)) := by
    have h := (Real.tendsto_log_atTop.const_div_atTop (Real.log 2)).sub_const 1
    simp only [zero_sub] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with L hL
    have hL0 : L ≠ 0 := by linarith
    have hlog0 : Real.log L ≠ 0 := (Real.log_pos (by linarith)).ne'
    rw [Real.log_div (by norm_num) hL0]
    field_simp
  have hslope := (continuousAt_dslope_same.mpr shapeSmooth_differentiable).tendsto.comp hδ
  have hsm : Tendsto (fun L => shapeSmooth (2 / L) / relativeErrorScale L) atTop (𝓝 0) := by
    have h := (hslope.const_mul 2).div_atTop Real.tendsto_log_atTop
    apply h.congr'
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with L hL
    have hL0 : L ≠ 0 := by linarith
    have he := sub_smul_dslope shapeSmooth 0 (2 / L)
    simp only [shapeSmooth_zero, sub_zero, smul_eq_mul] at he
    rw [← he]
    simp only [Function.comp_def, relativeErrorScale]
    field_simp
  have hsmall := (hlogratio.add hsm).div rateRatio_limit (by norm_num : (1 : ℝ) ≠ 0)
  simp only [add_zero, div_one] at hsmall
  apply hsmall.congr'
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with L hL
  have hL0 : L ≠ 0 := by linarith
  have hk := (rateRatio_bounds L hL).1.ne'
  have hlog0 : Real.log L ≠ 0 := (Real.log_pos (by linarith)).ne'
  unfold Reset.shapeLogCorrection relativeErrorScale shapeSmooth
  simp only [Pi.div_apply]
  change _ = (2 / L * Real.log (2 / L) / 2 + Real.log 2 -
    (2 - 2 / L) / 2 * Real.log (2 - 2 / L) - Real.log (1 - 2 / L)) /
    rateRatio L / (Real.log L / L)
  field_simp
  ring

theorem coreExponent_limit : Tendsto coreExponent atTop (𝓝 0) := by
  have hδ : Tendsto (fun L : ℝ => 2 / L) atTop (𝓝 0) := tendsto_id.const_div_atTop 2
  have hc := Reset.shape_log_correction_continuous.tendsto.comp hδ
  rw [Reset.shape_log_correction_zero] at hc
  have h := (hc.add_const 1).sub ((tendsto_const_nhds (x := (1 : ℝ))).div
    rateRatio_limit (by norm_num : (1 : ℝ) ≠ 0))
  change Tendsto (fun L => Reset.shapeLogCorrection (2 / L) + 1 - 1 / rateRatio L) atTop (𝓝 0)
  simpa only [Function.comp_def, Pi.div_apply, zero_add, div_one, sub_self] using h

theorem coreExponent_rate :
    Tendsto (fun L => coreExponent L / relativeErrorScale L) atTop (𝓝 (-1)) := by
  have hlogInv : Tendsto (fun L : ℝ => 2 / Real.log L) atTop (𝓝 0) :=
    Real.tendsto_log_atTop.const_div_atTop 2
  have hsmall := (hlogInv.div rateRatio_limit (by norm_num : (1 : ℝ) ≠ 0)).neg
  have h := shape_log_correction_rate.add hsmall
  simp only [zero_div, neg_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with L hL
  have hL0 : L ≠ 0 := by linarith
  have hk := (rateRatio_bounds L hL).1.ne'
  have hlog0 : Real.log L ≠ 0 := (Real.log_pos (by linarith)).ne'
  simp only [Pi.div_apply, coreExponent, relativeErrorScale]
  field_simp
  unfold rateRatio
  field_simp
  ring

theorem scaled_reset_gain_exponent (L : ℝ) (hL : 2 < L) :
    L * Reset.resetGain L = (4 / Real.exp 1) * Real.exp (coreExponent L) := by
  rw [Reset.scaled_reset_gain_exact L hL]
  unfold coreExponent rateRatio
  rw [Real.exp_sub, Real.exp_add]
  simp only [neg_div, Real.exp_neg]
  field_simp

theorem scaled_reset_gain_rate :
    Tendsto (fun L => (L * Reset.resetGain L - 4 / Real.exp 1) / relativeErrorScale L)
      atTop (𝓝 (-(4 / Real.exp 1))) := by
  have hs := (continuousAt_dslope_same.mpr Real.differentiable_exp.differentiableAt).tendsto.comp
    coreExponent_limit
  simp only [dslope_same, Real.deriv_exp, Real.exp_zero] at hs
  have h := (hs.mul coreExponent_rate).const_mul (4 / Real.exp 1)
  simp only [mul_neg_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with L hL
  rw [scaled_reset_gain_exponent L hL]
  have he := sub_smul_dslope Real.exp 0 (coreExponent L)
  simp only [Real.exp_zero, sub_zero, smul_eq_mul] at he
  simp only [Function.comp_def]
  calc
    _ = (4 / Real.exp 1) * (coreExponent L * dslope Real.exp 0 (coreExponent L)) /
        relativeErrorScale L := by ring
    _ = (4 / Real.exp 1) * (Real.exp (coreExponent L) - 1) / relativeErrorScale L := by rw [he]
    _ = _ := by ring

def probabilityCorrection (L : ℝ) : ℝ := gainCorrection L / (curveEpsilon L / radius L ^ 2)
def logScale (L : ℝ) : ℝ := Real.log (1 / curveEpsilon L)
def scalarRemainder (L : ℝ) : ℝ :=
  (4 / Real.exp 1) / logScale L - curveGain L / curveEpsilon L
def targetRemainderScale (L : ℝ) : ℝ := Real.log (logScale L) / logScale L ^ 2

theorem probabilityCorrection_limit : Tendsto probabilityCorrection atTop (𝓝 1) := by
  change Tendsto (fun L => gainCorrection L / (curveEpsilon L / radius L ^ 2)) atTop _
  have h := gainCorrection_limit.div curveEpsilon_scaled_limit (by norm_num : (1 : ℝ) ≠ 0)
  change Tendsto (fun L => gainCorrection L / (curveEpsilon L / radius L ^ 2))
    atTop (𝓝 (1 / 1 : ℝ)) at h
  simpa only [div_one] using h

theorem probabilityCorrection_fast : Fast probabilityCorrection 1 := by
  have h := gainCorrection_fast.div curveEpsilon_scaled_fast curveEpsilon_scaled_limit
    (by norm_num : (1 : ℝ) ≠ 0)
  simpa only [Fast, probabilityCorrection, div_one] using h

theorem curve_relative_gain_exact (L : ℝ) (hL : 2 < L) (hA : 1 < curveA L) :
    curveGain L / curveEpsilon L = Reset.resetGain L * probabilityCorrection L := by
  have h := curveGain_scaled_exact L hL hA
  unfold probabilityCorrection
  have hr := (radius_pos L).ne'
  field_simp at h ⊢
  rw [h]

theorem curve_relative_gain_rate :
    Tendsto (fun L => (L * (curveGain L / curveEpsilon L) - 4 / Real.exp 1) /
      relativeErrorScale L) atTop (𝓝 (-(4 / Real.exp 1))) := by
  have hsmall := probabilityCorrection_fast.div_atTop Real.tendsto_log_atTop
  have h := (scaled_reset_gain_rate.mul probabilityCorrection_limit).add
    (hsmall.const_mul (4 / Real.exp 1))
  simp only [mul_one, mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (2 : ℝ), curveA_eventually_gt_one] with L hL hA
  rw [curve_relative_gain_exact L hL hA]
  unfold relativeErrorScale
  have hL0 : L ≠ 0 := by linarith
  field_simp
  ring

theorem logScale_sub_L (L : ℝ) (he : 0 < curveEpsilon L) :
    logScale L - L = -Real.log (curveEpsilon L / radius L ^ 2) := by
  have hr : radius L ^ 2 ≠ 0 := pow_ne_zero _ (radius_pos L).ne'
  have hlogr : Real.log (radius L ^ 2) = -L := by
    rw [Real.log_pow, radius, Real.log_exp]
    ring
  unfold logScale
  rw [Real.log_div he.ne' hr, hlogr, one_div, Real.log_inv]
  ring

theorem logScale_div_L_limit : Tendsto (fun L => logScale L / L) atTop (𝓝 1) :=
  curve_log_scale_limit

theorem logScale_eventually_gt_one : ∀ᶠ L : ℝ in atTop, 1 < logScale L := by
  have h := logScale_div_L_limit.eventually
    (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  filter_upwards [eventually_gt_atTop (4 : ℝ), h] with L hL hT
  have hL0 : 0 < L := by linarith
  have hT' := (lt_div_iff₀ hL0).mp hT
  linarith

theorem log_logScale_ratio_limit :
    Tendsto (fun L => Real.log (logScale L) / Real.log L) atTop (𝓝 1) := by
  have hl := logScale_div_L_limit.log (by norm_num : (1 : ℝ) ≠ 0)
  simp only [Real.log_one] at hl
  have h := (hl.div_atTop Real.tendsto_log_atTop).const_add 1
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (2 : ℝ), logScale_eventually_gt_one] with L hL hT
  have hL0 : L ≠ 0 := by linarith
  have hT0 : logScale L ≠ 0 := by linarith
  have hlog0 : Real.log L ≠ 0 := (Real.log_pos (by linarith)).ne'
  rw [Real.log_div hT0 hL0]
  field_simp
  ring

theorem scalarRemainder_L_rate :
    Tendsto (fun L => scalarRemainder L / (Real.log L / L ^ 2)) atTop
      (𝓝 (4 / Real.exp 1)) := by
  have hlogE := curveEpsilon_scaled_limit.log (by norm_num : (1 : ℝ) ≠ 0)
  simp only [Real.log_one] at hlogE
  have hsmall := ((hlogE.div_atTop Real.tendsto_log_atTop).div logScale_div_L_limit
    (by norm_num : (1 : ℝ) ≠ 0)).const_mul (4 / Real.exp 1)
  have h := hsmall.sub curve_relative_gain_rate
  simp only [zero_div, mul_zero, zero_sub, neg_neg] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (2 : ℝ), logScale_eventually_gt_one,
    curveEpsilon_eventually_pos] with L hL hT he
  have hL0 : L ≠ 0 := by linarith
  have hT0 : logScale L ≠ 0 := by linarith
  have hlog0 : Real.log L ≠ 0 := (Real.log_pos (by linarith)).ne'
  have hl := logScale_sub_L L he
  simp only [Pi.div_apply, relativeErrorScale, scalarRemainder]
  field_simp
  linear_combination 4 * curveEpsilon L * hl

theorem scalarRemainder_target_rate :
    Tendsto (fun L => scalarRemainder L / targetRemainderScale L) atTop
      (𝓝 (4 / Real.exp 1)) := by
  have hscale := (logScale_div_L_limit.pow 2).div log_logScale_ratio_limit
    (by norm_num : (1 : ℝ) ≠ 0)
  have h := scalarRemainder_L_rate.mul hscale
  simp only [one_pow, div_one, mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (2 : ℝ), logScale_eventually_gt_one] with L hL hT
  have hL0 : L ≠ 0 := by linarith
  have hT0 : logScale L ≠ 0 := by linarith
  have hlog0 : Real.log L ≠ 0 := (Real.log_pos (by linarith)).ne'
  have hlogT0 := (Real.log_pos hT).ne'
  simp only [Pi.div_apply, targetRemainderScale]
  field_simp

def actualEpsilon (L : ℝ) : ℝ := 1 - (finiteOutput 0 (unitJumps L) 1).2
def actualRemainder (L : ℝ) : ℝ :=
  (finiteOutput 0 (unitJumps L) 1).1 / actualEpsilon L -
    (1 - (4 / Real.exp 1) / Real.log (1 / actualEpsilon L))
def actualRemainderScale (L : ℝ) : ℝ :=
  Real.log (Real.log (1 / actualEpsilon L)) / Real.log (1 / actualEpsilon L) ^ 2

/-- 原 K006 的定量余项，实际上还有明确的下一阶极限。 -/
theorem finiteOutput_remainder_rate :
    Tendsto (fun L => actualRemainder L / actualRemainderScale L) atTop
      (𝓝 (4 / Real.exp 1)) := by
  apply scalarRemainder_target_rate.congr'
  filter_upwards [eventually_gt_atTop (2 : ℝ), curveA_eventually_gt_one,
    curveEpsilon_eventually_pos] with L hL hA he
  unfold actualRemainder actualRemainderScale actualEpsilon
  rw [actual_unit_curve_output L hL hA]
  simp only [curvePoint, sub_sub_cancel]
  unfold scalarRemainder targetRemainderScale logScale
  field_simp
  ring

/-- 以真实有限 GKSL 概率表述的 O(loglog/log²) 余项。 -/
theorem finiteOutput_remainder_isBigO :
    Asymptotics.IsBigO atTop actualRemainder actualRemainderScale := by
  apply Asymptotics.isBigO_of_div_tendsto_nhds _ (4 / Real.exp 1) finiteOutput_remainder_rate
  filter_upwards [eventually_gt_atTop (2 : ℝ), curveA_eventually_gt_one,
    logScale_eventually_gt_one] with L hL hA hT
  have hpos : 0 < actualRemainderScale L := by
    unfold actualRemainderScale actualEpsilon
    rw [actual_unit_curve_output L hL hA]
    simp only [curvePoint, sub_sub_cancel]
    change 0 < Real.log (logScale L) / logScale L ^ 2
    exact div_pos (Real.log_pos hT) (sq_pos_of_pos (by linarith))
  exact fun hzero => False.elim (hpos.ne' hzero)

theorem curveGain_eventually_pos : ∀ᶠ L : ℝ in atTop, 0 < curveGain L := by
  filter_upwards [eventually_gt_atTop (2 : ℝ), curveA_eventually_gt_one] with L hL hA
  have hk := (rateRatio_bounds L hL).1
  have hAp : 0 < curveA L := by linarith
  have hS := Reset.optimal_scale_pos (curveA L) (curveA L - 1) (rateRatio L)
    hAp (by linarith) hk
  exact mul_pos (mul_pos hk hAp) (Real.rpow_pos_of_pos hS _)

theorem curve_relative_gain_zero :
    Tendsto (fun L => curveGain L / curveEpsilon L) atTop (𝓝 0) := by
  have h := curve_relative_gain_limit.div_atTop tendsto_id
  apply h.congr'
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with L hL
  have hL0 : L ≠ 0 := by linarith
  simp only [id_eq]
  field_simp

/-- 实际尾段在概率方形内部，并严格低于经典重置直线。 -/
theorem finiteOutput_nonclassical_tail : ∀ᶠ L : ℝ in atTop,
    let p := finiteOutput 0 (unitJumps L) 1
    0 < p.1 ∧ p.1 < 1 - p.2 ∧ 0 < p.2 ∧ p.2 < 1 := by
  have hG := curve_relative_gain_zero.eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hE := curveEpsilon_limit.eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_gt_atTop (2 : ℝ), curveA_eventually_gt_one,
    curveEpsilon_eventually_pos, curveGain_eventually_pos, hG, hE] with L hL hA he hg hrel he1
  dsimp only
  rw [actual_unit_curve_output L hL hA]
  simp only [curvePoint, sub_sub_cancel]
  have hge : curveGain L < curveEpsilon L := (div_lt_one he).mp hrel
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem time_eventually_pos : ∀ᶠ L : ℝ in atTop, 0 < curveTime L := by
  filter_upwards [eventually_gt_atTop (2 : ℝ), curveA_eventually_gt_one] with L hL hA
  exact optimalTime_pos _ _ hA (rateRatio_bounds L hL).1

theorem triangularJump_rank_one (m n : ℝ) (hn : n ≠ 0) :
    (triangularJump m n).rank = 1 := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hv : triangularJump m n = Matrix.vecMulVec ![-(m : ℂ), n] ![1, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [triangularJump, Matrix.vecMulVec]
  have hu : (triangularJump m n).rank ≤ 1 := by
    rw [hv]
    exact Matrix.rank_vecMulVec_le _ _
  have hsub : ((triangularJump m n).submatrix (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 0)).rank = 1 := by
    have hd : ((triangularJump m n).submatrix (fun _ : Fin 1 => 1)
        (fun _ : Fin 1 => 0)).det ≠ 0 := by
      simpa [Matrix.det_fin_one, Matrix.submatrix, triangularJump] using hnC
    simpa using Matrix.rank_of_det_ne_zero hd
  have hl := Matrix.rank_submatrix_le (triangularJump m n)
    (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 0)
  rw [hsub] at hl
  omega

theorem jump_rank_one (c s m n : ℝ) (hc : c ^ 2 + s ^ 2 = 1) (hn : n ≠ 0) :
    (jump c s m n).rank = 1 := by
  have hdet : (rotation c s).det = 1 := by
    have hC : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hc
    simp [rotation, Matrix.det_fin_two]
    linear_combination hC
  have hdetStar : (rotation c s).conjTranspose.det ≠ 0 := by
    simp [Matrix.det_conjTranspose, hdet]
  unfold jump conjugate
  rw [Matrix.rank_mul_eq_left_of_det_ne_zero _ _ hdetStar,
    Matrix.rank_mul_eq_right_of_det_ne_zero _ _ (by rw [hdet]; norm_num)]
  exact triangularJump_rank_one m n hn

theorem unitJumps_eventually_rank_one : ∀ᶠ L : ℝ in atTop, ∀ μ : Fin 1,
    (unitJumps L μ).rank = 1 := by
  filter_upwards [eventually_gt_atTop (2 : ℝ), time_eventually_pos] with L hL ht
  intro μ
  have hn : 0 < paperN (rateRatio L) := by
    have hk := (rateRatio_bounds L hL).1
    unfold paperN
    positivity
  have hs : (Real.sqrt (curveTime L) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr ht).ne'
  change (((Real.sqrt (curveTime L) : ℂ)) •
    jump (Real.cos (radius L)) (Real.sin (radius L)) (paperM (rateRatio L))
      (paperN (rateRatio L))).rank = 1
  rw [Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hs)]
  exact jump_rank_one _ _ _ _ (Real.cos_sq_add_sin_sq _) hn.ne'

theorem curveEpsilon_continuousAt (L : ℝ) (hL : 2 < L) (hA : 1 < curveA L) :
    ContinuousAt curveEpsilon L := by
  have hL0 : L ≠ 0 := by linarith
  have hkpos := (rateRatio_bounds L hL).1
  have hApos : 0 < curveA L := by linarith
  have hk0 := hkpos.ne'
  have hA0 : curveA L ≠ 0 := by linarith
  have hr : ContinuousAt radius L := by unfold radius; fun_prop
  have hk : ContinuousAt rateRatio L := by unfold rateRatio; fun_prop
  have hσ : ContinuousAt sigma L := by unfold sigma; fun_prop
  have hb : ContinuousAt curveB L := by unfold curveB; fun_prop
  have ha : ContinuousAt curveA L := by unfold curveA; fun_prop
  have hbase : 0 < (curveA L - 1) / ((1 + rateRatio L) * curveA L) := by
    have hp := (rateRatio_bounds L hL).1
    positivity
  have hs : ContinuousAt curveScale L := by
    unfold curveScale Reset.optimalScale
    exact ContinuousAt.rpow (by fun_prop (disch := positivity)) (by fun_prop) (Or.inl hbase.ne')
  have hf : ContinuousAt curveFast L := by
    have hsp : 0 < curveScale L :=
      Reset.optimal_scale_pos _ _ _ (by linarith) (by linarith) (rateRatio_bounds L hL).1
    unfold curveFast
    exact ContinuousAt.rpow hs (by fun_prop) (Or.inl hsp.ne')
  unfold curveEpsilon
  fun_prop

/-- 连续尾段覆盖每个充分小的正重置误差，无需假设单调性。 -/
theorem curve_covers_small_epsilon :
    ∃ ε₀ > 0, ∀ ε ∈ Set.Ioo 0 ε₀, ∃ L : ℝ,
      2 < L ∧ 1 < curveA L ∧ curveEpsilon L = ε ∧ curvePoint L ∈ Q2 := by
  have hevent : ∀ᶠ L : ℝ in atTop,
      2 < L ∧ 1 < curveA L ∧ 0 < curveEpsilon L :=
    (eventually_gt_atTop (2 : ℝ)).and (curveA_eventually_gt_one.and curveEpsilon_eventually_pos)
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp hevent
  refine ⟨curveEpsilon L₀, (hL₀ L₀ le_rfl).2.2, ?_⟩
  intro ε hε
  have ht := curveEpsilon_limit.eventually (eventually_lt_nhds hε.1)
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.mp ht
  let M := max L₀ L₁
  have hm : L₀ ≤ M := le_max_left _ _
  have hεM : curveEpsilon M < ε := hL₁ M (le_max_right _ _)
  have hc : ContinuousOn curveEpsilon (Set.Icc L₀ M) := by
    intro x hx
    exact (curveEpsilon_continuousAt x (hL₀ x hx.1).1 (hL₀ x hx.1).2.1).continuousWithinAt
  obtain ⟨L, hLint, hLe⟩ := intermediate_value_Icc' hm hc ⟨hεM.le, hε.2.le⟩
  refine ⟨L, (hL₀ L hLint.1).1, (hL₀ L hLint.1).2.1, hLe, ?_⟩
  rw [← actual_unit_curve_output L (hL₀ L hLint.1).1 (hL₀ L hLint.1).2.1]
  exact finiteOutput_mem_Q2 0 (unitJumps L) 1 (by simp) (by norm_num)

end TwoStateQuantumEmbedding.ResetFamily

#print axioms TwoStateQuantumEmbedding.ResetFamily.curve_covers_small_epsilon
#print axioms TwoStateQuantumEmbedding.ResetFamily.gainCorrection_fast
#print axioms TwoStateQuantumEmbedding.ResetFamily.curveEpsilon_scaled_fast
#print axioms TwoStateQuantumEmbedding.ResetFamily.scaled_reset_gain_rate
#print axioms TwoStateQuantumEmbedding.ResetFamily.finiteOutput_remainder_rate
#print axioms TwoStateQuantumEmbedding.ResetFamily.finiteOutput_remainder_isBigO
#print axioms TwoStateQuantumEmbedding.ResetFamily.finiteOutput_nonclassical_tail
#print axioms TwoStateQuantumEmbedding.ResetFamily.unitJumps_eventually_rank_one




