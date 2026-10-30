import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic

/-!
# 重置端点的已编译标量核心

本文件不定义 GKSL 或量子通道，也不宣称完整形式化论文的纯稳态端点定理。
注释中的对应关系仅用于审计，所有声明均由 Lean 内核检查。
-/

noncomputable section
open Filter Topology

namespace Reset

/-- 领先尺度的统一上界；不要求 `δ` 为正。 -/
theorem logarithmic_profile_bound (L δ : ℝ) (hL : 0 < L) :
    2 * δ * Real.exp (-(L * δ / 2)) ≤ 4 / (Real.exp 1 * L) := by
  have h := Real.mul_exp_neg_le_exp_neg_one (L * δ / 2)
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ 4 / L by positivity)
  have hLn : L ≠ 0 := ne_of_gt hL
  rw [Real.exp_neg 1] at hm
  convert hm using 1 <;> field_simp
  ring

/-- 上界在明确参数 `δ = 2/L` 处达到。 -/
theorem logarithmic_profile_attains (L : ℝ) (hL : 0 < L) :
    2 * (2 / L) * Real.exp (-(L * (2 / L) / 2)) =
      4 / (Real.exp 1 * L) := by
  have hLn : L ≠ 0 := ne_of_gt hL
  have he : L * (2 / L) / 2 = 1 := by field_simp
  rw [he, Real.exp_neg]
  field_simp
  norm_num

/-- Bernoulli 不等式给出的无量纲精确幂次包络。 -/
theorem normalized_power_envelope (k x : ℝ) (hk : 0 ≤ k) (hx : 0 ≤ x) :
    (1 + k) * x - x ^ (1 + k) ≤ k := by
  have h := one_add_mul_self_le_rpow_one_add
    (s := x - 1) (by linarith : -1 ≤ x - 1)
    (p := 1 + k) (by linarith : 1 ≤ 1 + k)
  have he : 1 + (x - 1) = x := by ring
  rw [he] at h
  nlinarith

/-- 标量平方根条件是由通道与稳态的两个正性估计产生的中间前提。 -/
theorem stationary_measurement_product (a ε p : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hε : 0 ≤ ε)
    (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (h : p ≤ (Real.sqrt (a * p) + Real.sqrt (ε * (1 - p))) ^ 2) :
    ((1 - Real.sqrt a) ^ 2 + ε) * p ≤ ε := by
  have hsp := Real.sq_sqrt hp
  have hsa := Real.sq_sqrt ha
  have hse := Real.sq_sqrt (show 0 ≤ ε * (1 - p) by positivity)
  rw [Real.sqrt_mul ha] at h
  have hsqa : Real.sqrt a ≤ 1 := by
    have := Real.sqrt_nonneg a
    nlinarith
  have hroot : Real.sqrt p ≤
      Real.sqrt a * Real.sqrt p + Real.sqrt (ε * (1 - p)) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg p) (by positivity)).mp
    simpa only [hsp] using h
  have hnonneg : 0 ≤ (1 - Real.sqrt a) * Real.sqrt p := by positivity
  have hsquare : ((1 - Real.sqrt a) * Real.sqrt p) ^ 2 ≤
      (Real.sqrt (ε * (1 - p))) ^ 2 := by
    apply (sq_le_sq₀ hnonneg (Real.sqrt_nonneg _)).mpr
    nlinarith
  rw [mul_pow, hsp, hse] at hsquare
  nlinarith

/-- 分母严格正时的分式版本，不对恒等表产生 `0/0`。 -/
theorem stationary_measurement_fraction (a ε p : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hε : 0 ≤ ε)
    (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hden : 0 < (1 - Real.sqrt a) ^ 2 + ε)
    (h : p ≤ (Real.sqrt (a * p) + Real.sqrt (ε * (1 - p))) ^ 2) :
    p ≤ ε / ((1 - Real.sqrt a) ^ 2 + ε) := by
  apply (le_div_iff₀ hden).2
  simpa only [mul_comm] using stationary_measurement_product a ε p ha ha1 hε hp hp1 h

/-- 在任意指定正达到点上的精确全局包络。 -/
theorem scaled_power_envelope (P k t S : ℝ)
    (hP : 0 ≤ P) (hk : 0 ≤ k) (ht : 0 < t) (hS : 0 ≤ S) :
    ((1 + k) * P * t ^ k) * S - P * S ^ (1 + k) ≤
      k * P * t ^ (1 + k) := by
  have h := normalized_power_envelope k (S / t) hk (by positivity)
  have hm := mul_le_mul_of_nonneg_left h
    (show 0 ≤ P * t ^ (1 + k) by positivity)
  rw [Real.div_rpow hS (le_of_lt ht)] at hm
  have htne : t ≠ 0 := ne_of_gt ht
  have hpowne : t ^ (1 + k) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ht _)
  have hpow : t ^ (1 + k) = t * t ^ k := by
    rw [Real.rpow_add ht, Real.rpow_one]
  have heq : P * t ^ (1 + k) *
      ((1 + k) * (S / t) - S ^ (1 + k) / t ^ (1 + k)) =
      ((1 + k) * P * t ^ k) * S - P * S ^ (1 + k) := by
    field_simp
    rw [hpow]
    ring
  rw [heq] at hm
  nlinarith

/-- 两幂次竞争的正最优尺度。 -/
def optimalScale (P Q k : ℝ) : ℝ := (Q / ((1 + k) * P)) ^ k⁻¹

/-- 论文中的精确标量包络 `D_k`。 -/
def scalarEnvelope (P Q k : ℝ) : ℝ :=
  k * P * (Q / ((1 + k) * P)) ^ ((1 + k) / k)

theorem optimal_scale_pos (P Q k : ℝ) (hP : 0 < P) (hQ : 0 < Q)
    (hk : 0 < k) : 0 < optimalScale P Q k := by
  unfold optimalScale
  positivity

theorem optimal_scale_power (P Q k : ℝ) (hP : 0 < P) (hQ : 0 < Q)
    (hk : 0 < k) : (optimalScale P Q k) ^ k = Q / ((1 + k) * P) := by
  unfold optimalScale
  exact Real.rpow_inv_rpow (by positivity) (ne_of_gt hk)

theorem optimal_scale_power_add (P Q k : ℝ) (hP : 0 < P) (hQ : 0 < Q)
    (hk : 0 < k) :
    (optimalScale P Q k) ^ (1 + k) =
      (Q / ((1 + k) * P)) ^ ((1 + k) / k) := by
  unfold optimalScale
  rw [← Real.rpow_mul (by positivity)]
  congr 1
  ring

/-- 全部非负 `S` 上的真实上界；主要结论不是输入假设。 -/
theorem scalar_envelope_bound (P Q k S : ℝ)
    (hP : 0 < P) (hQ : 0 < Q) (hk : 0 < k) (hS : 0 ≤ S) :
    Q * S - P * S ^ (1 + k) ≤ scalarEnvelope P Q k := by
  have hcrit : (1 + k) * P * (optimalScale P Q k) ^ k = Q := by
    rw [optimal_scale_power P Q k hP hQ hk]
    field_simp
  have h := scaled_power_envelope P k (optimalScale P Q k) S
    hP.le hk.le (optimal_scale_pos P Q k hP hQ hk) hS
  rw [hcrit, optimal_scale_power_add P Q k hP hQ hk] at h
  exact h

/-- 同一显式尺度使包络取等。 -/
theorem scalar_envelope_attains (P Q k : ℝ)
    (hP : 0 < P) (hQ : 0 < Q) (hk : 0 < k) :
    Q * optimalScale P Q k - P * (optimalScale P Q k) ^ (1 + k) =
      scalarEnvelope P Q k := by
  have ht := optimal_scale_pos P Q k hP hQ hk
  have hcrit : (1 + k) * P * (optimalScale P Q k) ^ k = Q := by
    rw [optimal_scale_power P Q k hP hQ hk]
    field_simp
  have hpow : (optimalScale P Q k) ^ (1 + k) =
      optimalScale P Q k * (optimalScale P Q k) ^ k := by
    rw [Real.rpow_add ht, Real.rpow_one]
  unfold scalarEnvelope
  rw [← optimal_scale_power_add P Q k hP hQ hk]
  rw [hpow]
  nlinarith [congrArg (fun x : ℝ => x * optimalScale P Q k) hcrit]

theorem optimal_scale_lt_one (P Q k : ℝ)
    (hP : 0 < P) (hQ : 0 < Q) (hQP : Q < P) (hk : 0 < k) :
    optimalScale P Q k < 1 := by
  have hb : 0 < Q / ((1 + k) * P) := by positivity
  have hbl : Q / ((1 + k) * P) < 1 := by
    apply (div_lt_one (by positivity)).2
    nlinarith
  unfold optimalScale
  calc
    _ < (1 : ℝ) ^ k⁻¹ := Real.rpow_lt_rpow hb.le hbl (by positivity)
    _ = 1 := Real.one_rpow _

/-- 因而论文中的区间最大值是正式的 `IsGreatest`，不只是候选驻点。 -/
theorem scalar_envelope_isGreatest (P Q k : ℝ)
    (hP : 0 < P) (hQ : 0 < Q) (hQP : Q < P) (hk : 0 < k) :
    IsGreatest ((fun S : ℝ => Q * S - P * S ^ (1 + k)) '' Set.Icc 0 1)
      (scalarEnvelope P Q k) := by
  constructor
  · refine ⟨optimalScale P Q k, ?_, scalar_envelope_attains P Q k hP hQ hk⟩
    exact ⟨(optimal_scale_pos P Q k hP hQ hk).le,
      (optimal_scale_lt_one P Q k hP hQ hQP hk).le⟩
  · intro y hy
    rcases hy with ⟨S, hS, rfl⟩
    exact scalar_envelope_bound P Q k S hP hQ hk hS.1

/-- 显式重置构造中两个指数模在所选尺度的精确负瞬态。 -/
theorem reset_two_modes_at_optimum (A k : ℝ) (hA : 1 < A) (hk : 0 < k) :
    A * (optimalScale A (A - 1) k) ^ (1 + k) -
      (A - 1) * optimalScale A (A - 1) k =
      -k * A * (optimalScale A (A - 1) k) ^ (1 + k) := by
  have hAp : 0 < A := by linarith
  have hQp : 0 < A - 1 := by linarith
  have h := scalar_envelope_attains A (A - 1) k hAp hQp hk
  unfold scalarEnvelope at h
  rw [← optimal_scale_power_add A (A - 1) k hAp hQp hk] at h
  linarith

/-- 对应 `B ≥ A` 速率区域的一致负瞬态上界，前提仅为已分离的标量核估计。 -/
theorem reverse_rate_scalar_bound (q A Δ R : ℝ) (hR : 0 < R)
    (hkernel : Real.exp (-A) * (Δ - R * (A + 1)) ≤ q) :
    max (-q) 0 ≤ R * Real.exp (-Δ / R) := by
  let x : ℝ := A + 1 - Δ / R
  have h := Real.mul_exp_neg_le_exp_neg_one x
  have hm := mul_le_mul_of_nonneg_left h
    (show 0 ≤ R * Real.exp (1 - Δ / R) by positivity)
  have hidentity : Real.exp (-A) * (R * (A + 1) - Δ) =
      (R * Real.exp (1 - Δ / R)) * (x * Real.exp (-x)) := by
    calc
      _ = R * x * Real.exp (-A) := by dsimp [x]; field_simp
      _ = R * x * (Real.exp (1 - Δ / R) * Real.exp (-x)) := by
        rw [← Real.exp_add]
        congr 2
        dsimp [x]
        ring
      _ = _ := by ring
  have hfinal : (R * Real.exp (1 - Δ / R)) * Real.exp (-1) =
      R * Real.exp (-Δ / R) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 1
    congr 1
    ring
  rw [← hidentity, hfinal] at hm
  apply max_le
  · nlinarith
  · positivity

/-- 以 `δ=1-k` 写出的退化前因子 `H(k)`，仍使用原始实幂表达式。 -/
def shape (δ : ℝ) : ℝ :=
  (1 - δ) * (2 * Real.sqrt (δ / (2 - δ)) / (1 - δ)) ^ ((2 - δ) / (1 - δ))

/-- 主文原始记号中的 `H(k)`，保留平方根和实幂。 -/
def purePrefactor (k : ℝ) : ℝ :=
  k * (2 * Real.sqrt (1 - k ^ 2) / (k * (1 + k))) ^ ((1 + k) / k)

/-- 验证参数替换确实连接主文函数，未另造具有所需极限的替代函数。 -/
theorem pure_prefactor_shape (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    purePrefactor (1 - δ) = shape δ := by
  have hu : 0 < 1 - δ := by linarith
  have hv : 0 < 2 - δ := by linarith
  have hss : Real.sqrt (1 - (1 - δ) ^ 2) =
      (2 - δ) * Real.sqrt (δ / (2 - δ)) := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by nlinarith), mul_pow, Real.sq_sqrt (by positivity)]
    field_simp
    ring
  have hLambda : 1 + (1 - δ) = 2 - δ := by ring
  have hbase : 2 * Real.sqrt (1 - (1 - δ) ^ 2) / ((1 - δ) * (1 + (1 - δ))) =
      2 * Real.sqrt (δ / (2 - δ)) / (1 - δ) := by
    rw [hss, hLambda]
    field_simp
  unfold purePrefactor shape
  rw [hbase, hLambda]

/-- 对数中的可去奇点表达式；`δ log δ` 在零点连续。 -/
def shapeLogCorrection (δ : ℝ) : ℝ :=
  (δ * Real.log δ / 2 + Real.log 2 -
    (2 - δ) / 2 * Real.log (2 - δ) - Real.log (1 - δ)) / (1 - δ)

theorem shape_normalized_exact (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    shape δ / (2 * δ) = Real.exp (shapeLogCorrection δ) := by
  have hu : 0 < 1 - δ := by linarith
  have hv : 0 < 2 - δ := by linarith
  have hx : 0 < δ / (2 - δ) := by positivity
  have hs : 0 < Real.sqrt (δ / (2 - δ)) := Real.sqrt_pos.2 hx
  have hb : 0 < 2 * Real.sqrt (δ / (2 - δ)) / (1 - δ) := by positivity
  have hpos : 0 < shape δ / (2 * δ) := by unfold shape; positivity
  rw [← Real.exp_log hpos]
  congr 1
  unfold shape shapeLogCorrection
  rw [Real.log_div (by positivity) (by positivity)]
  rw [Real.log_mul (ne_of_gt hu) (ne_of_gt (Real.rpow_pos_of_pos hb _))]
  rw [Real.log_rpow hb]
  rw [Real.log_div (by positivity) (ne_of_gt hu)]
  rw [Real.log_mul (by norm_num) (ne_of_gt hs)]
  rw [Real.log_sqrt hx.le]
  rw [Real.log_div (ne_of_gt hδ) (ne_of_gt hv)]
  rw [Real.log_mul (by norm_num) (ne_of_gt hδ)]
  field_simp
  ring

theorem shape_log_correction_zero : shapeLogCorrection 0 = 0 := by
  unfold shapeLogCorrection
  norm_num

theorem shape_log_correction_continuous : ContinuousAt shapeLogCorrection 0 := by
  unfold shapeLogCorrection
  have hml : ContinuousAt (fun δ : ℝ => δ * Real.log δ) 0 :=
    Real.continuous_mul_log.continuousAt
  apply ContinuousAt.div
  · apply ContinuousAt.sub
    · apply ContinuousAt.sub
      · exact (hml.div_const 2).add continuousAt_const
      · fun_prop (disch := norm_num)
    · fun_prop (disch := norm_num)
  · fun_prop
  · norm_num

/-- 该极限验证 `H(1-δ)/(2δ)→1`，包含趋零实幂前因子。 -/
theorem shape_normalized_limit :
    Tendsto (fun δ : ℝ => shape δ / (2 * δ)) (𝓝[>] 0) (𝓝 1) := by
  have hc : Tendsto (fun δ : ℝ => Real.exp (shapeLogCorrection δ))
      (𝓝 0) (𝓝 1) := by
    simpa only [Function.comp_def, shape_log_correction_zero, Real.exp_zero] using
      (Real.continuous_exp.continuousAt.comp shape_log_correction_continuous).tendsto
  have h := hc.mono_left
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  apply h.congr'
  filter_upwards [eventually_mem_nhdsWithin,
    (show ∀ᶠ δ : ℝ in 𝓝[>] 0, δ < 1 from
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds)]
    with δ hδ hδ1
  exact (shape_normalized_exact δ hδ hδ1).symm

/-- 解析构造中领先相对改进 `G₀(L)` 的精确标量表达式。 -/
def resetGain (L : ℝ) : ℝ :=
  shape (2 / L) * Real.exp (-1 / (1 - 2 / L))

theorem reset_gain_eq_prefactor (L : ℝ) (hL : 2 < L) :
    resetGain L = purePrefactor (1 - 2 / L) * Real.exp (-1 / (1 - 2 / L)) := by
  have hLp : 0 < L := by linarith
  unfold resetGain
  rw [pure_prefactor_shape (2 / L) (by positivity) ((div_lt_one hLp).2 hL)]

theorem scaled_reset_gain_exact (L : ℝ) (hL : 2 < L) :
    L * resetGain L =
      4 * Real.exp (shapeLogCorrection (2 / L)) *
        Real.exp (-1 / (1 - 2 / L)) := by
  have hLpos : 0 < L := by linarith
  have hδ : 0 < 2 / L := by positivity
  have hδ1 : 2 / L < 1 := (div_lt_one hLpos).2 hL
  have hnorm := shape_normalized_exact (2 / L) hδ hδ1
  have hscale : L * shape (2 / L) = 4 * Real.exp (shapeLogCorrection (2 / L)) := by
    have hn : L ≠ 0 := ne_of_gt hLpos
    field_simp at hnorm
    nlinarith
  unfold resetGain
  rw [← mul_assoc, hscale]

/-- 对数构造的解析领先项确实具有 `4/e` 极限；不是数值拟合。 -/
theorem scaled_reset_gain_limit :
    Tendsto (fun L : ℝ => L * resetGain L) atTop (𝓝 (4 / Real.exp 1)) := by
  have hδ : Tendsto (fun L : ℝ => 2 / L) atTop (𝓝 0) :=
    tendsto_id.const_div_atTop 2
  have hc : ContinuousAt
      (fun δ : ℝ => 4 * Real.exp (shapeLogCorrection δ) * Real.exp (-1 / (1 - δ))) 0 := by
    have hcor := shape_log_correction_continuous
    fun_prop (disch := norm_num)
  have h := hc.tendsto.comp hδ
  have hvalue : 4 * Real.exp (shapeLogCorrection 0) * Real.exp (-1 / (1 - 0)) =
      4 / Real.exp 1 := by
    rw [shape_log_correction_zero]
    simp [Real.exp_neg, div_eq_mul_inv]
  rw [hvalue] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with L hL
  exact (scaled_reset_gain_exact L hL).symm

/-- 固定紧区间上的粗界足以控制远离退化端点的指数尾部。 -/
theorem shape_bounded (δ : ℝ) (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) :
    0 ≤ shape δ ∧ shape δ ≤ 256 := by
  have hu : 0 < 1 - δ := by linarith
  have hv : 0 < 2 - δ := by linarith
  have hx : 0 < δ / (2 - δ) := by positivity
  have hxl : δ / (2 - δ) ≤ 1 := (div_le_one hv).2 (by linarith)
  have hs : Real.sqrt (δ / (2 - δ)) ≤ 1 := by
    have hsq := Real.sq_sqrt hx.le
    have hsn := Real.sqrt_nonneg (δ / (2 - δ))
    nlinarith
  have hb : 0 < 2 * Real.sqrt (δ / (2 - δ)) / (1 - δ) := by positivity
  have hbl : 2 * Real.sqrt (δ / (2 - δ)) / (1 - δ) ≤ 4 := by
    apply (div_le_iff₀ hu).2
    nlinarith
  have he0 : 0 ≤ (2 - δ) / (1 - δ) := by positivity
  have he4 : (2 - δ) / (1 - δ) ≤ 4 := by
    apply (div_le_iff₀ hu).2
    linarith
  have hp : (2 * Real.sqrt (δ / (2 - δ)) / (1 - δ)) ^ ((2 - δ) / (1 - δ)) ≤ 256 := by
    calc
      _ ≤ (4 : ℝ) ^ ((2 - δ) / (1 - δ)) :=
        Real.rpow_le_rpow hb.le hbl he0
      _ ≤ (4 : ℝ) ^ (4 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) he4
      _ = 256 := by norm_num
  constructor
  · unfold shape; positivity
  · unfold shape
    calc
      _ ≤ 1 * 256 := mul_le_mul (by linarith : 1 - δ ≤ 1) hp (by positivity) (by norm_num)
      _ = 256 := by norm_num

theorem decay_exponent_comparison (L δ : ℝ)
    (hL : 0 ≤ L) (_hδ : 0 ≤ δ) (hδ1 : δ < 1) :
    Real.exp (-(δ * L / (2 * (1 - δ)))) ≤ Real.exp (-(δ * L / 2)) := by
  apply Real.exp_le_exp.mpr
  have hdiv : δ * L / 2 ≤ δ * L / (2 * (1 - δ)) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * (1 - δ))).2
    nlinarith [mul_nonneg hL (sq_nonneg δ)]
  exact neg_le_neg hdiv

theorem scaled_profile_bound (L δ : ℝ) (hL : 0 < L) :
    L * (2 * δ * Real.exp (-(δ * L / 2))) ≤ 4 / Real.exp 1 := by
  have h := mul_le_mul_of_nonneg_left (logarithmic_profile_bound L δ hL) hL.le
  have hn : L ≠ 0 := ne_of_gt hL
  convert h using 1 <;> field_simp

/-- 对全部退化参数的一致 `4/e` 包络，不是仅沿指定参数序列的极限。 -/
theorem shape_uniform_bound (η : ℝ) (hη : 0 < η) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      L * shape δ * Real.exp (-(δ * L / (2 * (1 - δ)))) ≤ 4 / Real.exp 1 + η := by
  let c : ℝ := η * Real.exp 1 / 4
  have hc : 0 < c := by dsimp [c]; positivity
  have hev : ∀ᶠ δ : ℝ in 𝓝[>] 0, shape δ / (2 * δ) < 1 + c :=
    shape_normalized_limit.eventually (eventually_lt_nhds (by linarith : (1 : ℝ) < 1 + c))
  obtain ⟨d, hd, hsmall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have hdpos : 0 < d := hd
  have htail : Tendsto (fun L : ℝ => 256 * L * Real.exp (-(d * L / 2))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) (d / 2)
      (by positivity)).const_mul 256
    have heq : (fun L : ℝ => 256 * L * Real.exp (-(d * L / 2))) =
        (fun L : ℝ => 256 * (L * Real.exp (-(d / 2) * L))) := by
      funext L
      have he : -(d * L / 2) = -(d / 2) * L := by ring
      rw [he]
      ring
    rw [heq]
    simpa only [Real.rpow_one, mul_zero] using h
  have hevent : ∀ᶠ L : ℝ in atTop,
      256 * L * Real.exp (-(d * L / 2)) < 4 / Real.exp 1 + η :=
    htail.eventually (eventually_lt_nhds (by positivity))
  obtain ⟨L₀, hlarge⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨max 1 L₀, ?_⟩
  intro L hL δ hδ hδh
  have hL1 : 1 ≤ L := (le_max_left 1 L₀).trans hL
  have hLL : L₀ ≤ L := (le_max_right 1 L₀).trans hL
  have hLp : 0 < L := by linarith
  have hδ1 : δ < 1 := by linarith
  have hshape := (shape_bounded δ hδ hδh).1
  have hdecay := decay_exponent_comparison L δ hLp.le hδ.le hδ1
  by_cases hδd : δ < d
  · have hs : shape δ ≤ 2 * δ * (1 + c) := by
      have h := hsmall (show δ ∈ Set.Ioo 0 d from ⟨hδ, hδd⟩)
      have h' := (div_lt_iff₀ (by positivity : 0 < 2 * δ)).mp h
      nlinarith
    calc
      _ ≤ L * (2 * δ * (1 + c)) * Real.exp (-(δ * L / 2)) := by
        gcongr
      _ = (1 + c) * (L * (2 * δ * Real.exp (-(δ * L / 2)))) := by ring
      _ ≤ (1 + c) * (4 / Real.exp 1) :=
        mul_le_mul_of_nonneg_left (scaled_profile_bound L δ hLp) (by positivity)
      _ = 4 / Real.exp 1 + η := by dsimp [c]; field_simp
  · have hdd : d ≤ δ := le_of_not_gt hδd
    have he : Real.exp (-(δ * L / 2)) ≤ Real.exp (-(d * L / 2)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hdd hLp.le]
    calc
      _ ≤ L * 256 * Real.exp (-(d * L / 2)) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (shape_bounded δ hδ hδh).2 hLp.le)
          (hdecay.trans he) (Real.exp_nonneg _) (by positivity)
      _ = 256 * L * Real.exp (-(d * L / 2)) := by ring
      _ ≤ 4 / Real.exp 1 + η := (hlarge L hLL).le

/-- 以上一致包络以论文原始 `k` 变量表述。 -/
theorem pure_prefactor_uniform_bound (η : ℝ) (hη : 0 < η) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ k : ℝ, 1 / 2 ≤ k → k < 1 →
      L * purePrefactor k * Real.exp (-((1 - k) * L / (2 * k))) ≤
        4 / Real.exp 1 + η := by
  obtain ⟨L₀, hL₀⟩ := shape_uniform_bound η hη
  refine ⟨L₀, ?_⟩
  intro L hL k hk hk1
  have hδ : 0 < 1 - k := by linarith
  have hδ1 : 1 - k < 1 := by linarith
  have heq : purePrefactor k = shape (1 - k) := by
    simpa only [sub_sub_cancel] using pure_prefactor_shape (1 - k) hδ hδ1
  have h := hL₀ L hL (1 - k) hδ (by linarith)
  rw [← heq] at h
  simpa only [sub_sub_cancel] using h

#print axioms logarithmic_profile_bound
#print axioms stationary_measurement_product
#print axioms scalar_envelope_bound
#print axioms scalar_envelope_attains
#print axioms scalar_envelope_isGreatest
#print axioms reset_two_modes_at_optimum
#print axioms reverse_rate_scalar_bound
#print axioms shape_normalized_limit
#print axioms scaled_reset_gain_limit
#print axioms reset_gain_eq_prefactor
#print axioms shape_uniform_bound
#print axioms pure_prefactor_shape
#print axioms pure_prefactor_uniform_bound

end Reset
