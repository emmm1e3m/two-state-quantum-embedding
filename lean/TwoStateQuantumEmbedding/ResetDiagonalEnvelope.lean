import TwoStateQuantumEmbedding.ResetDiagonalScalar
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section
open Filter Topology
namespace TwoStateQuantumEmbedding.ResetDiagonalEnvelope
/-- 稿件的实际速率比前因子，保留原始实幂公式。 -/
def diagonalF (τ : ℝ) : ℝ :=
  (1 - τ) / 2 * ((1 + τ) / 2) ^ ((1 + τ) / (1 - τ)) *
    (8 * τ / (1 - τ) ^ 2) ^ (2 / (1 - τ))

def diagonalLogCorrection (τ : ℝ) : ℝ :=
  (2 * (τ * Real.log τ) + 4 * τ * Real.log 2 +
    (1 + τ) * Real.log (1 + τ) - (3 + τ) * Real.log (1 - τ)) / (1 - τ)

theorem diagonalF_normalized_exact (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ < 1) :
    diagonalF τ / (16 * τ ^ 2) = Real.exp (diagonalLogCorrection τ) := by
  have hu : 0 < 1 - τ := by linarith
  have hv : 0 < 1 + τ := by linarith
  have hb : 0 < (1 + τ) / 2 := by positivity
  have hc : 0 < 8 * τ / (1 - τ) ^ 2 := by positivity
  have hpos : 0 < diagonalF τ / (16 * τ ^ 2) := by unfold diagonalF; positivity
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 3
    norm_num at h
    exact h
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 4
    norm_num at h
    exact h
  rw [← Real.exp_log hpos]
  congr 1
  unfold diagonalF diagonalLogCorrection
  rw [Real.log_div (by positivity) (by positivity)]
  rw [Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_div (by positivity) (by norm_num)]
  rw [Real.log_rpow hb, Real.log_rpow hc]
  rw [Real.log_div (by positivity) (by norm_num)]
  rw [Real.log_div (by positivity) (by positivity)]
  rw [Real.log_mul (by norm_num) (ne_of_gt hτ), Real.log_pow]
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  rw [h8, h16]
  field_simp
  <;> ring

theorem diagonal_log_correction_zero : diagonalLogCorrection 0 = 0 := by
  simp [diagonalLogCorrection]

theorem diagonal_log_correction_continuous : ContinuousAt diagonalLogCorrection 0 := by
  unfold diagonalLogCorrection
  have hml : ContinuousAt (fun τ : ℝ => τ * Real.log τ) 0 :=
    Real.continuous_mul_log.continuousAt
  fun_prop (disch := norm_num)

/-- 真正的原始前因子满足 F(τ)/(16τ²)→1。 -/
theorem diagonalF_normalized_limit :
    Tendsto (fun τ : ℝ => diagonalF τ / (16 * τ ^ 2)) (𝓝[>] 0) (𝓝 1) := by
  have hc : Tendsto (fun τ : ℝ => Real.exp (diagonalLogCorrection τ))
      (𝓝 0) (𝓝 1) := by
    simpa only [Function.comp_def, diagonal_log_correction_zero, Real.exp_zero] using
      (Real.continuous_exp.continuousAt.comp diagonal_log_correction_continuous).tendsto
  have h := hc.mono_left
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  apply h.congr'
  filter_upwards [eventually_mem_nhdsWithin,
    (show ∀ᶠ τ : ℝ in 𝓝[>] 0, τ < 1 from
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds)]
      with τ hτ hτ1
  exact (diagonalF_normalized_exact τ hτ hτ1).symm

theorem diagonalF_bounded (τ : ℝ) (hτ : 0 < τ) (hτh : τ ≤ 1 / 2) :
    0 ≤ diagonalF τ ∧ diagonalF τ ≤ 65536 := by
  have hu : 0 < 1 - τ := by linarith
  have hb : 0 < (1 + τ) / 2 := by positivity
  have hbl : (1 + τ) / 2 ≤ 1 := by linarith
  have hc : 0 < 8 * τ / (1 - τ) ^ 2 := by positivity
  have hcl : 8 * τ / (1 - τ) ^ 2 ≤ 16 := by
    apply (div_le_iff₀ (by positivity : 0 < (1 - τ) ^ 2)).2
    nlinarith [sq_nonneg (τ - 1 / 2)]
  have he0 : 0 ≤ 2 / (1 - τ) := by positivity
  have he4 : 2 / (1 - τ) ≤ 4 := by
    apply (div_le_iff₀ hu).2
    linarith
  have hp : ((1 + τ) / 2) ^ ((1 + τ) / (1 - τ)) ≤ 1 := by
    calc
      _ ≤ (1 : ℝ) ^ ((1 + τ) / (1 - τ)) :=
        Real.rpow_le_rpow hb.le hbl (by positivity)
      _ = 1 := Real.one_rpow _
  have hq : (8 * τ / (1 - τ) ^ 2) ^ (2 / (1 - τ)) ≤ 65536 := by
    calc
      _ ≤ (16 : ℝ) ^ (2 / (1 - τ)) := Real.rpow_le_rpow hc.le hcl he0
      _ ≤ (16 : ℝ) ^ (4 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) he4
      _ = 65536 := by norm_num
  constructor
  · unfold diagonalF; positivity
  · unfold diagonalF
    have hfirst : (1 - τ) / 2 * ((1 + τ) / 2) ^ ((1 + τ) / (1 - τ)) ≤ 1 := by
      calc
        _ ≤ 1 * 1 := mul_le_mul (by linarith) hp (by positivity) (by norm_num)
        _ = 1 := by norm_num
    calc
      (1 - τ) / 2 * ((1 + τ) / 2) ^ ((1 + τ) / (1 - τ)) *
          (8 * τ / (1 - τ) ^ 2) ^ (2 / (1 - τ)) ≤ 1 * 65536 :=
        mul_le_mul hfirst hq (by positivity) (by norm_num)
      _ = 65536 := by norm_num

/-- 二次指数核的全局最优常数。 -/
theorem quadratic_profile_bound (L τ : ℝ) (hL : 0 < L) (hτ : 0 ≤ τ) :
    L ^ 2 * (16 * τ ^ 2 * Real.exp (-(τ * L))) ≤ 64 / (Real.exp 1) ^ 2 := by
  let y : ℝ := τ * L / 2
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have h := Real.mul_exp_neg_le_exp_neg_one y
  have hs := (sq_le_sq₀ (mul_nonneg hy (Real.exp_nonneg _)) (Real.exp_nonneg _)).2 h
  have he : Real.exp (-(τ * L)) = Real.exp (-y) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp [y]
    ring
  rw [he]
  rw [Real.exp_neg 1] at hs
  have hm := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 64)
  dsimp [y] at *
  convert hm using 1 <;> ring

theorem diagonal_decay_comparison (L τ : ℝ) (hL : 0 ≤ L)
    (hτ : 0 ≤ τ) (hτ1 : τ < 1) :
    Real.exp (-(τ * L / (1 - τ))) ≤ Real.exp (-(τ * L)) := by
  apply Real.exp_le_exp.mpr
  have hdiv : τ * L ≤ τ * L / (1 - τ) := by
    apply (le_div_iff₀ (by positivity : 0 < 1 - τ)).2
    nlinarith [mul_nonneg hL (sq_nonneg τ)]
  exact neg_le_neg hdiv

/-- 对稿件实际 F 的全比值区间一致优化，不是固定 τ 的点态极限。 -/
theorem diagonalF_uniform_bound (η : ℝ) (hη : 0 < η) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
      L ^ 2 * diagonalF τ * Real.exp (-(τ * L / (1 - τ))) ≤
        64 / (Real.exp 1) ^ 2 + η := by
  let c : ℝ := η * (Real.exp 1) ^ 2 / 64
  have hc : 0 < c := by dsimp [c]; positivity
  have hev : ∀ᶠ τ : ℝ in 𝓝[>] 0, diagonalF τ / (16 * τ ^ 2) < 1 + c :=
    diagonalF_normalized_limit.eventually
      (eventually_lt_nhds (by linarith : (1 : ℝ) < 1 + c))
  obtain ⟨d, hd, hsmall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have htail : Tendsto (fun L : ℝ => 65536 * L ^ 2 * Real.exp (-(d * L)))
      atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 : ℝ) d hd).const_mul 65536
    convert h using 1 <;> simp only [Real.rpow_two, mul_zero] <;> congr 1
    funext L
    ring
  have hevent : ∀ᶠ L : ℝ in atTop,
      65536 * L ^ 2 * Real.exp (-(d * L)) < 64 / (Real.exp 1) ^ 2 + η :=
    htail.eventually (eventually_lt_nhds (by positivity))
  obtain ⟨L₀, hlarge⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨max 1 L₀, ?_⟩
  intro L hL τ hτ hτh
  have hL1 : 1 ≤ L := (le_max_left 1 L₀).trans hL
  have hLL : L₀ ≤ L := (le_max_right 1 L₀).trans hL
  have hLp : 0 < L := by linarith
  have hτ1 : τ < 1 := by linarith
  have hF := (diagonalF_bounded τ hτ hτh).1
  have hdecay := diagonal_decay_comparison L τ hLp.le hτ.le hτ1
  by_cases hτd : τ < d
  · have hs : diagonalF τ ≤ 16 * τ ^ 2 * (1 + c) := by
      have h := hsmall (show τ ∈ Set.Ioo 0 d from ⟨hτ, hτd⟩)
      nlinarith [(div_lt_iff₀ (by positivity : 0 < 16 * τ ^ 2)).mp h]
    calc
      _ ≤ L ^ 2 * (16 * τ ^ 2 * (1 + c)) * Real.exp (-(τ * L)) := by gcongr
      _ = (1 + c) * (L ^ 2 * (16 * τ ^ 2 * Real.exp (-(τ * L)))) := by ring
      _ ≤ (1 + c) * (64 / (Real.exp 1) ^ 2) :=
        mul_le_mul_of_nonneg_left (quadratic_profile_bound L τ hLp hτ.le) (by positivity)
      _ = 64 / (Real.exp 1) ^ 2 + η := by dsimp [c]; field_simp
  · have hdd : d ≤ τ := le_of_not_gt hτd
    have he : Real.exp (-(τ * L)) ≤ Real.exp (-(d * L)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hdd hLp.le]
    calc
      _ ≤ L ^ 2 * 65536 * Real.exp (-(d * L)) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left (diagonalF_bounded τ hτ hτh).2 (sq_nonneg L))
          (hdecay.trans he) (Real.exp_nonneg _) (by positivity)
      _ = 65536 * L ^ 2 * Real.exp (-(d * L)) := by ring
      _ ≤ 64 / (Real.exp 1) ^ 2 + η := (hlarge L hLL).le

/-- 正比较矩阵的无量纲相干阻尼与反馈乘积。 -/
def zeta (χ τ : ℝ) : ℝ := ((1 - χ) ^ 2 + τ) / (2 * (1 + χ ^ 2))
def feedback (χ τ : ℝ) : ℝ := 2 * χ * τ / ((1 - χ) ^ 2 * (1 + χ ^ 2))
def spectralGap (z h : ℝ) : ℝ := Real.sqrt ((1 - z) ^ 2 + 4 * h)
def slowRate (z h : ℝ) : ℝ := (1 + z - spectralGap z h) / 2
def fastRate (z h : ℝ) : ℝ := (1 + z + spectralGap z h) / 2
def slowWeight (z h : ℝ) : ℝ := (spectralGap z h + z - 1) / (2 * spectralGap z h)
def positivePopulation (z h x : ℝ) : ℝ :=
  (1 - slowWeight z h) * Real.exp (-fastRate z h * x) +
    slowWeight z h * Real.exp (-slowRate z h * x)

theorem spectral_ranges (z h : ℝ) (hz : 0 < z) (hz1 : z < 1)
    (hh : 0 < h) (hhz : h < z) :
    0 < slowRate z h ∧ slowRate z h < 1 ∧ 1 < fastRate z h ∧
      0 < slowWeight z h ∧ slowWeight z h < 1 := by
  have hr : 0 ≤ (1 - z) ^ 2 + 4 * h := by positivity
  have hs := Real.sq_sqrt hr
  have hn := Real.sqrt_nonneg ((1 - z) ^ 2 + 4 * h)
  have hg : 1 - z < spectralGap z h := by unfold spectralGap; nlinarith
  have hgp : 0 < spectralGap z h := by linarith
  have hgu : spectralGap z h < 1 + z := by unfold spectralGap; nlinarith
  unfold slowRate fastRate slowWeight
  refine ⟨by linarith, by linarith, by linarith, ?_, ?_⟩
  · apply div_pos <;> linarith
  · apply (div_lt_one (by positivity : 0 < 2 * spectralGap z h)).2
    linarith

/-- 正比较谱解自身给出精确 D0 包络。 -/
theorem positive_population_scalar_bound (q z h x : ℝ)
    (hz : 0 < z) (hz1 : z < 1) (hh : 0 < h) (hhz : h < z) (hx : 0 ≤ x)
    (hq : 2 * Real.exp (-x) - positivePopulation z h x ≤ q) :
    max (-q) 0 ≤ scalarD0 (slowRate z h) (slowWeight z h) := by
  obtain ⟨hs, hs1, hf, hd, hd1⟩ := spectral_ranges z h hz hz1 hh hhz
  apply signed_population_scalar_bound q (slowRate z h) (slowWeight z h) x hs hs1 hd
  have he : Real.exp (-fastRate z h * x) ≤ Real.exp (-x) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hf.le hx]
  have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ 1 - slowWeight z h by linarith)
  unfold positivePopulation at hq
  linarith

/-- 权重的有理化形式避免 τ→0 的消去误差。 -/
theorem slowWeight_rationalized (z h : ℝ) (hz1 : z < 1) (hh : 0 < h) :
    slowWeight z h =
      2 * h / (spectralGap z h * (spectralGap z h + (1 - z))) := by
  have hsq : (spectralGap z h) ^ 2 = (1 - z) ^ 2 + 4 * h :=
    Real.sq_sqrt (by positivity)
  have hg : 0 < spectralGap z h := by unfold spectralGap; apply Real.sqrt_pos.2; positivity
  have hgs : spectralGap z h + (1 - z) ≠ 0 := by positivity
  unfold slowWeight
  field_simp
  nlinarith

/-- β 相对零 χ 值的精确差，误差中的 χ 因子未被隐藏。 -/
def rateCorrection (χ τ : ℝ) : ℝ :=
  (2 + τ * χ) / (2 * (1 + χ ^ 2)) +
    4 * τ / ((1 - χ) ^ 2 * (1 + χ ^ 2) *
      (spectralGap (zeta χ τ) (feedback χ τ) + (1 - zeta χ τ)))

def weightScale (χ τ : ℝ) : ℝ :=
  4 / ((1 - χ) ^ 2 * (1 + χ ^ 2) * spectralGap (zeta χ τ) (feedback χ τ) *
    (spectralGap (zeta χ τ) (feedback χ τ) + (1 - zeta χ τ)))

theorem zeta_exact (χ τ : ℝ) :
    zeta χ τ = (1 + τ) / 2 - χ * ((2 + τ * χ) / (2 * (1 + χ ^ 2))) := by
  unfold zeta
  have hn : 1 + χ ^ 2 ≠ 0 := by positivity
  field_simp
  <;> ring

/-- 固定小 χ 阈值上的实际参数界；对全小速率比一致。 -/
theorem actual_parameter_bounds (χ τ : ℝ) (hχ : 0 < χ) (hχs : χ ≤ 1 / 100)
    (hτ : 0 < τ) (hτh : τ ≤ 1 / 2) :
    2 / 5 ≤ zeta χ τ ∧ zeta χ τ ≤ 3 / 4 ∧
      0 < feedback χ τ ∧ feedback χ τ ≤ 1 / 80 := by
  have hχ1 : χ < 1 := by linarith
  have hχn : 1 - χ ≠ 0 := by positivity
  have ha : 9 / 10 ≤ (1 - χ) ^ 2 := by nlinarith
  have hb : 1 ≤ 1 + χ ^ 2 := by nlinarith [sq_nonneg χ]
  have hab : 9 / 10 ≤ (1 - χ) ^ 2 * (1 + χ ^ 2) :=
    le_trans (by norm_num) (mul_le_mul ha hb (by norm_num) (by positivity))
  have hd : 0 < (1 - χ) ^ 2 * (1 + χ ^ 2) := by positivity
  have hprod : χ * τ ≤ 1 / 200 := by
    have h := mul_le_mul hχs hτh hτ.le (by norm_num : (0 : ℝ) ≤ 1 / 100)
    norm_num at h
    exact h
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold zeta
    apply (le_div_iff₀ (by positivity : 0 < 2 * (1 + χ ^ 2))).2
    nlinarith
  · rw [zeta_exact]
    have hn : 0 ≤ χ * ((2 + τ * χ) / (2 * (1 + χ ^ 2))) := by positivity
    linarith
  · unfold feedback; positivity
  · unfold feedback
    apply (div_le_iff₀ hd).2
    nlinarith

theorem actual_spectral_bounds (χ τ : ℝ) (hχ : 0 < χ) (hχs : χ ≤ 1 / 100)
    (hτ : 0 < τ) (hτh : τ ≤ 1 / 2) :
    1 / 3 ≤ slowRate (zeta χ τ) (feedback χ τ) ∧
      slowRate (zeta χ τ) (feedback χ τ) < 1 ∧
      0 < slowWeight (zeta χ τ) (feedback χ τ) ∧
      slowWeight (zeta χ τ) (feedback χ τ) < 1 := by
  obtain ⟨hzl, hzu, hhp, hhu⟩ := actual_parameter_bounds χ τ hχ hχs hτ hτh
  have hz : 0 < zeta χ τ := by linarith
  have hz1 : zeta χ τ < 1 := by linarith
  have hhz : feedback χ τ < zeta χ τ := by linarith
  obtain ⟨_, hs1, _, hdp, hdu⟩ := spectral_ranges _ _ hz hz1 hhp hhz
  refine ⟨?_, hs1, hdp, hdu⟩
  have hsq : spectralGap (zeta χ τ) (feedback χ τ) ^ 2 =
      (1 - zeta χ τ) ^ 2 + 4 * feedback χ τ := Real.sq_sqrt (by positivity)
  have hnon : 0 ≤ spectralGap (zeta χ τ) (feedback χ τ) := Real.sqrt_nonneg _
  unfold slowRate
  nlinarith

theorem weightScale_exact (χ τ : ℝ) (hz1 : zeta χ τ < 1)
    (hh : 0 < feedback χ τ) :
    slowWeight (zeta χ τ) (feedback χ τ) = χ * τ * weightScale χ τ := by
  rw [slowWeight_rationalized _ _ hz1 hh]
  unfold weightScale feedback
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem slowRate_rationalized (z h : ℝ) (hz1 : z < 1) (hh : 0 < h) :
    slowRate z h = z - 2 * h / (spectralGap z h + (1 - z)) := by
  have hsq : (spectralGap z h) ^ 2 = (1 - z) ^ 2 + 4 * h :=
    Real.sq_sqrt (by positivity)
  have hg : 0 < spectralGap z h := by unfold spectralGap; apply Real.sqrt_pos.2; positivity
  have hgs : spectralGap z h + (1 - z) ≠ 0 := by positivity
  unfold slowRate
  field_simp
  nlinarith

theorem rateCorrection_exact (χ τ : ℝ) (hz1 : zeta χ τ < 1)
    (hh : 0 < feedback χ τ) :
    slowRate (zeta χ τ) (feedback χ τ) = (1 + τ) / 2 - χ * rateCorrection χ τ := by
  rw [slowRate_rationalized _ _ hz1 hh]
  conv_lhs => lhs; rw [zeta_exact]
  unfold rateCorrection feedback
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem scalarD0_log (β d : ℝ) (hβ : 0 < β) (hβ1 : β < 1) (hd : 0 < d) :
    Real.log (scalarD0 β d) = Real.log (1 - β) +
      β / (1 - β) * Real.log β + 1 / (1 - β) * Real.log d -
      β / (1 - β) * Real.log (1 + d) := by
  unfold scalarD0
  rw [Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_rpow (by positivity)]
  rw [Real.log_div (by positivity) (by positivity)]
  rw [Real.log_mul (ne_of_gt hd) (ne_of_gt hβ)]
  have hn : 1 - β ≠ 0 := ne_of_gt (sub_pos.mpr hβ1)
  field_simp
  <;> ring

/-- 原始 D0 的统一幂指数控制；包含任意小 τ，无相对误差假设。 -/
theorem scalarD0_scaled_bound (T τ β w b : ℝ)
    (hT : 1 ≤ T) (hτ : 0 < τ) (hβ : 0 < β) (hβ1 : β < 1)
    (hw : 0 < w) (hb : 0 ≤ b)
    (hrelation : β = (1 + τ) / 2 - Real.exp (-T) * b) :
    scalarD0 β (w * τ * Real.exp (-T)) * T ^ 2 * Real.exp (2 * T) ≤
      ((1 - β) * β ^ (β / (1 - β)) * w ^ (1 / (1 - β)) *
        Real.exp (-1 / (1 - β))) *
          Real.exp (4 * b / (1 - β) * T * Real.exp (-T)) := by
  have hTp : 0 < T := by linarith
  have hden : 0 < 1 - β := by linarith
  have hp : 0 < 1 / (1 - β) := by positivity
  have hd : 0 < w * τ * Real.exp (-T) := by positivity
  have hD : 0 < scalarD0 β (w * τ * Real.exp (-T)) := scalarD0_pos β _ hβ hβ1 hd
  have hleft : 0 < scalarD0 β (w * τ * Real.exp (-T)) * T ^ 2 * Real.exp (2 * T) := by
    exact mul_pos (mul_pos (scalarD0_pos β _ hβ hβ1 hd) (sq_pos_of_pos hTp)) (Real.exp_pos _)
  have hright : 0 < ((1 - β) * β ^ (β / (1 - β)) * w ^ (1 / (1 - β)) *
        Real.exp (-1 / (1 - β))) *
          Real.exp (4 * b / (1 - β) * T * Real.exp (-T)) := by positivity
  rw [← Real.exp_log hleft, ← Real.exp_log hright]
  apply Real.exp_le_exp.mpr
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hlogTle : Real.log T ≤ T := (Real.log_le_sub_one_of_pos hTp).trans (by linarith)
  have hprofile := Real.log_le_sub_one_of_pos (show 0 < τ * T by positivity)
  rw [Real.log_mul (ne_of_gt hτ) (ne_of_gt hTp)] at hprofile
  have hprofile' := mul_le_mul_of_nonneg_left hprofile hp.le
  have hdrop : 0 ≤ β / (1 - β) * Real.log (1 + w * τ * Real.exp (-T)) := by
    apply mul_nonneg (by positivity) (Real.log_nonneg (by nlinarith))
  have hτT : 0 ≤ (τ / (1 - β)) * Real.log T := by positivity
  have herr := mul_le_mul_of_nonneg_left hlogTle
    (show 0 ≤ 2 * b / (1 - β) * Real.exp (-T) by positivity)
  have hre : 2 - 1 / (1 - β) =
      -τ / (1 - β) + 2 * b / (1 - β) * Real.exp (-T) := by
    field_simp
    nlinarith
  rw [Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_mul (by positivity) (by positivity)]
  rw [scalarD0_log β _ hβ hβ1 hd, Real.log_pow, Real.log_exp]
  rw [Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_mul (by positivity) (by positivity), Real.log_exp]
  rw [Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_rpow hβ, Real.log_rpow hw, Real.log_exp, Real.log_exp]
  have hreT := congrArg (fun x : ℝ => x * T) hre
  have hreLog := congrArg (fun x : ℝ => x * Real.log T) hre
  simp only [div_eq_mul_inv] at hprofile' hdrop hτT herr hreT hreLog ⊢
  nlinarith only [hprofile', hdrop, hτT, herr, hreT, hreLog]

def actualCoefficient (χ τ : ℝ) : ℝ :=
  let β := slowRate (zeta χ τ) (feedback χ τ)
  (1 - β) * β ^ (β / (1 - β)) * (weightScale χ τ) ^ (1 / (1 - β)) *
    Real.exp (-1 / (1 - β))

theorem actual_zero_parameters :
    zeta 0 0 = 1 / 2 ∧ feedback 0 0 = 0 ∧
      slowRate (zeta 0 0) (feedback 0 0) = 1 / 2 ∧
      weightScale 0 0 = 8 ∧ rateCorrection 0 0 = 1 := by
  norm_num [zeta, feedback, slowRate, spectralGap, weightScale, rateCorrection]

theorem actualCoefficient_zero : actualCoefficient 0 0 = 16 / (Real.exp 1) ^ 2 := by
  obtain ⟨_, _, hb, hw, _⟩ := actual_zero_parameters
  unfold actualCoefficient
  rw [hb, hw]
  norm_num
  rw [Real.exp_neg, show (2 : ℝ) = (2 : ℕ) * (1 : ℝ) by norm_num, Real.exp_nat_mul]
  ring

theorem actualCoefficient_continuous :
    ContinuousAt (fun v : ℝ × ℝ => actualCoefficient v.1 v.2) (0, 0) := by
  have hz : ContinuousAt (fun v : ℝ × ℝ => zeta v.1 v.2) (0, 0) := by
    unfold zeta
    fun_prop (disch := norm_num)
  have hh : ContinuousAt (fun v : ℝ × ℝ => feedback v.1 v.2) (0, 0) := by
    unfold feedback
    fun_prop (disch := norm_num)
  have hg : ContinuousAt
      (fun v : ℝ × ℝ => spectralGap (zeta v.1 v.2) (feedback v.1 v.2)) (0, 0) := by
    unfold spectralGap
    fun_prop
  have hb : ContinuousAt
      (fun v : ℝ × ℝ => slowRate (zeta v.1 v.2) (feedback v.1 v.2)) (0, 0) := by
    unfold slowRate
    fun_prop
  have hw : ContinuousAt (fun v : ℝ × ℝ => weightScale v.1 v.2) (0, 0) := by
    unfold weightScale
    fun_prop (disch := norm_num [zeta, feedback, spectralGap])
  have hden : ContinuousAt (fun v : ℝ × ℝ =>
      1 - slowRate (zeta v.1 v.2) (feedback v.1 v.2)) (0, 0) :=
    continuousAt_const.sub hb
  have hn : (1 : ℝ) - slowRate (zeta 0 0) (feedback 0 0) ≠ 0 := by
    rw [actual_zero_parameters.2.2.1]
    norm_num
  have hbr := hb.rpow (hb.div hden hn) (Or.inl (by
    norm_num [zeta, feedback, spectralGap, slowRate]))
  have hpr : ContinuousAt (fun v : ℝ × ℝ =>
      1 / (1 - slowRate (zeta v.1 v.2) (feedback v.1 v.2))) (0, 0) :=
    continuousAt_const.div hden hn
  have hwr := hw.rpow hpr (Or.inl (by
    norm_num [zeta, feedback, spectralGap, weightScale]))
  have her : ContinuousAt (fun v : ℝ × ℝ =>
      -1 / (1 - slowRate (zeta v.1 v.2) (feedback v.1 v.2))) (0, 0) :=
    continuousAt_const.div hden hn
  have he := Real.continuous_exp.continuousAt.comp
    her
  exact ((hden.mul hbr).mul hwr).mul he

theorem actual_correction_bounds (χ τ : ℝ) (hχ : 0 < χ) (hχs : χ ≤ 1 / 100)
    (hτ : 0 < τ) (hτh : τ ≤ 1 / 2) :
    0 < weightScale χ τ ∧ weightScale χ τ ≤ 36 ∧
      0 ≤ rateCorrection χ τ ∧ rateCorrection χ τ ≤ 6 ∧
      slowRate (zeta χ τ) (feedback χ τ) ≤ 3 / 4 := by
  obtain ⟨hzl, hzu, hhp, hhu⟩ := actual_parameter_bounds χ τ hχ hχs hτ hτh
  have hχ1 : χ < 1 := by linarith
  have ha : 9 / 10 ≤ (1 - χ) ^ 2 := by nlinarith
  have hA : 9 / 10 ≤ (1 - χ) ^ 2 * (1 + χ ^ 2) := by
    have h := mul_le_mul_of_nonneg_left (show 1 ≤ 1 + χ ^ 2 by nlinarith [sq_nonneg χ])
      (sq_nonneg (1 - χ))
    nlinarith
  have hg0 : 0 ≤ spectralGap (zeta χ τ) (feedback χ τ) := Real.sqrt_nonneg _
  have hsq : spectralGap (zeta χ τ) (feedback χ τ) ^ 2 =
      (1 - zeta χ τ) ^ 2 + 4 * feedback χ τ := Real.sq_sqrt (by positivity)
  have hg : 1 / 4 ≤ spectralGap (zeta χ τ) (feedback χ τ) := by nlinarith
  have hgs : 1 / 2 ≤ spectralGap (zeta χ τ) (feedback χ τ) + (1 - zeta χ τ) := by linarith
  have hgp : 0 < spectralGap (zeta χ τ) (feedback χ τ) := by linarith
  have hzgap : 0 < 1 - zeta χ τ := by linarith
  have hχgap : 0 < 1 - χ := by linarith
  have hAg : 9 / 40 ≤ (1 - χ) ^ 2 * (1 + χ ^ 2) *
      spectralGap (zeta χ τ) (feedback χ τ) := by
    have h := mul_le_mul hA hg (by norm_num : (0 : ℝ) ≤ 1 / 4) (by positivity)
    nlinarith
  have hden : 9 / 80 ≤ (1 - χ) ^ 2 * (1 + χ ^ 2) *
      spectralGap (zeta χ τ) (feedback χ τ) *
      (spectralGap (zeta χ τ) (feedback χ τ) + (1 - zeta χ τ)) := by
    have h := mul_le_mul hAg hgs (by norm_num : (0 : ℝ) ≤ 1 / 2) (by positivity)
    nlinarith
  have hbden : 9 / 20 ≤ (1 - χ) ^ 2 * (1 + χ ^ 2) *
      (spectralGap (zeta χ τ) (feedback χ τ) + (1 - zeta χ τ)) := by
    have h := mul_le_mul hA hgs (by norm_num : (0 : ℝ) ≤ 1 / 2) (by positivity)
    nlinarith
  have hfirst : (2 + τ * χ) / (2 * (1 + χ ^ 2)) ≤ 3 / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (1 + χ ^ 2))).2
    nlinarith [mul_le_mul hτh hχs hχ.le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hsecond : 4 * τ / ((1 - χ) ^ 2 * (1 + χ ^ 2) *
      (spectralGap (zeta χ τ) (feedback χ τ) + (1 - zeta χ τ))) ≤ 9 / 2 := by
    apply (div_le_iff₀ (by linarith : 0 < (1 - χ) ^ 2 * (1 + χ ^ 2) *
      (spectralGap (zeta χ τ) (feedback χ τ) + (1 - zeta χ τ)))).2
    nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold weightScale
    exact div_pos (by norm_num) (by linarith)
  · unfold weightScale
    apply (div_le_iff₀ (by linarith)).2
    nlinarith
  · unfold rateCorrection
    positivity
  · unfold rateCorrection
    linarith
  · unfold slowRate
    nlinarith

theorem actual_scaled_bound (T τ : ℝ) (hT : 1 ≤ T)
    (hχs : Real.exp (-T) ≤ 1 / 100) (hτ : 0 < τ) (hτh : τ ≤ 1 / 2) :
    scalarD0 (slowRate (zeta (Real.exp (-T)) τ) (feedback (Real.exp (-T)) τ))
        (slowWeight (zeta (Real.exp (-T)) τ) (feedback (Real.exp (-T)) τ)) *
      T ^ 2 * Real.exp (2 * T) ≤
      actualCoefficient (Real.exp (-T)) τ * Real.exp (96 * T * Real.exp (-T)) := by
  let χ := Real.exp (-T)
  have hχ : 0 < χ := Real.exp_pos _
  obtain ⟨hzl, hzu, hhp, _⟩ := actual_parameter_bounds χ τ hχ hχs hτ hτh
  have hz1 : zeta χ τ < 1 := by linarith
  obtain ⟨hbl, hbu, _, _⟩ := actual_spectral_bounds χ τ hχ hχs hτ hτh
  have hb : 0 < slowRate (zeta χ τ) (feedback χ τ) := by linarith
  obtain ⟨hwp, _, hbp, hb6, hb34⟩ := actual_correction_bounds χ τ hχ hχs hτ hτh
  have h := scalarD0_scaled_bound T τ _ (weightScale χ τ) (rateCorrection χ τ)
    hT hτ hb hbu hwp hbp (rateCorrection_exact χ τ hz1 hhp)
  rw [show weightScale χ τ * τ * Real.exp (-T) = χ * τ * weightScale χ τ by dsimp [χ]; ring,
    ← weightScale_exact χ τ hz1 hhp] at h
  change _ ≤ actualCoefficient χ τ * Real.exp (96 * T * χ)
  change _ ≤ actualCoefficient χ τ *
    Real.exp (4 * rateCorrection χ τ / (1 - slowRate (zeta χ τ) (feedback χ τ)) * T * χ) at h
  have hc : 0 ≤ actualCoefficient χ τ := by unfold actualCoefficient; positivity
  have he : 4 * rateCorrection χ τ / (1 - slowRate (zeta χ τ) (feedback χ τ)) ≤ 96 := by
    apply (div_le_iff₀ (sub_pos.mpr hbu)).2
    nlinarith
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ hc
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right he (by linarith : 0 ≤ T)) hχ.le

theorem scalarD0_le_power (β d : ℝ) (hβ : 0 < β) (hβ1 : β < 1) (hd : 0 < d) :
    scalarD0 β d ≤ d ^ (1 / (1 - β)) := by
  have hr : 0 ≤ β / (1 - β) := by positivity
  have hbase : d * β / (1 + d) ≤ d := by
    apply (div_le_iff₀ (by positivity : 0 < 1 + d)).2
    nlinarith
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ d * β / (1 + d)) hbase hr
  have he : 1 / (1 - β) = 1 + β / (1 - β) := by field_simp; ring
  rw [he, Real.rpow_add hd, Real.rpow_one]
  unfold scalarD0
  apply mul_le_mul _ hp (by positivity) hd.le
  nlinarith

theorem actual_tail_bound (T τ δ : ℝ) (hT : 1 ≤ T)
    (hχs : Real.exp (-T) ≤ 1 / 100)
    (hδ : 0 < δ) (hδτ : δ ≤ τ) (hτh : τ ≤ 1 / 2)
    (hχδ : Real.exp (-T) ≤ δ / 24) :
    scalarD0 (slowRate (zeta (Real.exp (-T)) τ) (feedback (Real.exp (-T)) τ))
        (slowWeight (zeta (Real.exp (-T)) τ) (feedback (Real.exp (-T)) τ)) *
      T ^ 2 * Real.exp (2 * T) ≤
      (18 : ℝ) ^ (2 + δ / 2) * T ^ 2 * Real.exp (-(δ / 2) * T) := by
  let χ := Real.exp (-T)
  let β := slowRate (zeta χ τ) (feedback χ τ)
  let d := slowWeight (zeta χ τ) (feedback χ τ)
  have hχ : 0 < χ := Real.exp_pos _
  have hτ : 0 < τ := hδ.trans_le hδτ
  obtain ⟨hzl, hzu, hhp, _⟩ := actual_parameter_bounds χ τ hχ hχs hτ hτh
  have hz1 : zeta χ τ < 1 := by linarith
  obtain ⟨hbl, hbu, hdp, _⟩ := actual_spectral_bounds χ τ hχ hχs hτ hτh
  obtain ⟨hwp, hw36, hbp, hb6, hb34⟩ := actual_correction_bounds χ τ hχ hχs hτ hτh
  have hb : 0 < β := by dsimp [β]; linarith
  have hb1 : β < 1 := hbu
  have hd : 0 < d := hdp
  have hbexact := rateCorrection_exact χ τ hz1 hhp
  have hmul : χ * rateCorrection χ τ ≤ δ / 4 := by
    have h := mul_le_mul hχδ hb6 hbp (by linarith : (0 : ℝ) ≤ δ / 24)
    dsimp [χ] at *
    nlinarith
  have hβδ : 1 / 2 + δ / 4 ≤ β := by dsimp [β]; linarith
  have hexponent : 2 + δ / 2 ≤ 1 / (1 - β) := by
    apply (le_div_iff₀ (sub_pos.mpr hb1)).2
    have hδh : δ ≤ 1 / 2 := hδτ.trans hτh
    nlinarith
  have hd18 : d ≤ 18 * χ := by
    dsimp [d]
    rw [weightScale_exact χ τ hz1 hhp]
    have h := mul_le_mul hτh hw36 hwp.le (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hm := mul_le_mul_of_nonneg_left h hχ.le
    nlinarith
  have hbase : 18 * χ ≤ 1 := by dsimp [χ]; nlinarith
  have hp := (scalarD0_le_power β d hb hb1 hd).trans
    ((Real.rpow_le_rpow hd.le hd18 (by positivity : 0 ≤ 1 / (1 - β))).trans
      (Real.rpow_le_rpow_of_exponent_ge (by positivity) hbase hexponent))
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hp (sq_nonneg T)) (Real.exp_nonneg (2 * T))
  change scalarD0 β d * T ^ 2 * Real.exp (2 * T) ≤ _
  apply hm.trans_eq
  dsimp [χ]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 18) (Real.exp_nonneg _),
    Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  have he : Real.exp (-T * (2 + δ / 2)) * Real.exp (2 * T) = Real.exp (-(δ / 2) * T) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (18 : ℝ) ^ (2 + δ / 2) * T ^ 2 *
      (Real.exp (-T * (2 + δ / 2)) * Real.exp (2 * T)) := by ring
    _ = _ := by rw [he]

theorem continuousAt_pair_local_upper (f : ℝ × ℝ → ℝ)
    (hf : ContinuousAt f (0, 0)) (B : ℝ) (hB : f (0, 0) < B) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ χ τ : ℝ, 0 ≤ χ → χ < δ → 0 ≤ τ → τ < δ →
      f (χ, τ) < B := by
  have he : ∀ᶠ v : ℝ × ℝ in 𝓝 (0, 0), f v < B :=
    hf.tendsto.eventually (eventually_lt_nhds hB)
  obtain ⟨δ, hδ, hball⟩ := (Metric.mem_nhds_iff
    (s := {v : ℝ × ℝ | f v < B})
    (x := (0, 0))).mp he
  refine ⟨δ, hδ, ?_⟩
  intro χ τ hχ hχδ hτ hτδ
  apply hball
  simp only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero,
    abs_of_nonneg hχ, abs_of_nonneg hτ, max_lt_iff]
  exact ⟨hχδ, hτδ⟩

/-- 原始实际系数在二维矩形内接近 16/e²。 -/
theorem actualCoefficient_local_bound (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ χ τ : ℝ, 0 ≤ χ → χ < δ → 0 ≤ τ → τ < δ →
      actualCoefficient χ τ < 16 / (Real.exp 1) ^ 2 + η := by
  exact continuousAt_pair_local_upper (fun v => actualCoefficient v.1 v.2)
    actualCoefficient_continuous _ (by rw [actualCoefficient_zero]; linarith)

def actualD0 (χ τ : ℝ) : ℝ :=
  scalarD0 (slowRate (zeta χ τ) (feedback χ τ)) (slowWeight (zeta χ τ) (feedback χ τ))

/-- 全部小速率比的实际 D0 一致上界，包含 τ 超指数趋零。 -/
theorem actualD0_uniform_bound (η : ℝ) (hη : 0 < η) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
      actualD0 (Real.exp (-T)) τ * T ^ 2 * Real.exp (2 * T) ≤
        16 / (Real.exp 1) ^ 2 + η := by
  let c : ℝ := 16 / (Real.exp 1) ^ 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hce : c + η / 2 ≠ 0 := by positivity
  obtain ⟨δ, hδ, hlocal⟩ := actualCoefficient_local_bound (η / 2) (by positivity)
  have hχ : Tendsto (fun T : ℝ => Real.exp (-T)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hχev : ∀ᶠ T : ℝ in atTop,
      Real.exp (-T) < min (1 / 100) (min δ (δ / 24)) :=
    hχ.eventually (eventually_lt_nhds (by positivity))
  have herr0 : Tendsto (fun T : ℝ => 96 * T * Real.exp (-T)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) 1 (by norm_num)).const_mul 96
    simpa only [Real.rpow_one, neg_one_mul, mul_zero, mul_assoc] using h
  have herr : Tendsto (fun T : ℝ => Real.exp (96 * T * Real.exp (-T))) atTop (𝓝 1) := by
    simpa only [Real.exp_zero, Function.comp_def] using
      Real.continuous_exp.continuousAt.tendsto.comp herr0
  have herrev : ∀ᶠ T : ℝ in atTop,
      Real.exp (96 * T * Real.exp (-T)) < 1 + η / (2 * (c + η / 2)) :=
    herr.eventually (eventually_lt_nhds (by
      have hp : 0 < η / (2 * (c + η / 2)) := by positivity
      linarith))
  have htail : Tendsto (fun T : ℝ =>
      (18 : ℝ) ^ (2 + δ / 2) * T ^ 2 * Real.exp (-(δ / 2) * T)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 : ℝ) (δ / 2)
      (by positivity)).const_mul ((18 : ℝ) ^ (2 + δ / 2))
    simpa only [Real.rpow_two, mul_zero, mul_assoc] using h
  have htailev : ∀ᶠ T : ℝ in atTop,
      (18 : ℝ) ^ (2 + δ / 2) * T ^ 2 * Real.exp (-(δ / 2) * T) < c + η :=
    htail.eventually (eventually_lt_nhds (by positivity))
  have hev : ∀ᶠ T : ℝ in atTop, ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
      actualD0 (Real.exp (-T)) τ * T ^ 2 * Real.exp (2 * T) ≤ c + η := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), hχev, herrev, htailev]
      with T hT hχs herrT htailT
    intro τ hτ hτh
    have hχ100 : Real.exp (-T) ≤ 1 / 100 := (lt_min_iff.mp hχs).1.le
    have hχδ : Real.exp (-T) < δ := (lt_min_iff.mp (lt_min_iff.mp hχs).2).1
    have hχδ24 : Real.exp (-T) ≤ δ / 24 := (lt_min_iff.mp (lt_min_iff.mp hχs).2).2.le
    by_cases hτδ : τ < δ
    · have hC := hlocal (Real.exp (-T)) τ (Real.exp_nonneg _) hχδ hτ.le hτδ
      calc
        _ ≤ actualCoefficient (Real.exp (-T)) τ * Real.exp (96 * T * Real.exp (-T)) :=
          actual_scaled_bound T τ hT hχ100 hτ hτh
        _ ≤ (c + η / 2) * (1 + η / (2 * (c + η / 2))) :=
          mul_le_mul hC.le herrT.le (Real.exp_nonneg _) (by positivity)
        _ = c + η := by field_simp; ring
    · exact (actual_tail_bound T τ δ hT hχ100 hδ (le_of_not_gt hτδ) hτh hχδ24).trans htailT.le
  exact Filter.eventually_atTop.mp hev

def stationaryNu (T : ℝ) : ℝ := Real.exp (-2 * T) / (1 + Real.exp (-2 * T))

def nuScale (T : ℝ) : ℝ :=
  (1 + Real.exp (-2 * T)) * (2 + Real.log (1 + Real.exp (-2 * T)) / T) ^ 2

theorem stationaryNu_pos (T : ℝ) : 0 < stationaryNu T := by
  unfold stationaryNu
  positivity

theorem nuScale_limit : Tendsto nuScale atTop (𝓝 4) := by
  have hχ : Tendsto (fun T : ℝ => Real.exp (-T)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hE : Tendsto (fun T : ℝ => Real.exp (-2 * T)) atTop (𝓝 0) := by
    have h := hχ.pow 2
    convert h using 1
    · funext T
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    · norm_num
  have hsum : Tendsto (fun T : ℝ => 1 + Real.exp (-2 * T)) atTop (𝓝 1) := by
    simpa using hE.const_add 1
  have hlog : Tendsto (fun T : ℝ => Real.log (1 + Real.exp (-2 * T))) atTop (𝓝 0) := by
    simpa only [Real.log_one, Function.comp_def] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hsum
  have hinv : Tendsto (fun T : ℝ => 1 / T) atTop (𝓝 0) := tendsto_id.const_div_atTop 1
  have hlogdiv : Tendsto (fun T : ℝ => Real.log (1 + Real.exp (-2 * T)) / T) atTop (𝓝 0) := by
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_zero] using hlog.mul hinv
  have h := hsum.mul ((hlogdiv.const_add 2).pow 2)
  convert h using 1
  · rfl
  · norm_num

theorem nu_normalization (T y : ℝ) (hT : 0 < T) :
    y * (Real.log (1 / stationaryNu T)) ^ 2 / stationaryNu T =
      (y * T ^ 2 * Real.exp (2 * T)) * nuScale T := by
  have hlog : Real.log (1 / stationaryNu T) = 2 * T + Real.log (1 + Real.exp (-2 * T)) := by
    unfold stationaryNu
    rw [Real.log_div (by norm_num) (by positivity), Real.log_one]
    rw [Real.log_div (by positivity) (by positivity), Real.log_exp]
    ring
  rw [hlog]
  unfold stationaryNu nuScale
  have hTn : T ≠ 0 := ne_of_gt hT
  have he : Real.exp (-2 * T) = (Real.exp (2 * T))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [he]
  field_simp
  <;> ring

theorem actualD0_nuScale_exact (T τ : ℝ) (hT : 0 < T) :
    actualD0 (Real.exp (-T)) τ * (Real.log (1 / stationaryNu T)) ^ 2 / stationaryNu T =
      (actualD0 (Real.exp (-T)) τ * T ^ 2 * Real.exp (2 * T)) * nuScale T :=
  nu_normalization T _ hT

/-- 在真实稳态 ν 的对数归一化下得到 64/e²，一致于全部小速率比。 -/
theorem actualD0_nu_uniform_bound (η : ℝ) (hη : 0 < η) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
      actualD0 (Real.exp (-T)) τ * (Real.log (1 / stationaryNu T)) ^ 2 / stationaryNu T ≤
        64 / (Real.exp 1) ^ 2 + η := by
  let c : ℝ := 16 / (Real.exp 1) ^ 2
  have hc : 0 < c := by dsimp [c]; positivity
  let δ := min 1 (η / (2 * (5 + c)))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδu : δ ≤ η / (2 * (5 + c)) := min_le_right _ _
  have hδmul : δ * (2 * (5 + c)) ≤ η := (le_div_iff₀ (by positivity)).mp hδu
  obtain ⟨T₁, hmain⟩ := actualD0_uniform_bound δ hδ
  have hsev : ∀ᶠ T : ℝ in atTop, nuScale T < 4 + δ :=
    nuScale_limit.eventually (eventually_lt_nhds (by linarith))
  obtain ⟨T₂, hscale⟩ := Filter.eventually_atTop.mp hsev
  refine ⟨max 1 (max T₁ T₂), ?_⟩
  intro T hT τ hτ hτh
  have hT1 : 1 ≤ T := (le_max_left _ _).trans hT
  have hTT : max T₁ T₂ ≤ T := (le_max_right _ _).trans hT
  have hT₁ : T₁ ≤ T := (le_max_left _ _).trans hTT
  have hT₂ : T₂ ≤ T := (le_max_right _ _).trans hTT
  rw [actualD0_nuScale_exact T τ (by linarith)]
  have hns : 0 ≤ nuScale T := by unfold nuScale; positivity
  have hm := mul_le_mul (hmain T hT₁ τ hτ hτh) (hscale T hT₂).le hns
    (show 0 ≤ c + δ by positivity)
  apply hm.trans
  have hd2 : δ ^ 2 ≤ δ := by nlinarith
  calc
    (c + δ) * (4 + δ) ≤ 4 * c + η := by nlinarith
    _ = 64 / (Real.exp 1) ^ 2 + η := by dsimp [c]; ring

/-- 对数参数化覆盖所有足够小的实际 ν。 -/
theorem smallNu_transfer (P : ℝ → ℝ → Prop)
    (hP : ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → P (Real.exp (-T)) (stationaryNu T)) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν < ν₀ →
      P (Real.sqrt (ν / (1 - ν))) ν := by
  obtain ⟨T₀, hmain⟩ := hP
  let S := max 1 T₀
  let χ₀ := Real.exp (-S)
  have hχ₀ : 0 < χ₀ := Real.exp_pos _
  refine ⟨min (1 / 4) (χ₀ ^ 2 / 4), by positivity, ?_⟩
  intro ν hν hνsmall
  have hν14 : ν < 1 / 4 := (lt_min_iff.mp hνsmall).1
  have hνχ : ν < χ₀ ^ 2 / 4 := (lt_min_iff.mp hνsmall).2
  have hden : 0 < 1 - ν := by linarith
  let χ := Real.sqrt (ν / (1 - ν))
  let T := -Real.log χ
  have hχ : 0 < χ := Real.sqrt_pos.2 (by positivity)
  have hχsq : χ ^ 2 = ν / (1 - ν) := Real.sq_sqrt (by positivity)
  have hmul := mul_le_mul_of_nonneg_right hν14.le (sq_nonneg χ₀)
  have hχsq_lt : χ ^ 2 < χ₀ ^ 2 := by
    rw [hχsq]
    apply (div_lt_iff₀ hden).2
    nlinarith
  have hχlt : χ < χ₀ := by nlinarith
  have hlog := Real.log_lt_log hχ hχlt
  have hST : S ≤ T := by
    dsimp [χ₀] at hlog
    rw [Real.log_exp] at hlog
    dsimp [T]
    linarith
  have hT : T₀ ≤ T := (le_max_right 1 T₀).trans hST
  have hexp : Real.exp (-T) = χ := by dsimp [T]; simp [Real.exp_log hχ]
  have hE : Real.exp (-2 * T) = χ ^ 2 := by
    rw [show -2 * T = (2 : ℕ) * (-T) by norm_num <;> ring, Real.exp_nat_mul, hexp]
  have hnu : stationaryNu T = ν := by
    unfold stationaryNu
    rw [hE, hχsq]
    have hn : 1 - ν ≠ 0 := ne_of_gt hden
    field_simp
    <;> ring
  have h := hmain T hT
  rw [hexp, hnu] at h
  exact h

/-- 同一一致界以任意实际小 ν 表述，无序列或固定速率比限制。 -/
theorem actualD0_nu_small_ratio_uniform (η : ℝ) (hη : 0 < η) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν < ν₀ →
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
      actualD0 (Real.sqrt (ν / (1 - ν))) τ * (Real.log (1 / ν)) ^ 2 / ν ≤
        64 / (Real.exp 1) ^ 2 + η :=
  smallNu_transfer (fun χ ν => ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
    actualD0 χ τ * (Real.log (1 / ν)) ^ 2 / ν ≤ 64 / (Real.exp 1) ^ 2 + η)
    (actualD0_nu_uniform_bound η hη)

def weightedFeedback (χ τ : ℝ) : ℝ :=
  36 * χ * τ / ((1 - χ) ^ 2 * (3 * τ - 1 - 6 * χ - χ ^ 2))

theorem weightedFeedback_bound (χ τ : ℝ) (hχ : 0 < χ) (hχs : χ ≤ 1 / 100)
    (hτ : 1 / 2 ≤ τ) :
    0 < weightedFeedback χ τ ∧ weightedFeedback χ τ ≤ 48 * χ ∧
      weightedFeedback χ τ < 1 ∧
      weightedFeedback χ τ / (1 - weightedFeedback χ τ) ≤ 100 * χ := by
  have hτp : 0 < τ := by linarith
  have hχ1 : χ < 1 := by linarith
  have ha : 9 / 10 ≤ (1 - χ) ^ 2 := by nlinarith
  have hχsq : χ ^ 2 ≤ 1 / 10000 := by nlinarith
  have hb : 7 / 8 * τ ≤ 3 * τ - 1 - 6 * χ - χ ^ 2 := by nlinarith
  have hbp : 0 < 3 * τ - 1 - 6 * χ - χ ^ 2 := by nlinarith
  have hab : 63 / 80 * τ ≤ (1 - χ) ^ 2 * (3 * τ - 1 - 6 * χ - χ ^ 2) := by
    have h := mul_le_mul ha hb (by positivity : 0 ≤ 7 / 8 * τ) (by positivity)
    nlinarith
  have hd : 0 < (1 - χ) ^ 2 * (3 * τ - 1 - 6 * χ - χ ^ 2) := by positivity
  have he : 0 < weightedFeedback χ τ := by unfold weightedFeedback; positivity
  have heu : weightedFeedback χ τ ≤ 48 * χ := by
    unfold weightedFeedback
    apply (div_le_iff₀ hd).2
    have h := mul_le_mul_of_nonneg_left hab hχ.le
    nlinarith
  have he1 : weightedFeedback χ τ < 1 := by nlinarith
  refine ⟨he, heu, he1, ?_⟩
  apply (div_le_iff₀ (sub_pos.mpr he1)).2
  have he48 : weightedFeedback χ τ ≤ 48 / 100 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left he48 hχ.le
  nlinarith

theorem cubic_profile_bound (a y : ℝ) (ha : 0 ≤ a) (hy : 0 ≤ y) :
    a * y ^ 2 - y ^ 3 ≤ 4 / 27 * a ^ 3 := by
  have h := mul_nonneg (sq_nonneg (y - 2 * a / 3)) (show 0 ≤ y + a / 3 by positivity)
  nlinarith

theorem large_ratio_scalar_bound (χ x q : ℝ) (hχ : 0 ≤ χ)
    (hq : Real.exp (-x) - 100 * χ * Real.exp (-(2 * x / 3)) ≤ q) :
    max (-q) 0 ≤ 4 / 27 * (100 * χ) ^ 3 := by
  let y := Real.exp (-x / 3)
  have he2 : Real.exp (-(2 * x / 3)) = y ^ 2 := by
    dsimp [y]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have he3 : Real.exp (-x) = y ^ 3 := by
    dsimp [y]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have h := cubic_profile_bound (100 * χ) y (by positivity) (Real.exp_nonneg _)
  rw [he2, he3] at hq
  apply max_le
  · linarith
  · positivity

def largeD (χ : ℝ) : ℝ := 4 / 27 * (100 * χ) ^ 3

theorem largeD_normalized_limit :
    Tendsto (fun T : ℝ => largeD (Real.exp (-T)) *
      (Real.log (1 / stationaryNu T)) ^ 2 / stationaryNu T) atTop (𝓝 0) := by
  have hbase : Tendsto (fun T : ℝ => (4 / 27 * 100 ^ 3) * T ^ 2 * Real.exp (-T))
      atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 : ℝ) 1 (by norm_num)).const_mul
      (4 / 27 * 100 ^ 3)
    simpa only [Real.rpow_two, neg_one_mul, mul_zero, mul_assoc] using h
  have h := hbase.mul nuScale_limit
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  rw [nu_normalization T _ hT]
  have he : Real.exp (-T) ^ 3 * Real.exp (2 * T) = Real.exp (-T) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  unfold largeD
  have hi : (4 / 27 * (100 * Real.exp (-T)) ^ 3) * T ^ 2 * Real.exp (2 * T) =
      (4 / 27 * 100 ^ 3) * T ^ 2 * Real.exp (-T) := by
    calc
      _ = (4 / 27 * 100 ^ 3) * T ^ 2 * (Real.exp (-T) ^ 3 * Real.exp (2 * T)) := by ring
      _ = _ := by rw [he]
  rw [hi]

theorem largeD_nu_uniform_small (η : ℝ) (hη : 0 < η) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν < ν₀ →
      largeD (Real.sqrt (ν / (1 - ν))) * (Real.log (1 / ν)) ^ 2 / ν ≤ η := by
  refine smallNu_transfer (fun χ ν => largeD χ * (Real.log (1 / ν)) ^ 2 / ν ≤ η) ?_
  apply Filter.eventually_atTop.mp
  exact (largeD_normalized_limit.eventually (eventually_lt_nhds hη)).mono
    (fun _ h => h.le)

def diagonalEnvelope (χ τ : ℝ) : ℝ := if τ ≤ 1 / 2 then actualD0 χ τ else largeD χ

/-- 全速率比标量包络：近重根与无穷大比值均用实际加权核界。 -/
theorem diagonalEnvelope_nu_uniform (η : ℝ) (hη : 0 < η) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν < ν₀ →
      ∀ τ : ℝ, 0 < τ →
      diagonalEnvelope (Real.sqrt (ν / (1 - ν))) τ * (Real.log (1 / ν)) ^ 2 / ν ≤
        64 / (Real.exp 1) ^ 2 + η := by
  obtain ⟨ν₁, hν₁, hsmall⟩ := actualD0_nu_small_ratio_uniform η hη
  obtain ⟨ν₂, hν₂, hlarge⟩ := largeD_nu_uniform_small η hη
  refine ⟨min ν₁ ν₂, by positivity, ?_⟩
  intro ν hν hνu τ hτ
  have hν1 := (lt_min_iff.mp hνu).1
  have hν2 := (lt_min_iff.mp hνu).2
  unfold diagonalEnvelope
  split_ifs with hτh
  · exact hsmall ν hν hν1 τ hτ hτh
  · have h := hlarge ν hν hν2
    have hc : 0 ≤ 64 / (Real.exp 1) ^ 2 := by positivity
    linarith

theorem weightedFeedback_eq_normalized (χ τ : ℝ) (hχ : 0 < χ)
    (hχs : χ ≤ 1 / 100) (hτ : 1 / 2 ≤ τ) :
    2 / 3 < zeta χ τ ∧
      feedback χ τ / ((1 - 2 / 3) * (zeta χ τ - 2 / 3)) = weightedFeedback χ τ := by
  have hχ1 : χ < 1 := by linarith
  have hχsq : χ ^ 2 ≤ 1 / 10000 := by nlinarith
  have hp : 0 < 3 * τ - 1 - 6 * χ - χ ^ 2 := by nlinarith
  have hz : 2 / 3 < zeta χ τ := by
    unfold zeta
    apply (lt_div_iff₀ (by positivity : 0 < 2 * (1 + χ ^ 2))).2
    nlinarith
  refine ⟨hz, ?_⟩
  unfold feedback zeta weightedFeedback
  have hA : 1 - χ ≠ 0 := by positivity
  have hB : 1 + χ ^ 2 ≠ 0 := by positivity
  have hC : 3 * τ - 1 - 6 * χ - χ ^ 2 ≠ 0 := ne_of_gt hp
  field_simp
  <;> ring

#print axioms scalarD0_eq_envelope
#print axioms scalarD0_exponential_bound
#print axioms signed_population_scalar_bound
#print axioms diagonalF_normalized_limit
#print axioms diagonalF_uniform_bound
#print axioms scalarD0_exponential_attains
#print axioms spectral_ranges
#print axioms positive_population_scalar_bound
#print axioms slowWeight_rationalized
#print axioms weightScale_exact
#print axioms scalarD0_scaled_bound
#print axioms actualD0_nu_small_ratio_uniform
#print axioms largeD_normalized_limit
#print axioms diagonalEnvelope_nu_uniform
#print axioms weightedFeedback_eq_normalized

end TwoStateQuantumEmbedding.ResetDiagonalEnvelope
