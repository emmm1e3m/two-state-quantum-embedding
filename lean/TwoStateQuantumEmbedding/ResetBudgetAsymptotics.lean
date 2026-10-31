import TwoStateQuantumEmbedding.ResetStationaryBudget
import Mathlib.Topology.Algebra.Order.Field

noncomputable section
open Set Filter Matrix
open scoped Topology ComplexOrder MatrixOrder

namespace TwoStateQuantumEmbedding.ResetEndpoint

/-- 小正误差的预算严格正。 -/
theorem spectralBudget_pos_small {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) (1 / 64)) :
    0 < spectralBudget ε := lt_of_lt_of_le hε.1 (spectralBudget_explicit hε.1.le hε.2.le).1

/-- 原始误差趋零时，谱预算也从正侧趋零。 -/
theorem spectralBudget_tendsto_zero :
    Tendsto spectralBudget (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h := spectralBudget_ratio_tendsto_one.mul
    (show Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) from nhdsWithin_le_nhds)
  have hh : Tendsto (fun ε => spectralBudget ε / ε * ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using h
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact div_mul_cancel₀ _ (ne_of_gt hε)

theorem spectralBudget_tendsto_zero_right :
    Tendsto spectralBudget (𝓝[>] (0 : ℝ)) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨spectralBudget_tendsto_zero, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 64 by norm_num)] with ε hε
  exact spectralBudget_pos_small hε

/-- 对数重置尺度趋于无穷。 -/
theorem resetLog_tendsto_atTop :
    Tendsto (fun ε : ℝ => Real.log (1 / ε)) (𝓝[>] 0) atTop := by
  simpa only [one_div, Function.comp_def] using Real.tendsto_log_atTop.comp
    (tendsto_inv_nhdsGT_zero : Tendsto (fun ε : ℝ => ε⁻¹) (𝓝[>] 0) atTop)

/-- rho/ε→1 蕴含两个发散对数之比趋于1。 -/
theorem spectralBudget_log_ratio_tendsto_one :
    Tendsto (fun ε => Real.log (1 / spectralBudget ε) / Real.log (1 / ε))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hlog : Tendsto (fun ε => Real.log (spectralBudget ε / ε))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def, Real.log_one] using (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
      spectralBudget_ratio_tendsto_one
  have hinv : Tendsto (fun ε : ℝ => (Real.log (1 / ε))⁻¹)
      (𝓝[>] 0) (𝓝 0) := tendsto_inv_atTop_zero.comp resetLog_tendsto_atTop
  have hh : Tendsto (fun ε => 1 - Real.log (spectralBudget ε / ε) *
      (Real.log (1 / ε))⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (hlog.mul hinv)
  apply hh.congr'
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 64 by norm_num)] with ε hε
  have hr := spectralBudget_pos_small hε
  have hl : 0 < Real.log (1 / ε) := Real.log_pos ((lt_div_iff₀ hε.1).2 (by linarith [hε.2]))
  have hid : Real.log (1 / spectralBudget ε) =
      Real.log (1 / ε) - Real.log (spectralBudget ε / ε) := by
    rw [Real.log_div one_ne_zero hr.ne', Real.log_div one_ne_zero hε.1.ne',
      Real.log_div hr.ne' hε.1.ne', Real.log_one]
    ring
  rw [hid, sub_div, div_self hl.ne']
  simp only [div_eq_mul_inv]

theorem spectralBudget_inv_ratio_tendsto_one :
    Tendsto (fun ε => ε / spectralBudget ε) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  simpa only [inv_div, inv_one] using spectralBudget_ratio_tendsto_one.inv₀
    (by norm_num : (1 : ℝ) ≠ 0)

theorem spectralBudget_inv_log_ratio_tendsto_one :
    Tendsto (fun ε => Real.log (1 / ε) / Real.log (1 / spectralBudget ε))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  simpa only [inv_div, inv_one] using spectralBudget_log_ratio_tendsto_one.inv₀
    (by norm_num : (1 : ℝ) ≠ 0)

/-- 从rho归一化到实际ε归一化的乘法因子。 -/
def budgetScaleChange (ε : ℝ) : ℝ :=
  spectralBudget ε / ε * (Real.log (1 / ε) / Real.log (1 / spectralBudget ε))

theorem budgetScaleChange_tendsto_one :
    Tendsto budgetScaleChange (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  unfold budgetScaleChange
  simpa only [one_mul] using
    spectralBudget_ratio_tendsto_one.mul spectralBudget_inv_log_ratio_tendsto_one

theorem resetLog_pos {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) :
    0 < Real.log (1 / ε) :=
  Real.log_pos ((lt_div_iff₀ hε.1).2 (by simpa using hε.2))

/-- 精确换尺度恒等式，保留增益的正负号。 -/
theorem budgetScaleChange_identity (ε g : ℝ)
    (hε : ε ≠ 0) (hr : spectralBudget ε ≠ 0)
    (hl : Real.log (1 / spectralBudget ε) ≠ 0) :
    Real.log (1 / ε) / ε * g =
      budgetScaleChange ε * (Real.log (1 / spectralBudget ε) / spectralBudget ε * g) := by
  unfold budgetScaleChange
  field_simp

/-- 给定统一rho精细包络，可得到156所需的实际ε容差上界。
这里hsharp明确保留150尚需证明的统一优化输入。 -/
theorem envelope_to_actual_tolerance (C : ℝ) (hC : 0 ≤ C)
    (F : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hsharp : ∀ η : ℝ, 0 < η → ∃ δ > 0,
      ∀ ρ p ν A B : ℝ, 0 < ρ → ρ < δ → 0 ≤ p → 0 ≤ ν → p + ν ≤ ρ →
        0 ≤ A → 0 ≤ B → Real.log (1 / ρ) * F p ν A B ≤ C * p + η * ρ) :
    ∀ η : ℝ, 0 < η → ∃ δ > 0, ∀ ε ∈ Ioo (0 : ℝ) δ,
      ∀ p ν A B g : ℝ, 0 ≤ p → 0 ≤ ν → p + ν ≤ spectralBudget ε →
        0 ≤ A → 0 ≤ B → g ≤ F p ν A B →
          Real.log (1 / ε) / ε * g ≤ C + η := by
  intro η hη
  obtain ⟨δr, hδr, hbound⟩ := hsharp (η / 2) (by positivity)
  have hlimit : Tendsto (fun ε => budgetScaleChange ε * (C + η / 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (C + η / 2)) := by
    simpa using budgetScaleChange_tendsto_one.mul_const (C + η / 2)
  have hevent : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ p ν A B g : ℝ, 0 ≤ p → 0 ≤ ν → p + ν ≤ spectralBudget ε →
        0 ≤ A → 0 ≤ B → g ≤ F p ν A B →
          Real.log (1 / ε) / ε * g ≤ C + η := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 64 by norm_num),
      spectralBudget_tendsto_zero.eventually (eventually_lt_nhds hδr),
      spectralBudget_tendsto_zero.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)),
      hlimit.eventually (eventually_lt_nhds (show C + η / 2 < C + η by linarith))]
      with ε hε hrδ hr1 hscale
    intro p ν A B g hp hν hbudget hA hB hg
    have hr := spectralBudget_pos_small hε
    have hlr := resetLog_pos ⟨hr, hr1⟩
    have hle := resetLog_pos (show ε ∈ Ioo (0 : ℝ) 1 from ⟨hε.1, by linarith [hε.2]⟩)
    have hs : 0 ≤ budgetScaleChange ε :=
      mul_nonneg (div_nonneg hr.le hε.1.le) (div_nonneg hle.le hlr.le)
    have hb := hbound (spectralBudget ε) p ν A B hr hrδ hp hν hbudget hA hB
    have hpρ : p ≤ spectralBudget ε := by linarith
    have hco := mul_le_mul_of_nonneg_left hpρ hC
    have hnorm : Real.log (1 / spectralBudget ε) / spectralBudget ε * F p ν A B ≤ C + η / 2 := by
      calc
        _ = (Real.log (1 / spectralBudget ε) * F p ν A B) / spectralBudget ε := by ring
        _ ≤ C + η / 2 := (div_le_iff₀ hr).2 (by nlinarith [hb])
    have hg' := mul_le_mul_of_nonneg_left hg (div_nonneg hlr.le hr.le)
    rw [budgetScaleChange_identity ε g hε.1.ne' hr.ne' hlr.ne']
    exact (mul_le_mul_of_nonneg_left (hg'.trans hnorm) hs).trans hscale.le
  obtain ⟨δ, hδ, hd⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevent
  exact ⟨δ, hδ, fun ε hε => hd hε⟩

/-- 精细领先项与总预算共同强制预算全部分配给p。 -/
theorem allocation_of_refined_bound
    (C : ℝ) (hC : 0 < C) (ρ p ν y r : ℕ → ℝ)
    (hρ : ∀ᶠ n in atTop, 0 < ρ n)
    (hnonneg : ∀ᶠ n in atTop, 0 ≤ p n ∧ 0 ≤ ν n)
    (hbudget : ∀ᶠ n in atTop, p n + ν n ≤ ρ n)
    (hbound : ∀ᶠ n in atTop, y n ≤ C * (p n / ρ n) + r n)
    (hy : Tendsto y atTop (𝓝 C)) (hr : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n => p n / ρ n) atTop (𝓝 1) ∧
      Tendsto (fun n => ν n / ρ n) atTop (𝓝 0) := by
  have hlo : Tendsto (fun n => (y n - r n) / C) atTop (𝓝 1) := by
    simpa [hC.ne'] using (hy.sub hr).div_const C
  have hp : Tendsto (fun n => p n / ρ n) atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
    · filter_upwards [hbound] with n hb
      apply (div_le_iff₀ hC).2
      linarith
    · filter_upwards [hρ, hnonneg, hbudget] with n hρn hpn hbn
      apply (div_le_iff₀ hρn).2
      linarith [hpn.2]
  refine ⟨hp, ?_⟩
  have hu : Tendsto (fun n => 1 - p n / ρ n) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [hρ, hnonneg] with n hρn hpn
    exact div_nonneg hpn.2 hρn.le
  · filter_upwards [hρ, hbudget] with n hρn hbn
    have hh := div_le_div_of_nonneg_right hbn hρn.le
    rw [add_div, div_self hρn.ne'] at hh
    linarith

/-- 给定实际ε归一化极限，换成rho归一化保留同一常数。 -/
theorem rho_scaled_limit_of_actual (ε g : ℕ → ℝ) (C : ℝ)
    (hε : Tendsto ε atTop (𝓝[>] (0 : ℝ)))
    (hg : Tendsto (fun n => Real.log (1 / ε n) / ε n * g n) atTop (𝓝 C)) :
    Tendsto (fun n => Real.log (1 / spectralBudget (ε n)) / spectralBudget (ε n) * g n)
      atTop (𝓝 C) := by
  have hfactor : Tendsto (fun n => ε n / spectralBudget (ε n) *
      (Real.log (1 / spectralBudget (ε n)) / Real.log (1 / ε n))) atTop (𝓝 1) := by
    simpa using (spectralBudget_inv_ratio_tendsto_one.comp hε).mul
      (spectralBudget_log_ratio_tendsto_one.comp hε)
  have hh : Tendsto (fun n => (ε n / spectralBudget (ε n) *
      (Real.log (1 / spectralBudget (ε n)) / Real.log (1 / ε n))) *
      (Real.log (1 / ε n) / ε n * g n)) atTop (𝓝 C) := by
    simpa using hfactor.mul hg
  apply hh.congr'
  filter_upwards [hε.eventually (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 64 by norm_num))]
    with n hn
  have hr := spectralBudget_pos_small hn
  have hl := resetLog_pos (show ε n ∈ Ioo (0 : ℝ) 1 from ⟨hn.1, by linarith [hn.2]⟩)
  field_simp [hn.1.ne', hr.ne', hl.ne']

/-- 饱和结构的精确序列接口；精细上界和饱和本身均为明确输入。 -/
theorem actual_saturation_allocation (C : ℝ) (hC : 0 < C)
    (ε p ν g r : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝[>] (0 : ℝ)))
    (hnonneg : ∀ᶠ n in atTop, 0 ≤ p n ∧ 0 ≤ ν n)
    (hbudget : ∀ᶠ n in atTop, p n + ν n ≤ spectralBudget (ε n))
    (hbound : ∀ᶠ n in atTop,
      Real.log (1 / spectralBudget (ε n)) * g n ≤
        C * p n + r n * spectralBudget (ε n))
    (hsaturated : Tendsto (fun n => Real.log (1 / ε n) / ε n * g n) atTop (𝓝 C))
    (hr : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n => p n / ε n) atTop (𝓝 1) ∧
      Tendsto (fun n => ν n / ε n) atTop (𝓝 0) := by
  have hρ : ∀ᶠ n in atTop, 0 < spectralBudget (ε n) := by
    filter_upwards [hε.eventually (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 64 by norm_num))]
      with n hn
    exact spectralBudget_pos_small hn
  have hnormalized : ∀ᶠ n in atTop,
      Real.log (1 / spectralBudget (ε n)) / spectralBudget (ε n) * g n ≤
        C * (p n / spectralBudget (ε n)) + r n := by
    filter_upwards [hρ, hbound] with n hρn hbn
    have hb := div_le_div_of_nonneg_right hbn hρn.le
    convert hb using 1 <;> field_simp
  obtain ⟨hpρ, hνρ⟩ := allocation_of_refined_bound C hC (fun n => spectralBudget (ε n)) p ν
    (fun n => Real.log (1 / spectralBudget (ε n)) / spectralBudget (ε n) * g n) r
    hρ hnonneg hbudget hnormalized (rho_scaled_limit_of_actual ε g C hε hsaturated) hr
  have hratio := spectralBudget_ratio_tendsto_one.comp hε
  constructor
  · have hh : Tendsto (fun n => p n / spectralBudget (ε n) * (spectralBudget (ε n) / ε n))
        atTop (𝓝 1) := by simpa using hpρ.mul hratio
    apply hh.congr'
    filter_upwards [hρ] with n hn
    field_simp
  · have hh : Tendsto (fun n => ν n / spectralBudget (ε n) * (spectralBudget (ε n) / ε n))
        atTop (𝓝 0) := by simpa using hνρ.mul hratio
    apply hh.congr'
    filter_upwards [hρ] with n hn
    field_simp

/-- 谱预算分配的相干及纯度标量后果。 -/
theorem coherence_purity_limits_of_allocation (ε p ν : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝[>] (0 : ℝ)))
    (hp : Tendsto (fun n => p n / ε n) atTop (𝓝 1))
    (hν : Tendsto (fun n => ν n / ε n) atTop (𝓝 0)) :
    Tendsto (fun n => (1 - 2 * ν n) ^ 2 * p n * (1 - p n) / ε n) atTop (𝓝 1) ∧
      Tendsto (fun n => 2 * ν n * (1 - ν n) / ε n) atTop (𝓝 0) := by
  have hε0 : Tendsto ε atTop (𝓝 0) := hε.mono_right nhdsWithin_le_nhds
  have hεpos : ∀ᶠ n in atTop, 0 < ε n := hε.eventually self_mem_nhdsWithin
  have hp0 : Tendsto p atTop (𝓝 0) := by
    have hh : Tendsto (fun n => p n / ε n * ε n) atTop (𝓝 0) := by simpa using hp.mul hε0
    apply hh.congr'
    filter_upwards [hεpos] with n hn
    exact div_mul_cancel₀ _ hn.ne'
  have hν0 : Tendsto ν atTop (𝓝 0) := by
    have hh : Tendsto (fun n => ν n / ε n * ε n) atTop (𝓝 0) := by simpa using hν.mul hε0
    apply hh.congr'
    filter_upwards [hεpos] with n hn
    exact div_mul_cancel₀ _ hn.ne'
  constructor
  · have hh : Tendsto (fun n => (1 - 2 * ν n) ^ 2 * (p n / ε n) * (1 - p n))
        atTop (𝓝 1) := by
      convert (((tendsto_const_nhds.sub (tendsto_const_nhds.mul hν0)).pow 2).mul hp).mul
        (tendsto_const_nhds.sub hp0) using 1
      norm_num
    apply hh.congr
    intro n
    ring
  · have hh : Tendsto (fun n => 2 * (ν n / ε n) * (1 - ν n)) atTop (𝓝 0) := by
      convert (tendsto_const_nhds.mul hν).mul (tendsto_const_nhds.sub hν0) using 1
      norm_num
    apply hh.congr
    intro n
    ring

/-- 给定精确谱公式，标量结构极限就是密度矩阵的相干与纯度极限。 -/
theorem stationary_matrix_structure_of_allocation
    (ε p ν : ℕ → ℝ) (ρ : ℕ → QubitMatrix)
    (hε : Tendsto ε atTop (𝓝[>] (0 : ℝ)))
    (hp : Tendsto (fun n => p n / ε n) atTop (𝓝 1))
    (hν : Tendsto (fun n => ν n / ε n) atTop (𝓝 0))
    (hcoherence : ∀ᶠ n in atTop, ‖ρ n 0 1‖ ^ 2 = (1 - 2 * ν n) ^ 2 * p n * (1 - p n))
    (hpurity : ∀ᶠ n in atTop, 1 - (ρ n * ρ n).trace.re = 2 * ν n * (1 - ν n)) :
    Tendsto (fun n => ‖ρ n 0 1‖ ^ 2 / ε n) atTop (𝓝 1) ∧
      Tendsto (fun n => (1 - (ρ n * ρ n).trace.re) / ε n) atTop (𝓝 0) := by
  obtain ⟨hc, hd⟩ := coherence_purity_limits_of_allocation ε p ν hε hp hν
  constructor
  · apply hc.congr'
    filter_upwards [hcoherence] with n hn
    rw [hn]
  · apply hd.congr'
    filter_upwards [hpurity] with n hn
    rw [hn]


/-- 二阶PSD矩阵的行列式实部恒等式。 -/
theorem psd_det_re_identity {ρ : QubitMatrix} (hρ : ρ.PosSemidef) :
    ρ.det.re = (ρ 0 0).re * (ρ 1 1).re - ‖ρ 0 1‖ ^ 2 := by
  have h00 : (ρ 0 0).im = 0 := (RCLike.nonneg_iff.mp (hρ.diag_nonneg (i := 0))).2
  have h11 : (ρ 1 1).im = 0 := (RCLike.nonneg_iff.mp (hρ.diag_nonneg (i := 1))).2
  have h10 : ρ 1 0 = star (ρ 0 1) := (hρ.isHermitian.apply 1 0).symm
  simp [Matrix.det_fin_two, Complex.mul_re, h00, h11, h10,
    Complex.sq_norm, Complex.normSq_apply]

/-- 同一矩阵平方的迹恒等式。 -/
theorem psd_trace_square_identity {ρ : QubitMatrix} (hρ : ρ.PosSemidef) :
    (ρ * ρ).trace.re = (ρ 0 0).re ^ 2 + (ρ 1 1).re ^ 2 + 2 * ‖ρ 0 1‖ ^ 2 := by
  have h00 : (ρ 0 0).im = 0 := (RCLike.nonneg_iff.mp (hρ.diag_nonneg (i := 0))).2
  have h11 : (ρ 1 1).im = 0 := (RCLike.nonneg_iff.mp (hρ.diag_nonneg (i := 1))).2
  have h10 : ρ 1 0 = star (ρ 0 1) := (hρ.isHermitian.apply 1 0).symm
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two,
    Complex.mul_re, h00, h11, h10, Complex.sq_norm, Complex.normSq_apply]
  ring

/-- 任意酉谱分解立即给出小特征值对应的行列式。 -/
theorem spectral_conjugate_det (ρ U : QubitMatrix) (ν : ℝ)
    (hU : U.conjTranspose * U = 1)
    (hspectral : ρ = U * Matrix.diagonal ![(ν : ℂ), 1 - ν] * U.conjTranspose) :
    ρ.det = (ν : ℂ) * (1 - ν) := by
  have hdetU := congrArg Matrix.det hU
  rw [Matrix.det_mul, Matrix.det_one] at hdetU
  rw [hspectral, Matrix.det_mul, Matrix.det_mul]
  calc
    _ = (Matrix.diagonal ![(ν : ℂ), 1 - ν]).det *
        (U.conjTranspose.det * U.det) := by ring
    _ = (ν : ℂ) * (1 - ν) := by
      rw [hdetU, mul_one]
      simp [Matrix.det_diagonal, Fin.prod_univ_two]

/-- 密度矩阵的谱数据给出相干与纯度缺陷的精确公式。 -/
theorem density_spectral_structure {ρ : QubitMatrix} (hρ : ρ.PosSemidef)
    (htrace : ρ.trace = 1) (ν p : ℝ)
    (hdet : ρ.det = (ν : ℂ) * (1 - ν))
    (hpopulation : (ρ 0 0).re = ν + (1 - 2 * ν) * p) :
    ‖ρ 0 1‖ ^ 2 = (1 - 2 * ν) ^ 2 * p * (1 - p) ∧
      1 - (ρ * ρ).trace.re = 2 * ν * (1 - ν) := by
  have hd : ρ.det.re = ν * (1 - ν) := by
    simpa using congrArg Complex.re hdet
  have ht := congrArg Complex.re htrace
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two] at ht
  have hdi := psd_det_re_identity hρ
  have h11 : (ρ 1 1).re = 1 - (ρ 0 0).re := by linarith
  rw [h11] at hdi
  have hco : ‖ρ 0 1‖ ^ 2 = (ρ 0 0).re * (1 - (ρ 0 0).re) - ν * (1 - ν) := by
    nlinarith
  constructor
  · rw [hco, hpopulation]
    ring
  · rw [psd_trace_square_identity hρ]
    have htsq : ((ρ 0 0).re + (ρ 1 1).re) ^ 2 = 1 := by rw [ht]; norm_num
    nlinarith

/-- 已证明谱公式后的真实矩阵结构极限。 -/
theorem stationary_matrix_structure_of_spectral_data
    (ε p ν : ℕ → ℝ) (ρ : ℕ → QubitMatrix)
    (hε : Tendsto ε atTop (𝓝[>] (0 : ℝ)))
    (hp : Tendsto (fun n => p n / ε n) atTop (𝓝 1))
    (hν : Tendsto (fun n => ν n / ε n) atTop (𝓝 0))
    (hstates : ∀ᶠ n in atTop, (ρ n).PosSemidef ∧ (ρ n).trace = 1)
    (hdet : ∀ᶠ n in atTop, (ρ n).det = (ν n : ℂ) * (1 - ν n))
    (hpopulation : ∀ᶠ n in atTop, (ρ n 0 0).re = ν n + (1 - 2 * ν n) * p n) :
    Tendsto (fun n => ‖ρ n 0 1‖ ^ 2 / ε n) atTop (𝓝 1) ∧
      Tendsto (fun n => (1 - (ρ n * ρ n).trace.re) / ε n) atTop (𝓝 0) := by
  have hform : ∀ᶠ n in atTop,
      ‖ρ n 0 1‖ ^ 2 = (1 - 2 * ν n) ^ 2 * p n * (1 - p n) ∧
        1 - (ρ n * ρ n).trace.re = 2 * ν n * (1 - ν n) := by
    filter_upwards [hstates, hdet, hpopulation] with n hs hd hp
    exact density_spectral_structure hs.1 hs.2 (ν n) (p n) hd hp
  exact stationary_matrix_structure_of_allocation ε p ν ρ hε hp hν
    (hform.mono fun _ h => h.1) (hform.mono fun _ h => h.2)

/-- 给定实际序列精细上界与饱和，全部稳态结构结论同时成立。
物理序列满足精细上界的证明仍由150/160接合，不在此前提中隐藏。 -/
theorem actual_saturation_stationary_structure (C : ℝ) (hC : 0 < C)
    (ε p ν g r : ℕ → ℝ) (ρ : ℕ → QubitMatrix)
    (hε : Tendsto ε atTop (𝓝[>] (0 : ℝ)))
    (hnonneg : ∀ᶠ n in atTop, 0 ≤ p n ∧ 0 ≤ ν n)
    (hbudget : ∀ᶠ n in atTop, p n + ν n ≤ spectralBudget (ε n))
    (hbound : ∀ᶠ n in atTop,
      Real.log (1 / spectralBudget (ε n)) * g n ≤
        C * p n + r n * spectralBudget (ε n))
    (hsaturated : Tendsto (fun n => Real.log (1 / ε n) / ε n * g n) atTop (𝓝 C))
    (hr : Tendsto r atTop (𝓝 0))
    (hstates : ∀ᶠ n in atTop, (ρ n).PosSemidef ∧ (ρ n).trace = 1)
    (hdet : ∀ᶠ n in atTop, (ρ n).det = (ν n : ℂ) * (1 - ν n))
    (hpopulation : ∀ᶠ n in atTop, (ρ n 0 0).re = ν n + (1 - 2 * ν n) * p n) :
    Tendsto (fun n => p n / ε n) atTop (𝓝 1) ∧
      Tendsto (fun n => ν n / ε n) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖ρ n 0 1‖ ^ 2 / ε n) atTop (𝓝 1) ∧
      Tendsto (fun n => (1 - (ρ n * ρ n).trace.re) / ε n) atTop (𝓝 0) := by
  obtain ⟨hp, hν⟩ := actual_saturation_allocation C hC ε p ν g r hε hnonneg hbudget
    hbound hsaturated hr
  exact ⟨hp, hν, stationary_matrix_structure_of_spectral_data ε p ν ρ hε hp hν
    hstates hdet hpopulation⟩


end TwoStateQuantumEmbedding.ResetEndpoint

#print axioms TwoStateQuantumEmbedding.ResetEndpoint.spectralBudget_log_ratio_tendsto_one
#print axioms TwoStateQuantumEmbedding.ResetEndpoint.budgetScaleChange_tendsto_one
#print axioms TwoStateQuantumEmbedding.ResetEndpoint.envelope_to_actual_tolerance

#print axioms TwoStateQuantumEmbedding.ResetEndpoint.actual_saturation_allocation
#print axioms TwoStateQuantumEmbedding.ResetEndpoint.stationary_matrix_structure_of_allocation


#print axioms TwoStateQuantumEmbedding.ResetEndpoint.spectral_conjugate_det
#print axioms TwoStateQuantumEmbedding.ResetEndpoint.density_spectral_structure
#print axioms TwoStateQuantumEmbedding.ResetEndpoint.actual_saturation_stationary_structure


#check TwoStateQuantumEmbedding.ResetEndpoint.spectralBudget_log_ratio_tendsto_one
#check TwoStateQuantumEmbedding.ResetEndpoint.spectralBudget_inv_ratio_tendsto_one
#check TwoStateQuantumEmbedding.ResetEndpoint.budgetScaleChange_tendsto_one
#check TwoStateQuantumEmbedding.ResetEndpoint.envelope_to_actual_tolerance
#check TwoStateQuantumEmbedding.ResetEndpoint.rho_scaled_limit_of_actual
#check TwoStateQuantumEmbedding.ResetEndpoint.actual_saturation_allocation
#check TwoStateQuantumEmbedding.ResetEndpoint.spectral_conjugate_det
#check TwoStateQuantumEmbedding.ResetEndpoint.density_spectral_structure
#check TwoStateQuantumEmbedding.ResetEndpoint.actual_saturation_stationary_structure


