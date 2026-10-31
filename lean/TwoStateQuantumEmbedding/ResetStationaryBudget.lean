import TwoStateQuantumEmbedding.CPTP
import TwoStateQuantumEmbedding.ResetCore

noncomputable section
open Matrix Complex Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder

namespace TwoStateQuantumEmbedding.ResetEndpoint

/-- 正半定二阶矩阵的非对角元满足主子式界。 -/
theorem psd_offdiag_sq_le {M : QubitMatrix} (hM : M.PosSemidef) :
    ‖M 0 1‖ ^ 2 ≤ (M 0 0).re * (M 1 1).re := by
  have hd := (RCLike.nonneg_iff.mp hM.det_nonneg).1
  change 0 ≤ M.det.re at hd
  have h00 := (RCLike.nonneg_iff.mp (hM.diag_nonneg (i := 0))).2
  have h11 := (RCLike.nonneg_iff.mp (hM.diag_nonneg (i := 1))).2
  change (M 0 0).im = 0 at h00
  change (M 1 1).im = 0 at h11
  have h10 : M 1 0 = star (M 0 1) := (hM.isHermitian.apply 1 0).symm
  simp only [Matrix.det_fin_two, Complex.sub_re, Complex.mul_re, h00, h11,
    h10, Complex.star_def, Complex.conj_re, Complex.conj_im] at hd
  rw [Complex.sq_norm]
  simp only [Complex.normSq_apply]
  nlinarith

/-- 真实通道的测量泛函由一个正 effect 表示。 -/
theorem channel_measurement_effect (E : QubitMatrix →ₗ[ℂ] QubitMatrix)
    (hE : IsChannel E) :
    ∃ F : QubitMatrix, F.PosSemidef ∧ ∀ X, (E X) 0 0 = (F * X).trace := by
  obtain ⟨r, K, hK⟩ := hE.cp
  let P : QubitMatrix := Matrix.single 0 0 1
  let F : QubitMatrix := ∑ i : Fin r, (K i).conjTranspose * P * K i
  refine ⟨F, ?_, ?_⟩
  · exact Matrix.posSemidef_sum _ (fun i _ =>
      (basisProjector_posSemidef 0).conjTranspose_mul_mul_same (K i))
  · intro X
    calc
      (E X) 0 0 = (P * E X).trace := by simp [P, Matrix.trace_single_mul]
      _ = ∑ i : Fin r, (P * (K i * X * (K i).conjTranspose)).trace := by
        rw [hK, Matrix.mul_sum, Matrix.trace_sum]
      _ = ∑ i : Fin r, (((K i).conjTranspose * P * K i) * X).trace := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Matrix.mul_assoc P, Matrix.trace_mul_comm]
        simp only [Matrix.mul_assoc]
      _ = (F * X).trace := by
        change _ = ((∑ i : Fin r, (K i).conjTranspose * P * K i) * X).trace
        rw [Matrix.sum_mul, Matrix.trace_sum]

/-- 正 effect 与正密度矩阵的测量交叉项界。 -/
theorem psd_trace_mul_le_sqrt {F ρ : QubitMatrix}
    (hF : F.PosSemidef) (hρ : ρ.PosSemidef) :
    (F * ρ).trace.re ≤
      (Real.sqrt ((F 0 0).re * (ρ 0 0).re) +
       Real.sqrt ((F 1 1).re * (ρ 1 1).re)) ^ 2 := by
  have hf0 : 0 ≤ (F 0 0).re := (RCLike.nonneg_iff.mp (hF.diag_nonneg (i := 0))).1
  have hf1 : 0 ≤ (F 1 1).re := (RCLike.nonneg_iff.mp (hF.diag_nonneg (i := 1))).1
  have hr0 : 0 ≤ (ρ 0 0).re := (RCLike.nonneg_iff.mp (hρ.diag_nonneg (i := 0))).1
  have hr1 : 0 ≤ (ρ 1 1).re := (RCLike.nonneg_iff.mp (hρ.diag_nonneg (i := 1))).1
  have hF00 : (F 0 0).im = 0 := (RCLike.nonneg_iff.mp (hF.diag_nonneg (i := 0))).2
  have hF11 : (F 1 1).im = 0 := (RCLike.nonneg_iff.mp (hF.diag_nonneg (i := 1))).2
  have hF10 : F 1 0 = star (F 0 1) := (hF.isHermitian.apply 1 0).symm
  have hρ10 : ρ 1 0 = star (ρ 0 1) := (hρ.isHermitian.apply 1 0).symm
  have hFo := Real.le_sqrt_of_sq_le (psd_offdiag_sq_le hF)
  have hρo := Real.le_sqrt_of_sq_le (psd_offdiag_sq_le hρ)
  have hm := mul_le_mul hFo hρo (norm_nonneg (ρ 0 1))
    (Real.sqrt_nonneg ((F 0 0).re * (F 1 1).re))
  have hc : (F 0 1 * ρ 1 0).re ≤ ‖F 0 1‖ * ‖ρ 0 1‖ := by
    calc
      _ ≤ ‖F 0 1 * ρ 1 0‖ := Complex.re_le_norm _
      _ = _ := by rw [norm_mul, hρ10, norm_star]
  have hid :
      Real.sqrt ((F 0 0).re * (F 1 1).re) *
          Real.sqrt ((ρ 0 0).re * (ρ 1 1).re) =
        Real.sqrt ((F 0 0).re * (ρ 0 0).re) *
          Real.sqrt ((F 1 1).re * (ρ 1 1).re) := by
    rw [Real.sqrt_mul hf0, Real.sqrt_mul hr0, Real.sqrt_mul hf0, Real.sqrt_mul hf1]
    ring
  rw [hid] at hm
  have ht : (F * ρ).trace.re =
      (F 0 0).re * (ρ 0 0).re + (F 1 1).re * (ρ 1 1).re +
        2 * (F 0 1 * ρ 1 0).re := by
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two,
      hF10, hρ10, Complex.mul_re, hF00, hF11]
    ring
  have hs0 := Real.sq_sqrt (mul_nonneg hf0 hr0)
  have hs1 := Real.sq_sqrt (mul_nonneg hf1 hr1)
  rw [ht]
  nlinarith

/-- 任意真实量子通道的不动密度矩阵满足平方根测量界。 -/
theorem channel_fixed_measurement_sqrt
    (E : QubitMatrix →ₗ[ℂ] QubitMatrix) (hE : IsChannel E)
    (ρ : QubitMatrix) (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1)
    (hfix : E ρ = ρ) :
    (ρ 0 0).re ≤
      (Real.sqrt ((E (Matrix.single 0 0 1) 0 0).re * (ρ 0 0).re) +
       Real.sqrt ((E (Matrix.single 1 1 1) 0 0).re * (1 - (ρ 0 0).re))) ^ 2 := by
  obtain ⟨F, hF, hval⟩ := channel_measurement_effect E hE
  have hdiag (i : Fin 2) : (E (Matrix.single i i 1) 0 0).re = (F i i).re := by
    rw [hval, Matrix.trace_mul_comm, Matrix.trace_single_mul]
    simp
  have hr1 : (ρ 1 1).re = 1 - (ρ 0 0).re := by
    have ht := congrArg Complex.re htrace
    simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two] at ht
    linarith
  have ht : (F * ρ).trace.re = (ρ 0 0).re := by rw [← hval, hfix]
  simpa only [hdiag, hr1, ht] using psd_trace_mul_le_sqrt hF hρ

/-- 已从通道正性证明前提的精确稳态乘积预算。 -/
theorem channel_fixed_measurement_product
    (E : QubitMatrix →ₗ[ℂ] QubitMatrix) (hE : IsChannel E)
    (ρ : QubitMatrix) (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1)
    (hfix : E ρ = ρ) :
    ((1 - Real.sqrt (E (Matrix.single 0 0 1) 0 0).re) ^ 2 +
      (E (Matrix.single 1 1 1) 0 0).re) * (ρ 0 0).re ≤
        (E (Matrix.single 1 1 1) 0 0).re := by
  have hp := density_diagonal_mem_Icc hρ htrace 0
  have ha := density_diagonal_mem_Icc (hE.pos _ (basisProjector_posSemidef 0))
    (by rw [hE.tp, basisProjector_trace]) 0
  have he := density_diagonal_mem_Icc (hE.pos _ (basisProjector_posSemidef 1))
    (by rw [hE.tp, basisProjector_trace]) 0
  exact Reset.stationary_measurement_product _ _ _ ha.1 ha.2 he.1 hp.1 hp.2
    (channel_fixed_measurement_sqrt E hE ρ hρ htrace hfix)


/-- 测量人口预算的精确有理函数。 -/
def measurementBudget (ε : ℝ) : ℝ := ε / (1 - 2 * Real.sqrt ε + 2 * ε)

/-- 谱混合度与基倾角的联合预算。 -/
def spectralBudget (ε : ℝ) : ℝ := 1 - Real.sqrt (1 - 2 * measurementBudget ε)

theorem measurementBudget_denom_pos {ε : ℝ} (hε : 0 ≤ ε) :
    0 < 1 - 2 * Real.sqrt ε + 2 * ε := by
  have hs := Real.sq_sqrt hε
  nlinarith [sq_nonneg (Real.sqrt ε - 1 / 2)]

theorem measurementBudget_nonneg {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ measurementBudget ε := div_nonneg hε (measurementBudget_denom_pos hε).le

theorem measurementBudget_lt_half {ε : ℝ} (hε : 0 ≤ ε) (hε4 : ε < 1 / 4) :
    measurementBudget ε < 1 / 2 := by
  have hs := Real.sq_sqrt hε
  have hs0 := Real.sqrt_nonneg ε
  have hs1 : Real.sqrt ε < 1 / 2 := by nlinarith
  apply (div_lt_iff₀ (measurementBudget_denom_pos hε)).2
  nlinarith

/-- product 预算在相关区域 a≤ε 化为只依赖实际误差的界。 -/
theorem measurement_budget_upper {a ε pstar : ℝ}
    (ha : 0 ≤ a) (hε : 0 ≤ ε) (haε : a ≤ ε) (hε4 : ε < 1 / 4)
    (hpstar : 0 ≤ pstar)
    (hbudget : ((1 - Real.sqrt a) ^ 2 + ε) * pstar ≤ ε) :
    pstar ≤ measurementBudget ε := by
  have hsa := Real.sq_sqrt ha
  have hse := Real.sq_sqrt hε
  have hsa0 := Real.sqrt_nonneg a
  have hse0 := Real.sqrt_nonneg ε
  have hsae := Real.sqrt_le_sqrt haε
  have hse1 : Real.sqrt ε < 1 / 2 := by nlinarith
  have hc : 1 - 2 * Real.sqrt ε + 2 * ε ≤ (1 - Real.sqrt a) ^ 2 + ε := by
    have hm := mul_nonneg (sub_nonneg.mpr hsae)
      (show 0 ≤ 2 - Real.sqrt ε - Real.sqrt a by linarith)
    nlinarith
  apply (le_div_iff₀ (measurementBudget_denom_pos hε)).2
  have hm := mul_le_mul_of_nonneg_right hc hpstar
  nlinarith

/-- 显式谱人口恒等式推出各误差与联合误差的精确预算。 -/
theorem spectral_budget_of_population {ε pstar ν p : ℝ}
    (hε : 0 ≤ ε) (hε4 : ε < 1 / 4)
    (hν : 0 ≤ ν) (hνhalf : ν ≤ 1 / 2) (hp : 0 ≤ p)
    (hidentity : pstar = ν + (1 - 2 * ν) * p)
    (hpop : pstar ≤ measurementBudget ε) :
    ν ≤ measurementBudget ε ∧ p ≤ measurementBudget ε ∧
      ν < 1 / 2 ∧ p < 1 / 2 ∧ p + ν ≤ spectralBudget ε := by
  have hu0 := measurementBudget_nonneg hε
  have hu1 := measurementBudget_lt_half hε hε4
  have hstar : pstar < 1 / 2 := lt_of_le_of_lt hpop hu1
  have hνstar : ν ≤ pstar := by
    have hm := mul_nonneg (show 0 ≤ 1 - 2 * ν by linarith) hp
    nlinarith
  have hνlt : ν < 1 / 2 := lt_of_le_of_lt hνstar hstar
  have hplt : p < 1 / 2 := by
    by_contra hh
    have hm := mul_nonneg (show 0 ≤ 1 - 2 * ν by linarith)
      (show 0 ≤ p - 1 / 2 by linarith)
    nlinarith
  have hpstar : p ≤ pstar := by
    have hm := mul_nonneg hν (show 0 ≤ 1 - 2 * p by linarith)
    nlinarith
  refine ⟨hνstar.trans hpop, hpstar.trans hpop, hνlt, hplt, ?_⟩
  have hs : 0 ≤ 1 - (p + ν) := by linarith
  have hq : 1 - 2 * measurementBudget ε ≤ (1 - (p + ν)) ^ 2 := by
    nlinarith [sq_nonneg (p - ν)]
  have hroot := Real.sq_sqrt (show 0 ≤ 1 - 2 * measurementBudget ε by linarith)
  have hle : Real.sqrt (1 - 2 * measurementBudget ε) ≤ 1 - (p + ν) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) hs).mp
    nlinarith
  unfold spectralBudget
  linarith

/-- 对任意固定密度矩阵及其显式谱人口数据的真实通道联合预算。 -/
theorem channel_fixed_spectral_budget
    (E : QubitMatrix →ₗ[ℂ] QubitMatrix) (hE : IsChannel E)
    (ρ : QubitMatrix) (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1)
    (hfix : E ρ = ρ) (ν p : ℝ)
    (hν : 0 ≤ ν) (hνhalf : ν ≤ 1 / 2) (hp : 0 ≤ p)
    (hspectral : (ρ 0 0).re = ν + (1 - 2 * ν) * p)
    (haε : (E (Matrix.single 0 0 1) 0 0).re ≤ (E (Matrix.single 1 1 1) 0 0).re)
    (hε4 : (E (Matrix.single 1 1 1) 0 0).re < 1 / 4) :
    p + ν ≤ spectralBudget (E (Matrix.single 1 1 1) 0 0).re := by
  have hpstar := density_diagonal_mem_Icc hρ htrace 0
  have ha := density_diagonal_mem_Icc (hE.pos _ (basisProjector_posSemidef 0))
    (by rw [hE.tp, basisProjector_trace]) 0
  have he := density_diagonal_mem_Icc (hE.pos _ (basisProjector_posSemidef 1))
    (by rw [hE.tp, basisProjector_trace]) 0
  have hpop := measurement_budget_upper ha.1 he.1 haε hε4 hpstar.1
    (channel_fixed_measurement_product E hE ρ hρ htrace hfix)
  exact (spectral_budget_of_population he.1 hε4 hν hνhalf hp hspectral hpop).2.2.2.2

/-- 根式反演在全区间 0≤u≤1/2 的显式二阶余项。 -/
theorem sqrt_inversion_bounds {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    u ≤ 1 - Real.sqrt (1 - 2 * u) ∧
      1 - Real.sqrt (1 - 2 * u) ≤ u + 2 * u ^ 2 := by
  have hs0 := Real.sqrt_nonneg (1 - 2 * u)
  have hs2 := Real.sq_sqrt (show 0 ≤ 1 - 2 * u by linarith)
  have hs1 : Real.sqrt (1 - 2 * u) ≤ 1 := by nlinarith
  have hslow : 1 - 2 * u ≤ Real.sqrt (1 - 2 * u) := by
    have hm := mul_nonneg hs0 (show 0 ≤ 1 - Real.sqrt (1 - 2 * u) by linarith)
    nlinarith
  have hr0 : 0 ≤ 1 - Real.sqrt (1 - 2 * u) := by linarith
  have hr2 : 1 - Real.sqrt (1 - 2 * u) ≤ 2 * u := by linarith
  have hr2sq := (sq_le_sq₀ hr0 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hu)).mpr hr2
  constructor <;> nlinarith [sq_nonneg (1 - Real.sqrt (1 - 2 * u))]

/-- 0≤ε≤1/64 时的统一显式渐近预算；常数 8 不依赖任何生成元参数。 -/
theorem spectralBudget_explicit {ε : ℝ} (hε : 0 ≤ ε) (hε64 : ε ≤ 1 / 64) :
    ε ≤ spectralBudget ε ∧ spectralBudget ε ≤ ε * (1 + 8 * Real.sqrt ε) := by
  let u := measurementBudget ε
  have hu0 : 0 ≤ u := measurementBudget_nonneg hε
  have hu1 : u < 1 / 2 := measurementBudget_lt_half hε (by linarith)
  have hd := measurementBudget_denom_pos hε
  have hs := Real.sq_sqrt hε
  have hs0 := Real.sqrt_nonneg ε
  have hs8 : Real.sqrt ε ≤ 1 / 8 := by nlinarith
  have hεs : ε ≤ Real.sqrt ε / 8 := by
    have hm := mul_nonneg hs0 (show 0 ≤ 1 / 8 - Real.sqrt ε by linarith)
    nlinarith
  have heq : u * (1 - 2 * Real.sqrt ε + 2 * ε) = ε := by
    dsimp [u, measurementBudget]
    exact div_mul_cancel₀ ε hd.ne'
  have hdhalf : 1 / 2 ≤ 1 - 2 * Real.sqrt ε + 2 * ε := by
    nlinarith [sq_nonneg (Real.sqrt ε - 1 / 2)]
  have hu2 : u ≤ 2 * ε := by
    have hm := mul_le_mul_of_nonneg_left hdhalf hu0
    nlinarith
  have hde1 : 1 - 2 * Real.sqrt ε + 2 * ε ≤ 1 := by linarith
  have hεu : ε ≤ u := by
    have hm := mul_le_mul_of_nonneg_left hde1 hu0
    nlinarith
  have hcorrection : u ≤ ε + 4 * ε * Real.sqrt ε := by
    have hm := mul_le_mul_of_nonneg_right hu2 hs0
    nlinarith [mul_nonneg hu0 hε]
  have hub := sqrt_inversion_bounds hu0 hu1.le
  have hu2sq : u ^ 2 ≤ 4 * ε ^ 2 := by
    have hh := (sq_le_sq₀ hu0 (show 0 ≤ 2 * ε by positivity)).mpr hu2
    nlinarith
  have heps2 := mul_le_mul_of_nonneg_left hεs hε
  change ε ≤ 1 - Real.sqrt (1 - 2 * u) ∧
    1 - Real.sqrt (1 - 2 * u) ≤ ε * (1 + 8 * Real.sqrt ε)
  constructor
  · exact hεu.trans hub.1
  · nlinarith [mul_nonneg hε hs0]

/-- 正式的大 O 陈述：rho(ε)=ε+O(ε sqrt ε)，取右侧极限。 -/
theorem spectralBudget_sub_isBigO :
    Asymptotics.IsBigO (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (fun ε => spectralBudget ε - ε) (fun ε => ε * Real.sqrt ε) := by
  apply Asymptotics.IsBigO.of_bound 8
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 64 by norm_num)] with ε hε
  have hb := spectralBudget_explicit hε.1.le hε.2.le
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hb.1), Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hε.1.le (Real.sqrt_nonneg ε))]
  nlinarith [hb.2]

/-- 用于后续比较系统的一个统一小误差域。 -/
theorem uniform_small_spectral_budget {ε ν p : ℝ}
    (hε : 0 ≤ ε) (hε1024 : ε ≤ 1 / 1024) (hν : 0 ≤ ν) (hp : 0 ≤ p)
    (hbudget : ν + p ≤ spectralBudget ε) :
    ν + p ≤ 2 * ε ∧ ν ≤ 1 / 257 ∧
      Real.sqrt (ν / (1 - ν)) ≤ 1 / 16 := by
  have hb := (spectralBudget_explicit hε (by linarith)).2
  have hs := Real.sq_sqrt hε
  have hs0 := Real.sqrt_nonneg ε
  have hs32 : Real.sqrt ε ≤ 1 / 32 := by nlinarith
  have hsum : ν + p ≤ 2 * ε := by
    have hm := mul_le_mul_of_nonneg_left hs32 hε
    nlinarith
  have hν257 : ν ≤ 1 / 257 := by linarith
  have hd : 0 < 1 - ν := by linarith
  have hratio : ν / (1 - ν) ≤ (1 / 16 : ℝ) ^ 2 := by
    apply (div_le_iff₀ hd).2
    nlinarith
  have hratio0 : 0 ≤ ν / (1 - ν) := div_nonneg hν hd.le
  refine ⟨hsum, hν257, ?_⟩
  have hsratio := Real.sq_sqrt hratio0
  have hsratio0 := Real.sqrt_nonneg (ν / (1 - ν))
  nlinarith

/-- 生成元零空间中的矩阵被真实指数演化固定，时间无需非负。 -/
theorem gksl_evolution_fixed_of_stationary {n : ℕ}
    (H : QubitMatrix) (A : Fin n → QubitMatrix) (ρ : QubitMatrix)
    (hstationary : gkslAction H A ρ = 0) (t : ℝ) :
    gkslSuperoperatorEvolution H A t ρ = ρ := by
  have h := congrArg (fun T : QubitMatrix →L[ℂ] QubitMatrix => T ρ)
    (expSemigroupCLM_sub_one_eq_intervalIntegral_mul (endEquiv (gkslLinearMap H A)) t)
  have hz : (endEquiv (gkslLinearMap H A)) ρ = 0 := hstationary
  simp only [_root_.sub_apply, one_apply_eq_self,
    mul_apply_eq_comp, hz, map_zero] at h
  exact sub_eq_zero.mp h

/-- 原模型输出第二对角概率的补数就是实际目标态扰动。 -/
theorem gksl_disturbance_eq_one_sub_output {n : ℕ}
    (H : QubitMatrix) (A : Fin n → QubitMatrix) (t : ℝ)
    (hH : H.IsHermitian) (ht : 0 ≤ t) :
    (gkslSuperoperatorEvolution H A t (Matrix.single 1 1 1) 0 0).re =
      1 - (finiteOutput H A t).2 := by
  have htrace := gkslSuperoperatorEvolution_trace H A t hH ht (Matrix.single 1 1 1)
  rw [basisProjector_trace] at htrace
  have hs := congrArg Complex.re htrace
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two] at hs
  rw [finiteOutput_eq_superoperator_probabilities]
  dsimp
  linarith

/-- 原始 GKSL 参数及其任意稳态密度矩阵的精确预算。 -/
theorem gksl_stationary_measurement_product {n : ℕ}
    (H : QubitMatrix) (A : Fin n → QubitMatrix) (t : ℝ)
    (hH : H.IsHermitian) (ht : 0 ≤ t)
    (ρ : QubitMatrix) (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1)
    (hstationary : gkslAction H A ρ = 0) :
    ((1 - Real.sqrt (finiteOutput H A t).1) ^ 2 + (1 - (finiteOutput H A t).2)) *
      (ρ 0 0).re ≤ 1 - (finiteOutput H A t).2 := by
  have h := channel_fixed_measurement_product
    (gkslSuperoperatorEvolution H A t).toLinearMap
    (gkslSuperoperatorEvolution_isChannel H A t hH ht)
    ρ hρ htrace (gksl_evolution_fixed_of_stationary H A ρ hstationary t)
  change ((1 - Real.sqrt (gkslSuperoperatorEvolution H A t (Matrix.single 0 0 1) 0 0).re) ^ 2 +
    (gkslSuperoperatorEvolution H A t (Matrix.single 1 1 1) 0 0).re) * (ρ 0 0).re ≤
    (gkslSuperoperatorEvolution H A t (Matrix.single 1 1 1) 0 0).re at h
  rw [gksl_disturbance_eq_one_sub_output H A t hH ht] at h
  simpa only [finiteOutput_eq_superoperator_probabilities] using h

/-- 原模型稳态加显式谱人口恒等式给出同一联合预算。 -/
theorem gksl_stationary_spectral_budget {n : ℕ}
    (H : QubitMatrix) (A : Fin n → QubitMatrix) (t : ℝ)
    (hH : H.IsHermitian) (ht : 0 ≤ t)
    (ρ : QubitMatrix) (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1)
    (hstationary : gkslAction H A ρ = 0) (ν p : ℝ)
    (hν : 0 ≤ ν) (hνhalf : ν ≤ 1 / 2) (hp : 0 ≤ p)
    (hspectral : (ρ 0 0).re = ν + (1 - 2 * ν) * p)
    (haε : (finiteOutput H A t).1 ≤ 1 - (finiteOutput H A t).2)
    (hε4 : 1 - (finiteOutput H A t).2 < 1 / 4) :
    p + ν ≤ spectralBudget (1 - (finiteOutput H A t).2) := by
  have hout := finiteOutput_mem_unitSquare H A t hH ht
  have he : 0 ≤ 1 - (finiteOutput H A t).2 := by linarith [hout.2.2]
  have hpstar := density_diagonal_mem_Icc hρ htrace 0
  have hpop := measurement_budget_upper hout.1.1 he haε hε4 hpstar.1
    (gksl_stationary_measurement_product H A t hH ht ρ hρ htrace hstationary)
  exact (spectral_budget_of_population he hε4 hν hνhalf hp hspectral hpop).2.2.2.2


/-- 正误差上 rho/ε−1 的相对大 O 版本。 -/
theorem spectralBudget_ratio_sub_isBigO :
    Asymptotics.IsBigO (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (fun ε => spectralBudget ε / ε - 1) Real.sqrt := by
  apply Asymptotics.IsBigO.of_bound 8
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 64 by norm_num)] with ε hε
  have hb := spectralBudget_explicit hε.1.le hε.2.le
  have hlo : 1 ≤ spectralBudget ε / ε := by
    apply (le_div_iff₀ hε.1).2
    simpa using hb.1
  have hhi : spectralBudget ε / ε ≤ 1 + 8 * Real.sqrt ε := by
    apply (div_le_iff₀ hε.1).2
    nlinarith [hb.2]
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hlo), Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg ε)]
  linarith

/-- 精确预算与实际误差之比趋向 1。 -/
theorem spectralBudget_ratio_tendsto_one :
    Filter.Tendsto (fun ε => spectralBudget ε / ε)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
  have hsqrt : Filter.Tendsto Real.sqrt (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h : Filter.Tendsto Real.sqrt (nhds (0 : ℝ)) (nhds (Real.sqrt 0)) :=
      Real.continuous_sqrt.continuousAt.tendsto
    simpa using h.mono_left
      (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0)
  have hu : Filter.Tendsto (fun ε => 1 + 8 * Real.sqrt ε)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
    convert tendsto_const_nhds.add (tendsto_const_nhds.mul hsqrt) using 1 <;> norm_num
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 64 by norm_num)] with ε hε
    apply (le_div_iff₀ hε.1).2
    simpa using (spectralBudget_explicit hε.1.le hε.2.le).1
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 64 by norm_num)] with ε hε
    apply (div_le_iff₀ hε.1).2
    nlinarith [(spectralBudget_explicit hε.1.le hε.2.le).2]


end TwoStateQuantumEmbedding.ResetEndpoint

#print axioms TwoStateQuantumEmbedding.ResetEndpoint.psd_offdiag_sq_le
#print axioms TwoStateQuantumEmbedding.ResetEndpoint.channel_measurement_effect


#print axioms TwoStateQuantumEmbedding.ResetEndpoint.channel_fixed_measurement_product


#print axioms TwoStateQuantumEmbedding.ResetEndpoint.spectral_budget_of_population
#print axioms TwoStateQuantumEmbedding.ResetEndpoint.channel_fixed_spectral_budget
#print axioms TwoStateQuantumEmbedding.ResetEndpoint.spectralBudget_explicit
#print axioms TwoStateQuantumEmbedding.ResetEndpoint.spectralBudget_sub_isBigO
#print axioms TwoStateQuantumEmbedding.ResetEndpoint.uniform_small_spectral_budget
#print axioms TwoStateQuantumEmbedding.ResetEndpoint.gksl_evolution_fixed_of_stationary
#print axioms TwoStateQuantumEmbedding.ResetEndpoint.gksl_stationary_measurement_product
#print axioms TwoStateQuantumEmbedding.ResetEndpoint.gksl_stationary_spectral_budget


#print axioms TwoStateQuantumEmbedding.ResetEndpoint.spectralBudget_ratio_sub_isBigO
#print axioms TwoStateQuantumEmbedding.ResetEndpoint.spectralBudget_ratio_tendsto_one


#check TwoStateQuantumEmbedding.ResetEndpoint.channel_fixed_measurement_product
#check TwoStateQuantumEmbedding.ResetEndpoint.gksl_evolution_fixed_of_stationary
#check TwoStateQuantumEmbedding.ResetEndpoint.gksl_stationary_measurement_product
#check TwoStateQuantumEmbedding.ResetEndpoint.gksl_stationary_spectral_budget
#check TwoStateQuantumEmbedding.ResetEndpoint.spectral_budget_of_population
#check TwoStateQuantumEmbedding.ResetEndpoint.spectralBudget_explicit
#check TwoStateQuantumEmbedding.ResetEndpoint.uniform_small_spectral_budget
#check TwoStateQuantumEmbedding.ResetEndpoint.spectralBudget_sub_isBigO
#check TwoStateQuantumEmbedding.ResetEndpoint.spectralBudget_ratio_sub_isBigO
#check TwoStateQuantumEmbedding.ResetEndpoint.spectralBudget_ratio_tendsto_one

