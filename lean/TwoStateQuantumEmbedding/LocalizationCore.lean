import TwoStateQuantumEmbedding.SwapCore
import TwoStateQuantumEmbedding.GKSLNormBounds
import TwoStateQuantumEmbedding.CanonicalRigidity
import TwoStateQuantumEmbedding.AzimuthGauge

/-! 全部近最优生成元的统一常数与谱能量定位。 -/
noncomputable section
open Matrix Complex
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

namespace TwoStateQuantumEmbedding.NearSwap
open GKSLAlgebra GKSLBounds CanonicalBloch
set_option maxRecDepth 2500
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def scale : ℝ := 16 / 3
def energyConstant (C : ℝ) : ℝ := Swap.localizationConstant C scale
def probabilityConstant (C : ℝ) : ℝ := 2 * energyConstant C / Swap.gap
def errorConstant (C : ℝ) : ℝ :=
  34 * scale * Real.sqrt (probabilityConstant C) + 8 * scale ^ 2
def radius (C : ℝ) : ℝ := min (1 / 128)
  (min (Swap.gap / (2 * C))
    (min (1 / (2 * (probabilityConstant C + errorConstant C)))
      (Swap.gap / (24 * energyConstant C))))

theorem energyConstant_pos (C : ℝ) (hC : 0 < C) : 0 < energyConstant C := by
  have hg := Swap.gap_pos
  have hr := Swap.slope_pos
  unfold energyConstant Swap.localizationConstant
  positivity

theorem probabilityConstant_pos (C : ℝ) (hC : 0 < C) : 0 < probabilityConstant C :=
  div_pos (mul_pos (by norm_num) (energyConstant_pos C hC)) Swap.gap_pos

theorem errorConstant_pos (C : ℝ) : 0 < errorConstant C := by
  unfold errorConstant scale
  positivity

theorem radius_pos (C : ℝ) (hC : 0 < C) : 0 < radius C := by
  have hL := energyConstant_pos C hC
  have hP := probabilityConstant_pos C hC
  have hE := errorConstant_pos C
  have hA := Swap.gap_pos
  unfold radius
  positivity

theorem radius_bounds (C b : ℝ) (hb : b ≤ radius C) :
    b ≤ 1 / 128 ∧ b ≤ Swap.gap / (2 * C) ∧
      b ≤ 1 / (2 * (probabilityConstant C + errorConstant C)) ∧
      b ≤ Swap.gap / (24 * energyConstant C) := by
  simpa only [radius, le_min_iff] using hb

theorem probabilityConstant_mul_gap (C : ℝ) :
    probabilityConstant C * Swap.gap = 2 * energyConstant C := by
  exact div_mul_cancel₀ _ Swap.gap_pos.ne'

/-- 对每个圈数都成立的参考读出粗上界。 -/
theorem qb_le_twice_mass (j : ℕ) (v : Fin 3 → ℂ) : Swap.qb j v ≤ 2 * Swap.mass v := by
  have hc0 : 0 ≤ 4 / Swap.frequency j := by positivity [Swap.frequency_pos j]
  have hc : 4 / Swap.frequency j ≤ Swap.rootTwo := by
    apply (div_le_iff₀ (Swap.frequency_pos j)).mpr
    have hh := mul_le_mul_of_nonneg_left (Swap.frequency_ge_pi j) Swap.rootTwo_pos.le
    have hp := mul_lt_mul_of_pos_left Swap.twice_rootTwo_lt_pi Swap.rootTwo_pos
    nlinarith [Swap.rootTwo_sq]
  have hcross : (4 / Swap.frequency j) * Swap.cross v ≤ Swap.energy v := by
    by_cases hh : 0 ≤ Swap.cross v
    · have hm := mul_le_mul_of_nonneg_right hc hh
      have hs := Swap.squareMinus_nonneg v
      rw [Swap.squareMinus_identity] at hs
      linarith
    · have hm := mul_nonpos_of_nonneg_of_nonpos hc0 (le_of_not_ge hh)
      exact hm.trans (Swap.energy_nonneg v)
  have he : Swap.energy v ≤ Swap.mass v := by
    unfold Swap.energy Swap.mass
    nlinarith [Complex.normSq_nonneg (v 1), Complex.normSq_nonneg (v 2)]
  unfold Swap.qb
  linarith

theorem perpendicularMass_nonneg (v : Fin 3 → ℂ) : 0 ≤ Swap.perpendicularMass v := by
  unfold Swap.perpendicularMass
  exact add_nonneg (mul_nonneg (by norm_num) (Complex.normSq_nonneg _))
    (Complex.normSq_nonneg _)

/-- 论文首圈零方向的正交投影补。 -/
def perpendicularProjector : Matrix (Fin 3) (Fin 3) ℂ :=
  !![2/3, 0, ((Swap.rootTwo/3 : ℝ) : ℂ)*I;
     0, 1, 0;
     -((Swap.rootTwo/3 : ℝ) : ℂ)*I, 0, 1/3]

def kernelProjector : Matrix (Fin 3) (Fin 3) ℂ := 1 - perpendicularProjector

theorem perpendicularProjector_hermitian : perpendicularProjector.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [perpendicularProjector, Matrix.conjTranspose_apply]

theorem perpendicularProjector_idempotent : perpendicularProjector * perpendicularProjector =
    perpendicularProjector := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [perpendicularProjector, Matrix.mul_apply, Fin.sum_univ_three,
      Complex.mul_re, Complex.mul_im] <;>
    nlinarith [Swap.rootTwo_sq]

theorem perpendicularProjector_form (v : Fin 3 → ℂ) :
    star v ⬝ᵥ (perpendicularProjector *ᵥ v) = ((Swap.perpendicularMass v : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [perpendicularProjector, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Swap.perpendicularMass, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  all_goals ring_nf
  all_goals simp [Swap.rootTwo_sq]
  all_goals ring

theorem perpendicularProjector_posSemidef : perpendicularProjector.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg perpendicularProjector_hermitian
  intro v
  rw [perpendicularProjector_form]
  exact_mod_cast perpendicularMass_nonneg v

/-- 两种正式模块的 Gram 矩阵定义确实一致。 -/
theorem gram_eq {n : ℕ} (v : Fin n → Fin 3 → ℂ) :
    Swap.kossakowski v = GKSLAlgebra.kossakowski v := by
  ext i j
  simp [Swap.kossakowski, GKSLAlgebra.kossakowski, Matrix.vecMulVec, Matrix.sum_apply]

theorem traceQa_gram {n : ℕ} (j : ℕ) (v : Fin n → Fin 3 → ℂ) :
    (Swap.matrixQa j * GKSLAlgebra.kossakowski v).trace.re = ∑ l, Swap.qa j (v l) := by
  rw [← gram_eq, Swap.trace_Qa_kossakowski]
  rfl

theorem traceQb_gram {n : ℕ} (j : ℕ) (v : Fin n → Fin 3 → ℂ) :
    (Swap.matrixQb j * GKSLAlgebra.kossakowski v).trace.re = ∑ l, Swap.qb j (v l) := by
  rw [← gram_eq, Swap.trace_Qb_kossakowski]
  rfl

theorem dissipation_gram {n : ℕ} (v : Fin n → Fin 3 → ℂ) :
    dissipationSize (GKSLAlgebra.kossakowski v) = ∑ l, Swap.mass (v l) := by
  rw [dissipationSize, Rigidity.trace_realPart, ← gram_eq, Swap.trace_kossakowski]
  rfl

theorem tracePerp_gram {n : ℕ} (v : Fin n → Fin 3 → ℂ) :
    (perpendicularProjector * GKSLAlgebra.kossakowski v).trace.re =
      ∑ l, Swap.perpendicularMass (v l) := by
  rw [← gram_eq]
  simp only [Swap.kossakowski, Finset.mul_sum, Matrix.trace_sum, Complex.re_sum,
    Swap.trace_matrix_outer, perpendicularProjector_form, Complex.ofReal_re]

/-- 阶段性代数接口；实际余项会在最终定理中由 B2 提供。 -/
theorem gram_localization_of_remainders {n j : ℕ} (v : Fin n → Fin 3 → ℂ)
    (C a b p d Ra Rb : ℝ) (hC : 0 < C) (hb : 0 < b) (hsmall : b ≤ radius C)
    (hp : 0 ≤ p) (hd : 0 ≤ d) (hmass : d = ∑ l, Swap.mass (v l))
    (ha : a = p + (∑ l, Swap.qa j (v l)) + Ra)
    (hbexp : b = p + (∑ l, Swap.qb j (v l)) + Rb)
    (hRa : |Ra| ≤ Swap.remainderSize p d) (hRb : |Rb| ≤ Swap.remainderSize p d)
    (hnear : a ≤ Swap.slope * b + C * b ^ 2) (hscale : d ≤ scale * b) :
    j = 0 ∧ p ≤ probabilityConstant C * b ^ 2 ∧ b / 4 ≤ d ∧
      (∑ l, Swap.perpendicularMass (v l)) ≤ probabilityConstant C * b ^ 2 := by
  have hL := energyConstant_pos C hC
  have hP := probabilityConstant_pos C hC
  have hE := errorConstant_pos C
  have hA := Swap.gap_pos
  have hPG := probabilityConstant_mul_gap C
  obtain ⟨_, _, hsmallPE, hsmallL⟩ := radius_bounds C b hsmall
  have he := Swap.localization_energy v a b p d Ra Rb C scale hp hd ha hbexp
    hRa hRb hnear hscale
  change (Swap.gap / 2) * p +
      (∑ l, (Swap.qa j (v l) - Swap.slope * Swap.qb j (v l))) ≤ energyConstant C * b ^ 2 at he
  have hsum : 0 ≤ ∑ l, (Swap.qa j (v l) - Swap.slope * Swap.qb j (v l)) :=
    Finset.sum_nonneg (fun l _ => sub_nonneg.mpr (Swap.all_frequency_sharp j (v l)))
  have hpb : p ≤ probabilityConstant C * b ^ 2 := by
    have hm := congrArg (fun x : ℝ => x * b ^ 2) hPG
    nlinarith
  have hsqrt : Real.sqrt p ≤ Real.sqrt (probabilityConstant C) * b := by
    have hsq : (Real.sqrt (probabilityConstant C) * b) ^ 2 = probabilityConstant C * b ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hP.le]
    nlinarith [Real.sq_sqrt hp, Real.sqrt_nonneg p,
      mul_nonneg (Real.sqrt_nonneg (probabilityConstant C)) hb.le]
  have herr : Swap.remainderSize p d ≤ errorConstant C * b ^ 2 := by
    have hm := mul_le_mul hscale hsqrt (Real.sqrt_nonneg p) (by dsimp [scale]; positivity)
    have hsq : d ^ 2 ≤ (scale * b) ^ 2 := (sq_le_sq₀ hd (by dsimp [scale]; positivity)).mpr hscale
    unfold Swap.remainderSize errorConstant
    nlinarith
  have hqsum : (∑ l, Swap.qb j (v l)) ≤ 2 * d := by
    rw [hmass, Finset.mul_sum]
    exact Finset.sum_le_sum (fun l _ => qb_le_twice_mass j (v l))
  have hRbup : Rb ≤ errorConstant C * b ^ 2 := (le_abs_self Rb).trans (hRb.trans herr)
  have hsmallPE' : b * (2 * (probabilityConstant C + errorConstant C)) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp hsmallPE
  have hsmallPE'' := mul_le_mul_of_nonneg_right hsmallPE' hb.le
  have hdlow : b / 4 ≤ d := by nlinarith
  have hsmallL' : b * (24 * energyConstant C) ≤ Swap.gap :=
    (le_div_iff₀ (by positivity)).mp hsmallL
  have hj : j = 0 := by
    apply Swap.exclude_higher_frequencies v b p (energyConstant C) hb hp hL
    · apply (lt_div_iff₀ (by positivity : 0 < 12 * energyConstant C)).mpr
      nlinarith
    · simpa only [← hmass] using hdlow
    · exact he
  have hperp : (Swap.gap / 2) * (∑ l, Swap.perpendicularMass (v l)) ≤
      ∑ l, (Swap.qa 0 (v l) - Swap.slope * Swap.qb 0 (v l)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun l _ => Swap.first_frequency_gap (v l))
  rw [hj] at he
  have hpp := mul_nonneg (by positivity : 0 ≤ Swap.gap / 2) hp
  have hm := congrArg (fun x : ℝ => x * b ^ 2) hPG
  refine ⟨hj, hpb, hdlow, ?_⟩
  nlinarith

/-- 以上有限 Gram 组合覆盖任意真实 PSD K，无秩或跳跃数假设。 -/
theorem matrix_localization_of_remainders (K : Matrix (Fin 3) (Fin 3) ℂ)
    (hK : K.PosSemidef) (j : ℕ) (C a b p : ℝ)
    (hC : 0 < C) (hb : 0 < b) (hsmall : b ≤ radius C) (hp : 0 ≤ p)
    (hRa : |a - p - (Swap.matrixQa j * K).trace.re| ≤ Swap.remainderSize p (dissipationSize K))
    (hRb : |b - p - (Swap.matrixQb j * K).trace.re| ≤ Swap.remainderSize p (dissipationSize K))
    (hnear : a ≤ Swap.slope * b + C * b ^ 2) (hscale : dissipationSize K ≤ scale * b) :
    j = 0 ∧ p ≤ probabilityConstant C * b ^ 2 ∧ b / 4 ≤ dissipationSize K ∧
      (perpendicularProjector * K).trace.re ≤ probabilityConstant C * b ^ 2 := by
  obtain ⟨v, hv⟩ := exists_kossakowski_factor K hK
  have hd := dissipationSize_nonneg K hK
  have hmass : dissipationSize K = ∑ l, Swap.mass (v l) := by rw [← hv, dissipation_gram]
  have ha : a = p + (∑ l, Swap.qa j (v l)) + (a - p - (Swap.matrixQa j * K).trace.re) := by
    rw [← hv, traceQa_gram]
    ring
  have hbe : b = p + (∑ l, Swap.qb j (v l)) + (b - p - (Swap.matrixQb j * K).trace.re) := by
    rw [← hv, traceQb_gram]
    ring
  have hh := gram_localization_of_remainders v C a b p (dissipationSize K)
    (a - p - (Swap.matrixQa j * K).trace.re) (b - p - (Swap.matrixQb j * K).trace.re)
    hC hb hsmall hp hd hmass ha hbe hRa hRb hnear hscale
  simpa only [← tracePerp_gram, hv] using hh

theorem unitaryProbability_nonneg (h : BlochVec) : 0 ≤ unitaryProbability h 1 := by
  have hm := Q2_subset_unitSquare (canonicalOutput_mem_Q2 h 0 Matrix.PosSemidef.zero 1 (by norm_num))
  have he : (canonicalOutput h 0 1).1 = unitaryProbability h 1 := by
    simp [canonicalOutput, unitaryProbability, canonicalEvolution_zero_drift_column]
  rw [← he]
  exact hm.1.1

/-- 从真实概率和已经闭合的耗散刚性推出统一小耗散尺度。 -/
theorem canonical_near_scale (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ)
    (hK : K.PosSemidef) (C a b : ℝ) (hC : 0 < C) (hb : 0 < b)
    (hsmall : b ≤ radius C) (ha : a = (canonicalOutput h K 1).1)
    (hbe : b = (canonicalOutput h K 1).2) (hnear : a ≤ Swap.slope * b + C * b ^ 2) :
    0 ≤ a ∧ a < b ∧ a + b ≤ 1 / 64 ∧ dissipationSize K ≤ scale * b := by
  obtain ⟨hb128, hbC, _, _⟩ := radius_bounds C b hsmall
  have hCb : b * (2 * C) ≤ Swap.gap := (le_div_iff₀ (by positivity)).mp hbC
  have hCbb := mul_le_mul_of_nonneg_right hCb hb.le
  have hab : a < b := by
    have hgapb := mul_pos Swap.gap_pos hb
    unfold Swap.gap at *
    nlinarith
  have hsum : a + b ≤ 1 / 64 := by linarith
  have hm := Q2_subset_unitSquare (canonicalOutput_mem_Q2 h K hK 1 (by norm_num))
  have ha0 : 0 ≤ a := by rw [ha]; exact hm.1.1
  have hd := Rigidity.canonicalOutput_dissipative_rigidity h K hK (a + b)
    (by rw [ha, hbe]) (by linarith)
  have hdd : dissipationSize K ≤ (8 / 3) * (a + b) := by
    rw [dissipationSize, Rigidity.trace_realPart]
    exact hd.1.trans hd.2
  refine ⟨ha0, hab, hsum, ?_⟩
  dsimp [scale]
  linarith

theorem localized_probability_small (C b p : ℝ) (hC : 0 < C) (hb : 0 < b)
    (hsmall : b ≤ radius C) (hp : p ≤ probabilityConstant C * b ^ 2) : p ≤ 1 / 256 := by
  have hP := probabilityConstant_pos C hC
  have hE := errorConstant_pos C
  obtain ⟨hb128, _, hbPE, _⟩ := radius_bounds C b hsmall
  have hh : b * (2 * (probabilityConstant C + errorConstant C)) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp hbPE
  have hhb := mul_le_mul_of_nonneg_right hh hb.le
  nlinarith [mul_nonneg hE.le (sq_nonneg b)]

/-- j=0 后，B2 保留的角度与轴估计给出真实 Hamiltonian 坐标定位。 -/
theorem hamiltonian_coordinate_bounds (hx hz θ p : ℝ) (hhx : 0 ≤ hx) (hθ : 0 ≤ θ)
    (hθsq : (2 * θ) ^ 2 = hx ^ 2 + hz ^ 2) (hp : 0 ≤ p) (hpsmall : p ≤ 1 / 256)
    (hangle : |θ - Real.pi / 2| ≤ 2 * Real.sqrt p)
    (haxis : |hz| ≤ 2 * θ * Real.sqrt p) :
    0 < hx ∧ |hx - Real.pi| ≤ 12 * Real.sqrt p ∧ |hz| ≤ 8 * Real.sqrt p := by
  have hr := Real.sqrt_nonneg p
  have hr2 := Real.sq_sqrt hp
  have hrsmall : Real.sqrt p ≤ 1 / 16 := by nlinarith
  have hθup : θ ≤ 4 := by
    have hh := (abs_le.mp hangle).2
    linarith [Real.pi_lt_four]
  have hhz : |hz| ≤ 8 * Real.sqrt p := by
    have hh := mul_le_mul_of_nonneg_right hθup hr
    linarith
  have hxle : hx ≤ 2 * θ := by nlinarith [sq_nonneg hz]
  have hxlo : 2 * θ ≤ hx + |hz| := by
    have hh := mul_nonneg hhx (abs_nonneg hz)
    nlinarith [sq_abs hz, abs_nonneg hz]
  have hxx : |hx - Real.pi| ≤ 12 * Real.sqrt p := by
    obtain ⟨ha1, ha2⟩ := abs_le.mp hangle
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  refine ⟨?_, hxx, hhz⟩
  have hh := (abs_le.mp hxx).1
  linarith [Real.pi_gt_three]

theorem hamiltonian_norm_bound (hx hz p : ℝ)
    (hxerr : |hx - Real.pi| ≤ 12 * Real.sqrt p) (hzerr : |hz| ≤ 8 * Real.sqrt p) :
    ‖euclid ![hx, 0, hz] - euclid ![Real.pi, 0, 0]‖ ≤ 20 * Real.sqrt p := by
  have hx2 := (sq_le_sq₀ (abs_nonneg (hx - Real.pi)) (by positivity : 0 ≤ 12 * Real.sqrt p)).mpr hxerr
  have hz2 := (sq_le_sq₀ (abs_nonneg hz) (by positivity : 0 ≤ 8 * Real.sqrt p)).mpr hzerr
  rw [sq_abs] at hx2 hz2
  have hn : ‖euclid ![hx, 0, hz] - euclid ![Real.pi, 0, 0]‖ ^ 2 =
      (hx - Real.pi) ^ 2 + hz ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [euclid, Fin.sum_univ_three]
  nlinarith [norm_nonneg (euclid ![hx, 0, hz] - euclid ![Real.pi, 0, 0]), Real.sqrt_nonneg p]

/-- 同时提供用于有限维紧参数盒的通常 Pi 范数界。 -/
theorem hamiltonian_pi_norm_bound (hx hz p : ℝ) (hp : 0 ≤ p) (hpmax : p ≤ 1 / 256)
    (hxerr : |hx - Real.pi| ≤ 12 * Real.sqrt p) (hzerr : |hz| ≤ 8 * Real.sqrt p) :
    ‖(![hx, 0, hz] : BlochVec)‖ ≤ 6 := by
  have hr : Real.sqrt p ≤ 1 / 16 := by
    nlinarith [Real.sq_sqrt hp, Real.sqrt_nonneg p]
  have hhx : |hx| ≤ 6 := by
    have ht := abs_add_le (hx - Real.pi) Real.pi
    rw [abs_of_pos Real.pi_pos] at ht
    have he : hx - Real.pi + Real.pi = hx := by ring
    rw [he] at ht
    linarith [Real.pi_lt_four]
  have hhz : |hz| ≤ 6 := by linarith
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)).mpr
  intro i
  fin_cases i <;> simp only [Real.norm_eq_abs]
  · exact hhx
  · norm_num
  · exact hhz

def complexEuclid (v : Fin 3 → ℂ) : EuclideanSpace ℂ (Fin 3) := WithLp.toLp 2 v

theorem complexEuclid_norm_sq (v : Fin 3 → ℂ) :
    ‖complexEuclid v‖ ^ 2 = Swap.mass v := by
  simp [EuclideanSpace.norm_sq_eq, complexEuclid, Fin.sum_univ_three,
    Complex.sq_norm, Swap.mass, add_assoc]

theorem outer_toCLM (u v : Fin 3 → ℂ) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (Matrix.vecMulVec u (star v)) =
      InnerProductSpace.rankOne ℂ (complexEuclid u) (complexEuclid v) := by
  apply ContinuousLinearMap.coe_injective
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
  have hh := InnerProductSpace.symm_toEuclideanLin_rankOne (complexEuclid u) (complexEuclid v)
  have he := congrArg (Matrix.toEuclideanLin (𝕜 := ℂ)) hh
  simpa only [LinearEquiv.apply_symm_apply, complexEuclid, WithLp.ofLp_toLp] using he.symm

theorem norm_outer (u v : Fin 3 → ℂ) :
    ‖Matrix.vecMulVec u (star v)‖ = ‖complexEuclid u‖ * ‖complexEuclid v‖ := by
  rw [Matrix.cstar_norm_def, outer_toCLM, InnerProductSpace.norm_rankOne]

theorem psd_norm_le_dissipation (K : Matrix (Fin 3) (Fin 3) ℂ) (hK : K.PosSemidef) :
    ‖K‖ ≤ dissipationSize K := by
  obtain ⟨v, hv⟩ := exists_kossakowski_factor K hK
  have he : K = ∑ l, Matrix.vecMulVec (v l) (star (v l)) := by
    change K = Swap.kossakowski v
    rw [gram_eq, hv]
  have hd : dissipationSize K = ∑ l, Swap.mass (v l) := by rw [← hv, dissipation_gram]
  rw [hd, he]
  calc
    _ ≤ ∑ l, ‖Matrix.vecMulVec (v l) (star (v l))‖ := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l _
      rw [norm_outer, ← pow_two, complexEuclid_norm_sq]

theorem kernelProjector_eq_outer : kernelProjector =
    ((2 / 3 : ℝ) : ℂ) • Matrix.vecMulVec Swap.kernelVector (star Swap.kernelVector) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [kernelProjector, perpendicularProjector, Swap.kernelVector, Matrix.vecMulVec,
      Matrix.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im, map_ofNat]
  all_goals nlinarith [Swap.rootTwo_sq]

theorem norm_kernelProjector : ‖kernelProjector‖ = 1 := by
  rw [kernelProjector_eq_outer, norm_smul, norm_outer, ← pow_two, complexEuclid_norm_sq]
  simp [Swap.mass, Swap.kernelVector, Complex.normSq_apply]
  nlinarith [Swap.rootTwo_sq]

theorem perpendicular_action_mass (v : Fin 3 → ℂ) :
    Swap.mass (perpendicularProjector *ᵥ v) = Swap.perpendicularMass v := by
  simp [perpendicularProjector, Swap.mass, Swap.perpendicularMass, Matrix.mulVec,
    dotProduct, Fin.sum_univ_three, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring_nf
  simp [Swap.rootTwo_sq]
  ring

theorem parallel_action_mass (v : Fin 3 → ℂ) :
    Swap.mass (kernelProjector *ᵥ v) = Swap.parallelMass v := by
  simp [kernelProjector, perpendicularProjector, Swap.mass, Swap.parallelMass, Matrix.mulVec,
    dotProduct, Fin.sum_univ_three, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring_nf
  simp [Swap.rootTwo_sq]
  ring

theorem projected_outer (v : Fin 3 → ℂ) :
    Matrix.vecMulVec (kernelProjector *ᵥ v) (star (kernelProjector *ᵥ v)) =
      ((Swap.parallelMass v : ℝ) : ℂ) • kernelProjector := by
  have hcube : Swap.rootTwo ^ 3 = 2 * Swap.rootTwo := by rw [pow_succ, Swap.rootTwo_sq]
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [kernelProjector, perpendicularProjector, Matrix.vecMulVec, Swap.parallelMass,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.smul_apply,
      smul_eq_mul, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, map_ofNat]
  all_goals try ring_nf
  all_goals try simp only [Swap.rootTwo_sq, hcube]
  all_goals try ring_nf

theorem vector_split (v : Fin 3 → ℂ) :
    perpendicularProjector *ᵥ v + kernelProjector *ᵥ v = v := by
  rw [← Matrix.add_mulVec]
  have hh : perpendicularProjector + kernelProjector = 1 := by
    unfold kernelProjector
    abel
  rw [hh, Matrix.one_mulVec]

theorem outer_difference_split (v : Fin 3 → ℂ) :
    Matrix.vecMulVec v (star v) - ((Swap.mass v : ℝ) : ℂ) • kernelProjector =
      Matrix.vecMulVec (perpendicularProjector *ᵥ v) (star (perpendicularProjector *ᵥ v)) +
      Matrix.vecMulVec (perpendicularProjector *ᵥ v) (star (kernelProjector *ᵥ v)) +
      Matrix.vecMulVec (kernelProjector *ᵥ v) (star (perpendicularProjector *ᵥ v)) -
      ((Swap.perpendicularMass v : ℝ) : ℂ) • kernelProjector := by
  have hh : Matrix.vecMulVec v (star v) =
      Matrix.vecMulVec (perpendicularProjector *ᵥ v) (star (perpendicularProjector *ᵥ v)) +
      Matrix.vecMulVec (perpendicularProjector *ᵥ v) (star (kernelProjector *ᵥ v)) +
      Matrix.vecMulVec (kernelProjector *ᵥ v) (star (perpendicularProjector *ᵥ v)) +
      Matrix.vecMulVec (kernelProjector *ᵥ v) (star (kernelProjector *ᵥ v)) := by
    calc
      Matrix.vecMulVec v (star v) = Matrix.vecMulVec
          (perpendicularProjector *ᵥ v + kernelProjector *ᵥ v)
          (star (perpendicularProjector *ᵥ v + kernelProjector *ᵥ v)) :=
        congrArg (fun w => Matrix.vecMulVec w (star w)) (vector_split v).symm
      _ = _ := by
        simp only [star_add, Matrix.add_vecMulVec, Matrix.vecMulVec_add]
        abel
  rw [hh, projected_outer, Swap.mass_orthogonal_split, Complex.ofReal_add, add_smul]
  abel

theorem norm_outer_difference_le (v : Fin 3 → ℂ) :
    ‖Matrix.vecMulVec v (star v) - ((Swap.mass v : ℝ) : ℂ) • kernelProjector‖ ≤
      2 * Swap.perpendicularMass v +
        2 * Real.sqrt (Swap.perpendicularMass v) * Real.sqrt (Swap.mass v) := by
  have ht := perpendicularMass_nonneg v
  have hm := Swap.mass_nonneg v
  have hu : ‖complexEuclid (perpendicularProjector *ᵥ v)‖ = Real.sqrt (Swap.perpendicularMass v) := by
    rw [← perpendicular_action_mass, ← complexEuclid_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  have hw : ‖complexEuclid (kernelProjector *ᵥ v)‖ ≤ Real.sqrt (Swap.mass v) := by
    have hh := complexEuclid_norm_sq (kernelProjector *ᵥ v)
    rw [parallel_action_mass] at hh
    have hs := Swap.mass_orthogonal_split v
    nlinarith [Real.sq_sqrt hm, Real.sqrt_nonneg (Swap.mass v),
      norm_nonneg (complexEuclid (kernelProjector *ᵥ v))]
  rw [outer_difference_split]
  have hnorm := norm_sub_le
    (Matrix.vecMulVec (perpendicularProjector *ᵥ v) (star (perpendicularProjector *ᵥ v)) +
      Matrix.vecMulVec (perpendicularProjector *ᵥ v) (star (kernelProjector *ᵥ v)) +
      Matrix.vecMulVec (kernelProjector *ᵥ v) (star (perpendicularProjector *ᵥ v)))
    (((Swap.perpendicularMass v : ℝ) : ℂ) • kernelProjector)
  have htri := norm_add₃_le
    (a := Matrix.vecMulVec (perpendicularProjector *ᵥ v) (star (perpendicularProjector *ᵥ v)))
    (b := Matrix.vecMulVec (perpendicularProjector *ᵥ v) (star (kernelProjector *ᵥ v)))
    (c := Matrix.vecMulVec (kernelProjector *ᵥ v) (star (perpendicularProjector *ᵥ v)))
  simp only [norm_outer, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ht, norm_kernelProjector, mul_one, hu] at hnorm htri
  have hc := mul_le_mul_of_nonneg_left hw (Real.sqrt_nonneg (Swap.perpendicularMass v))
  nlinarith [Real.sq_sqrt ht]

/-- 任意 PSD 矩阵的实际 L2 范数集中；三列 Gram 分解保证常数与原跳跃数无关。 -/
theorem matrix_concentration_bound (K : Matrix (Fin 3) (Fin 3) ℂ) (hK : K.PosSemidef) :
    ‖K - ((dissipationSize K : ℝ) : ℂ) • kernelProjector‖ ≤
      2 * (perpendicularProjector * K).trace.re +
        6 * Real.sqrt ((perpendicularProjector * K).trace.re) * Real.sqrt (dissipationSize K) := by
  obtain ⟨v, hv⟩ := exists_kossakowski_factor K hK
  have hd : dissipationSize K = ∑ l, Swap.mass (v l) := by rw [← hv, dissipation_gram]
  have ht : (perpendicularProjector * K).trace.re = ∑ l, Swap.perpendicularMass (v l) := by
    rw [← hv, tracePerp_gram]
  have hsum : (∑ l, Matrix.vecMulVec (v l) (star (v l))) = K := by
    change Swap.kossakowski v = K
    rw [gram_eq, hv]
  have hc : (∑ l, ((Swap.mass (v l) : ℝ) : ℂ)) = ((dissipationSize K : ℝ) : ℂ) := by
    exact_mod_cast hd.symm
  have he : K - ((dissipationSize K : ℝ) : ℂ) • kernelProjector =
      ∑ l, (Matrix.vecMulVec (v l) (star (v l)) - ((Swap.mass (v l) : ℝ) : ℂ) • kernelProjector) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, hc]
  rw [he]
  apply (norm_sum_le _ _).trans
  have hi (l : Fin 3) :
      ‖Matrix.vecMulVec (v l) (star (v l)) - ((Swap.mass (v l) : ℝ) : ℂ) • kernelProjector‖ ≤
      2 * Swap.perpendicularMass (v l) +
        2 * Real.sqrt ((perpendicularProjector * K).trace.re) * Real.sqrt (dissipationSize K) := by
    have hiT : Swap.perpendicularMass (v l) ≤ (perpendicularProjector * K).trace.re := by
      rw [ht]
      exact Finset.single_le_sum (fun i _ => perpendicularMass_nonneg (v i)) (Finset.mem_univ l)
    have hiD : Swap.mass (v l) ≤ dissipationSize K := by
      rw [hd]
      exact Finset.single_le_sum (fun i _ => Swap.mass_nonneg (v i)) (Finset.mem_univ l)
    have hmul := mul_le_mul (Real.sqrt_le_sqrt hiT) (Real.sqrt_le_sqrt hiD)
      (Real.sqrt_nonneg (Swap.mass (v l))) (Real.sqrt_nonneg ((perpendicularProjector * K).trace.re))
    have hbase := norm_outer_difference_le (v l)
    nlinarith
  calc
    _ ≤ ∑ l : Fin 3, (2 * Swap.perpendicularMass (v l) +
        2 * Real.sqrt ((perpendicularProjector * K).trace.re) * Real.sqrt (dissipationSize K)) :=
      Finset.sum_le_sum (fun l _ => hi l)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← ht]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

def normalizedNoise (K : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  (((dissipationSize K)⁻¹ : ℝ) : ℂ) • K

def matrixError (C b : ℝ) : ℝ :=
  8 * probabilityConstant C * b +
    24 * Real.sqrt (probabilityConstant C) * Real.sqrt scale * Real.sqrt b

theorem tracePerp_nonneg (K : Matrix (Fin 3) (Fin 3) ℂ) (hK : K.PosSemidef) :
    0 ≤ (perpendicularProjector * K).trace.re := by
  obtain ⟨v, hv⟩ := exists_kossakowski_factor K hK
  rw [← hv, tracePerp_gram]
  exact Finset.sum_nonneg (fun i _ => perpendicularMass_nonneg (v i))

/-- 同一显式误差函数控制所有近最优 K/d，且使用真实欧氏算符范数。 -/
theorem normalized_noise_bound (K : Matrix (Fin 3) (Fin 3) ℂ) (hK : K.PosSemidef)
    (C b : ℝ) (hC : 0 < C) (hb : 0 < b)
    (hdlo : b / 4 ≤ dissipationSize K) (hdhi : dissipationSize K ≤ scale * b)
    (hperp : (perpendicularProjector * K).trace.re ≤ probabilityConstant C * b ^ 2) :
    ‖normalizedNoise K - kernelProjector‖ ≤ matrixError C b := by
  have hd : 0 < dissipationSize K := by linarith
  have ht := tracePerp_nonneg K hK
  have hP := probabilityConstant_pos C hC
  have hs : 0 ≤ scale := by norm_num [scale]
  have hts : Real.sqrt ((perpendicularProjector * K).trace.re) ≤ Real.sqrt (probabilityConstant C) * b := by
    have hh : (Real.sqrt (probabilityConstant C) * b) ^ 2 = probabilityConstant C * b ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hP.le]
    nlinarith [Real.sq_sqrt ht, Real.sqrt_nonneg ((perpendicularProjector * K).trace.re),
      mul_nonneg (Real.sqrt_nonneg (probabilityConstant C)) hb.le]
  have hds : Real.sqrt (dissipationSize K) ≤ Real.sqrt scale * Real.sqrt b := by
    simpa only [Real.sqrt_mul hs] using Real.sqrt_le_sqrt hdhi
  have hprod := mul_le_mul hts hds (Real.sqrt_nonneg (dissipationSize K))
    (mul_nonneg (Real.sqrt_nonneg (probabilityConstant C)) hb.le)
  have hu := matrix_concentration_bound K hK
  have hsc : ((dissipationSize K : ℝ) : ℂ) * (((dissipationSize K)⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ hd.ne', Complex.ofReal_one]
  have heq : ((dissipationSize K : ℝ) : ℂ) • (normalizedNoise K - kernelProjector) =
      K - ((dissipationSize K : ℝ) : ℂ) • kernelProjector := by
    rw [smul_sub, normalizedNoise, smul_smul, hsc, one_smul]
  have hn := congrArg norm heq
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd] at hn
  have hlo := mul_le_mul_of_nonneg_right hdlo (norm_nonneg (normalizedNoise K - kernelProjector))
  apply (mul_le_mul_iff_right₀ hb).mp
  unfold matrixError
  nlinarith

/-- 首圈纯核方向的单位耗散读出。 -/
def inverseScaleLimit : ℝ := (2 / 3) * (1 + 2 * Swap.rootTwo / Real.pi)

theorem inverseScaleLimit_pos : 0 < inverseScaleLimit := by
  unfold inverseScaleLimit
  have := Swap.rootTwo_pos
  have := Real.pi_pos
  positivity

def referenceReadout : Matrix (Fin 3) (Fin 3) ℂ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun K => (Swap.matrixQb 0 * K).trace.re
      map_add' := by intro A B; simp only [mul_add, Matrix.trace_add, Complex.add_re]
      map_smul' := by intro a A; simp only [Matrix.mul_smul, Matrix.trace_smul,
        Complex.smul_re, smul_eq_mul, RingHom.id_apply] }

theorem referenceReadout_apply (K : Matrix (Fin 3) (Fin 3) ℂ) :
    referenceReadout K = (Swap.matrixQb 0 * K).trace.re := rfl

theorem referenceReadout_kernel : referenceReadout kernelProjector = inverseScaleLimit := by
  have hqb : Swap.qb 0 Swap.kernelVector = 1 + 2 * Swap.rootTwo / Real.pi := by
    norm_num [Swap.qb, Swap.energy, Swap.cross, Swap.kernelVector, Swap.frequency_zero,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im, map_ofNat]
    ring_nf
    rw [Swap.rootTwo_sq]
    ring
  rw [referenceReadout_apply, kernelProjector_eq_outer, Matrix.mul_smul,
    Matrix.trace_smul, Swap.trace_matrix_outer, Swap.matrixQb_form, hqb]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, inverseScaleLimit]

theorem referenceReadout_normalized (K : Matrix (Fin 3) (Fin 3) ℂ) :
    referenceReadout (normalizedNoise K) = referenceReadout K / dissipationSize K := by
  change (Swap.matrixQb 0 * ((((dissipationSize K)⁻¹ : ℝ) : ℂ) • K)).trace.re = _
  simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, referenceReadout_apply]
  ring

def reciprocalError (C b : ℝ) : ℝ :=
  4 * (probabilityConstant C + errorConstant C) * b + ‖referenceReadout‖ * matrixError C b

def scaleError (C b : ℝ) : ℝ := scale / inverseScaleLimit * reciprocalError C b

/-- 从实际 b 的首阶读出得到耗散尺度极限；常数只依赖 C。 -/
theorem inverse_scale_bound (K : Matrix (Fin 3) (Fin 3) ℂ) (hK : K.PosSemidef)
    (C b p : ℝ) (hC : 0 < C) (hb : 0 < b) (hp : 0 ≤ p)
    (hprob : p ≤ probabilityConstant C * b ^ 2)
    (hdlo : b / 4 ≤ dissipationSize K) (hdhi : dissipationSize K ≤ scale * b)
    (hperp : (perpendicularProjector * K).trace.re ≤ probabilityConstant C * b ^ 2)
    (hRb : |b - p - (Swap.matrixQb 0 * K).trace.re| ≤ errorConstant C * b ^ 2) :
    |b / dissipationSize K - inverseScaleLimit| ≤ reciprocalError C b := by
  have hd : 0 < dissipationSize K := by linarith
  have hmat := normalized_noise_bound K hK C b hC hb hdlo hdhi hperp
  have hread := referenceReadout.le_opNorm (normalizedNoise K - kernelProjector)
  rw [map_sub, referenceReadout_normalized, referenceReadout_kernel, Real.norm_eq_abs] at hread
  have hread' := mul_le_mul_of_nonneg_left hmat (norm_nonneg referenceReadout)
  have herr : |b - referenceReadout K| ≤ (probabilityConstant C + errorConstant C) * b ^ 2 := by
    have hh := abs_add_le (b - p - referenceReadout K) p
    rw [abs_of_nonneg hp] at hh
    rw [referenceReadout_apply] at hh
    have he : b - p - (Swap.matrixQb 0 * K).trace.re + p =
        b - (Swap.matrixQb 0 * K).trace.re := by ring
    rw [he] at hh
    rw [referenceReadout_apply]
    nlinarith
  have hfirst : |b / dissipationSize K - referenceReadout K / dissipationSize K| ≤
      4 * (probabilityConstant C + errorConstant C) * b := by
    rw [← sub_div, abs_div, abs_of_pos hd, div_le_iff₀ hd]
    have hmul := mul_le_mul_of_nonneg_left hdlo
      (show 0 ≤ 4 * (probabilityConstant C + errorConstant C) * b by
        have := probabilityConstant_pos C hC
        have := errorConstant_pos C
        positivity)
    nlinarith
  have htri := abs_add_le
    (b / dissipationSize K - referenceReadout K / dissipationSize K)
    (referenceReadout K / dissipationSize K - inverseScaleLimit)
  have he : b / dissipationSize K - referenceReadout K / dissipationSize K +
      (referenceReadout K / dissipationSize K - inverseScaleLimit) =
      b / dissipationSize K - inverseScaleLimit := by ring
  rw [he] at htri
  unfold reciprocalError
  linarith

theorem scale_ratio_bound (K : Matrix (Fin 3) (Fin 3) ℂ) (hK : K.PosSemidef)
    (C b p : ℝ) (hC : 0 < C) (hb : 0 < b) (hp : 0 ≤ p)
    (hprob : p ≤ probabilityConstant C * b ^ 2)
    (hdlo : b / 4 ≤ dissipationSize K) (hdhi : dissipationSize K ≤ scale * b)
    (hperp : (perpendicularProjector * K).trace.re ≤ probabilityConstant C * b ^ 2)
    (hRb : |b - p - (Swap.matrixQb 0 * K).trace.re| ≤ errorConstant C * b ^ 2) :
    |dissipationSize K / b - inverseScaleLimit⁻¹| ≤ scaleError C b := by
  have hd : 0 < dissipationSize K := by linarith
  have hk := inverseScaleLimit_pos
  have hbase := inverse_scale_bound K hK C b p hC hb hp hprob hdlo hdhi hperp hRb
  have he : dissipationSize K / b - inverseScaleLimit⁻¹ =
      -(dissipationSize K / b / inverseScaleLimit) *
        (b / dissipationSize K - inverseScaleLimit) := by
    field_simp
    ring
  rw [he, abs_mul, abs_neg, abs_of_nonneg (by positivity)]
  have hscale : dissipationSize K / b / inverseScaleLimit ≤ scale / inverseScaleLimit := by
    apply div_le_div_of_nonneg_right _ hk.le
    exact (div_le_iff₀ hb).mpr hdhi
  exact (mul_le_mul hscale hbase (abs_nonneg _) (by unfold scale; positivity)).trans_eq rfl

theorem matrixError_tendsto_zero (C : ℝ) :
    Filter.Tendsto (matrixError C) (nhds 0) (nhds 0) := by
  have hc : Continuous (matrixError C) := by unfold matrixError; fun_prop
  simpa [matrixError] using hc.tendsto 0

theorem scaleError_tendsto_zero (C : ℝ) :
    Filter.Tendsto (scaleError C) (nhds 0) (nhds 0) := by
  have hc : Continuous (scaleError C) := by
    unfold scaleError reciprocalError matrixError
    fun_prop
  simpa [scaleError, reciprocalError, matrixError] using hc.tendsto 0

#print axioms matrix_localization_of_remainders
#print axioms canonical_near_scale
#print axioms hamiltonian_coordinate_bounds
#print axioms matrix_concentration_bound
#print axioms normalized_noise_bound
#print axioms inverse_scale_bound
#print axioms scale_ratio_bound

end TwoStateQuantumEmbedding.NearSwap

