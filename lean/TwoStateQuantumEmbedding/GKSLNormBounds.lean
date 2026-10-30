import TwoStateQuantumEmbedding.GKSLAlgebra
import TwoStateQuantumEmbedding.DissipativeFlow
import TwoStateQuantumEmbedding.Duhamel
import TwoStateQuantumEmbedding.CanonicalBloch
import TwoStateQuantumEmbedding.CPTP
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Tactic

/-! 真实规范 GKSL 参数的欧氏漂移界与 Bloch 球正性。 -/
noncomputable section
open Matrix Complex
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open scoped RealInnerProductSpace

namespace TwoStateQuantumEmbedding.GKSLBounds
open GKSLAlgebra DissipativeFlow
open CanonicalBloch

abbrev R3 := EuclideanSpace ℝ (Fin 3)
abbrev AugmentedSpace := ℝ × R3

def euclid (r : BlochVec) : R3 := WithLp.toLp 2 r

def dissipationSize (K : Matrix (Fin 3) (Fin 3) ℂ) : ℝ :=
  Matrix.trace (K.map Complex.re)

@[simp] theorem euclid_apply (r : BlochVec) (i : Fin 3) : euclid r i = r i := rfl

@[simp] theorem norm_euclid_sq (r : BlochVec) :
    ‖euclid r‖ ^ 2 = r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, euclid, add_assoc]

theorem blochState_det_re (r : BlochVec) :
    (Matrix.det (blochState r)).re = (1 - ‖euclid r‖ ^ 2) / 4 := by
  simp [Matrix.det_fin_two, blochState, realPauli, pauli, Matrix.smul_apply,
    smul_eq_mul, Complex.mul_re, Complex.mul_im, norm_euclid_sq]
  ring

/-- 对实际 Pauli 编码，PSD 恰好对应欧氏闭单位球。 -/
theorem blochState_posSemidef_iff (r : BlochVec) :
    (blochState r).PosSemidef ↔ ‖euclid r‖ ≤ 1 := by
  constructor
  · intro h
    have hd := (Complex.nonneg_iff.mp h.det_nonneg).1
    rw [blochState_det_re] at hd
    nlinarith [norm_nonneg (euclid r)]
  · intro hr
    let hh := blochState_hermitian r
    have hs : hh.eigenvalues 0 + hh.eigenvalues 1 = 1 := by
      have ht := congrArg Complex.re hh.trace_eq_sum_eigenvalues
      simpa [blochState_trace, Fin.sum_univ_two] using ht.symm
    have hp : 0 ≤ hh.eigenvalues 0 * hh.eigenvalues 1 := by
      have hd := congrArg Complex.re hh.det_eq_prod_eigenvalues
      simp [Fin.prod_univ_two, blochState_det_re, -norm_euclid_sq] at hd
      nlinarith [norm_nonneg (euclid r)]
    apply hh.posSemidef_iff_eigenvalues_nonneg.mpr
    intro i
    fin_cases i <;> dsimp
    · nlinarith [sq_nonneg (hh.eigenvalues 0)]
    · nlinarith [sq_nonneg (hh.eigenvalues 1)]

/-- 单个复跳跃的漂移满足精确的 2 tr K 界。 -/
theorem norm_drift_single_le (l : PauliVec) :
    ‖euclid (drift (singleK l))‖ ≤ 2 * dissipationSize (singleK l) := by
  let a : ℝ := (l 0).re ^ 2 + (l 1).re ^ 2 + (l 2).re ^ 2
  let b : ℝ := (l 0).im ^ 2 + (l 1).im ^ 2 + (l 2).im ^ 2
  let q : ℝ := (l 0).re * (l 0).im + (l 1).re * (l 1).im + (l 2).re * (l 2).im
  have hd : dissipationSize (singleK l) = a + b := by
    simp [dissipationSize, singleK, Matrix.trace, Fin.sum_univ_three,
      Complex.mul_re, a, b]
    ring
  have hc : ‖euclid (drift (singleK l))‖ ^ 2 = 16 * (a * b - q ^ 2) := by
    simp [norm_euclid_sq, drift, singleK, Complex.mul_im, a, b, q]
    ring
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  rw [hd]
  nlinarith [sq_nonneg (a - b), sq_nonneg q, norm_nonneg (euclid (drift (singleK l)))]

theorem drift_kossakowski {n : ℕ} (l : Fin n → PauliVec) :
    drift (kossakowski l) = ∑ μ, drift (singleK (l μ)) := by
  ext i
  fin_cases i <;>
    simp [drift, kossakowski, singleK, Finset.mul_sum, Finset.sum_apply]

theorem dissipationSize_kossakowski {n : ℕ} (l : Fin n → PauliVec) :
    dissipationSize (kossakowski l) = ∑ μ, dissipationSize (singleK (l μ)) := by
  change (∑ i, (∑ μ, l μ i * star (l μ i)).re) =
    ∑ μ, ∑ i, (l μ i * star (l μ i)).re
  simp only [Complex.re_sum]
  exact Finset.sum_comm

/-- 任意真实有限跳跃数的漂移界；逐跳跃界通过三角不等式求和。 -/
theorem norm_drift_kossakowski_le {n : ℕ} (l : Fin n → PauliVec) :
    ‖euclid (drift (kossakowski l))‖ ≤ 2 * dissipationSize (kossakowski l) := by
  rw [drift_kossakowski, dissipationSize_kossakowski, Finset.mul_sum]
  change ‖WithLp.toLp 2 (∑ μ, drift (singleK (l μ)))‖ ≤ _
  rw [WithLp.toLp_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun μ _ => norm_drift_single_le (l μ)))

/-- 任意 PSD 规范矩阵通过已证明的 Gram 分解得到同一界。 -/
theorem norm_drift_le (K : Matrix (Fin 3) (Fin 3) ℂ) (hK : K.PosSemidef) :
    ‖euclid (drift K)‖ ≤ 2 * dissipationSize K := by
  obtain ⟨l, rfl⟩ := exists_kossakowski_factor K hK
  exact norm_drift_kossakowski_le l

theorem real_part_posSemidef (K : Matrix (Fin 3) (Fin 3) ℂ) (hK : K.PosSemidef) :
    (K.map Complex.re).PosSemidef := by
  obtain ⟨l, rfl⟩ := exists_kossakowski_factor K hK
  exact kossakowski_real_posSemidef l

theorem dissipationSize_nonneg (K : Matrix (Fin 3) (Fin 3) ℂ) (hK : K.PosSemidef) :
    0 ≤ dissipationSize K := (real_part_posSemidef K hK).trace_nonneg

/-- D=2(tr S I−S) 的 L2 算符范数不超过 2 tr S。 -/
theorem norm_canonicalD_le (S : Matrix (Fin 3) (Fin 3) ℝ) (hS : S.PosSemidef) :
    ‖canonicalD S‖ ≤ 2 * S.trace := by
  let T := Matrix.toEuclideanCLM (𝕜 := ℝ) (canonicalD S)
  have hT : T.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (canonicalD_posSemidef S hS).isHermitian
  change ‖T‖ ≤ _
  rw [T.norm_eq_iSup_rayleighQuotient hT]
  apply ciSup_le
  intro x
  have hlo := inner_posSemidef_nonneg _ (canonicalD_posSemidef S hS) x
  have hhi := inner_posSemidef_nonneg _ (canonicalD_upper S hS) x
  simp only [map_sub, map_smul, map_one, _root_.sub_apply,
    _root_.smul_apply, one_apply_eq_self,
    inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq] at hhi
  change 0 ≤ ⟪x, T x⟫ at hlo
  change 0 ≤ 2 * S.trace * ‖x‖ ^ 2 - ⟪x, T x⟫ at hhi
  by_cases hx : x = 0
  · simp [hx, ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hS.trace_nonneg]
  · have hxpos : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
    simp only [ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real]
    rw [real_inner_comm x (T x)]
    rw [abs_of_nonneg (div_nonneg hlo (sq_nonneg _))]
    exact (div_le_iff₀ hxpos).mpr (by linarith)

/-- 用实际乘积范数承载仿射 Bloch 生成元；第一坐标为迹。 -/
def augmentedCLM (M : R3 →L[ℝ] R3) (c : R3) : AugmentedSpace →L[ℝ] AugmentedSpace :=
  (0 : AugmentedSpace →L[ℝ] ℝ).prod
    (M.comp (ContinuousLinearMap.snd ℝ ℝ R3) +
      (ContinuousLinearMap.fst ℝ ℝ R3).smulRight c)

@[simp] theorem augmentedCLM_apply (M : R3 →L[ℝ] R3) (c : R3) (x : AugmentedSpace) :
    augmentedCLM M c x = (0, M x.2 + x.1 • c) := rfl

theorem norm_augmentedCLM_le (M : R3 →L[ℝ] R3) (c : R3) :
    ‖augmentedCLM M c‖ ≤ ‖M‖ + ‖c‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg (norm_nonneg _) (norm_nonneg _))
  intro x
  have hfst : ‖x.1‖ ≤ ‖x‖ := le_max_left _ _
  have hsnd : ‖x.2‖ ≤ ‖x‖ := le_max_right _ _
  simp only [augmentedCLM_apply, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
  calc
    ‖M x.2 + x.1 • c‖ ≤ ‖M x.2‖ + ‖x.1 • c‖ := norm_add_le _ _
    _ ≤ ‖M‖ * ‖x.2‖ + ‖x.1‖ * ‖c‖ := by
      rw [norm_smul]
      gcongr
      exact M.le_opNorm _
    _ ≤ ‖M‖ * ‖x‖ + ‖x‖ * ‖c‖ := by gcongr
    _ = (‖M‖ + ‖c‖) * ‖x‖ := by ring

def dissipativeCLM (K : Matrix (Fin 3) (Fin 3) ℂ) : AugmentedSpace →L[ℝ] AugmentedSpace :=
  augmentedCLM (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (canonicalD (K.map Complex.re))))
    (euclid (drift K))

/-- 所需的 4d 来自两个真实 PSD 参数界，而非传播子界假设。 -/
theorem norm_dissipativeCLM_le (K : Matrix (Fin 3) (Fin 3) ℂ) (hK : K.PosSemidef) :
    ‖dissipativeCLM K‖ ≤ 4 * dissipationSize K := by
  have hD := norm_canonicalD_le (K.map Complex.re) (real_part_posSemidef K hK)
  have hc := norm_drift_le K hK
  have h := norm_augmentedCLM_le
    (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (canonicalD (K.map Complex.re)))) (euclid (drift K))
  simp only [norm_neg] at h
  change ‖dissipativeCLM K‖ ≤
    ‖canonicalD (K.map Complex.re)‖ + ‖euclid (drift K)‖ at h
  change ‖canonicalD (K.map Complex.re)‖ ≤ 2 * dissipationSize K at hD
  linarith

/-- 正单位迹截面的像位于同一单位球时，整个实线性映射为压缩。 -/
theorem norm_le_one_of_unit_slice (T : AugmentedSpace →L[ℝ] AugmentedSpace)
    (hT : ∀ r : R3, ‖r‖ ≤ 1 → ‖T (1, r)‖ ≤ 1) : ‖T‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  by_cases hx : x = 0
  · simp [hx]
  have hR : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let r : R3 := ‖x‖⁻¹ • x.2
  let a : ℝ := (‖x‖ + x.1) / 2
  let b : ℝ := (‖x‖ - x.1) / 2
  have hfst : |x.1| ≤ ‖x‖ := le_max_left _ _
  have hsnd : ‖x.2‖ ≤ ‖x‖ := le_max_right _ _
  have ha : 0 ≤ a := by dsimp [a]; linarith [le_abs_self x.1, neg_le_abs x.1]
  have hb : 0 ≤ b := by dsimp [b]; linarith [le_abs_self x.1]
  have hab : a + b = ‖x‖ := by dsimp [a, b]; ring
  have hr : ‖r‖ ≤ 1 := by
    dsimp [r]
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hR]
    have := (div_le_one hR).mpr hsnd
    simpa [div_eq_mul_inv, mul_comm] using this
  have hdecomp : x = a • (1, r) - b • (1, -r) := by
    apply Prod.ext
    · change x.1 = a * 1 - b * 1
      dsimp [a, b]
      ring
    · change x.2 = a • r - b • -r
      rw [smul_neg, sub_neg_eq_add, ← add_smul, hab]
      simp [r, smul_smul, hR.ne']
  calc
    ‖T x‖ = ‖a • T (1, r) - b • T (1, -r)‖ := by rw [hdecomp, map_sub, map_smul, map_smul]
    _ ≤ ‖a • T (1, r)‖ + ‖b • T (1, -r)‖ := norm_sub_le _ _
    _ = a * ‖T (1, r)‖ + b * ‖T (1, -r)‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * 1 + b * 1 := by gcongr; exact hT r hr; exact hT (-r) (by simpa using hr)
    _ = ‖x‖ := by simpa using hab

/-- 077 的四维数组顺序与本文件乘积范数空间之间的线性坐标等价。 -/
def augmentedCoords : AugmentedSpace ≃ₗ[ℝ] AugmentedVector where
  toFun x := ![x.1, x.2 0, x.2 1, x.2 2]
  invFun v := (v 0, euclid ![v 1, v 2, v 3])
  left_inv x := by
    apply Prod.ext
    · rfl
    · ext i
      fin_cases i <;> rfl
  right_inv v := by funext i; fin_cases i <;> rfl
  map_add' x y := by funext i; fin_cases i <;> rfl
  map_smul' c x := by funext i; fin_cases i <;> rfl

@[simp] theorem augmentedCoords_head (x : AugmentedSpace) : augmentedCoords x 0 = x.1 := rfl

@[simp] theorem spatialPart_augmentedCoords (x : AugmentedSpace) :
    spatialPart (augmentedCoords x) = fun i => x.2 i := by
  funext i
  fin_cases i <;> rfl

def augmentedMatrixEquiv : (AugmentedSpace →L[ℝ] AugmentedSpace) ≃ₐ[ℝ] AugmentedMatrix :=
  (Module.End.toContinuousLinearMap AugmentedSpace).symm.trans
    ((augmentedCoords.conjAlgEquiv ℝ).trans LinearMap.toMatrixAlgEquiv')

theorem augmentedMatrixEquiv_mulVec (T : AugmentedSpace →L[ℝ] AugmentedSpace)
    (x : AugmentedSpace) :
    augmentedMatrixEquiv T *ᵥ augmentedCoords x = augmentedCoords (T x) := by
  change Matrix.toLinAlgEquiv' (LinearMap.toMatrixAlgEquiv'
    (augmentedCoords.conjAlgEquiv ℝ T.toLinearMap)) (augmentedCoords x) = _
  rw [Matrix.toLinAlgEquiv'_toMatrixAlgEquiv']
  change augmentedCoords (T (augmentedCoords.symm (augmentedCoords x))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem augmentedMatrixEquiv_exp (T : AugmentedSpace →L[ℝ] AugmentedSpace) :
    augmentedMatrixEquiv (NormedSpace.exp T) = NormedSpace.exp (augmentedMatrixEquiv T) := by
  let : NormedAlgebra ℚ (AugmentedSpace →L[ℝ] AugmentedSpace) := .restrictScalars ℚ ℝ _
  exact NormedSpace.map_exp augmentedMatrixEquiv
    augmentedMatrixEquiv.toLinearMap.continuous_of_finiteDimensional T

/-- 通过代数同构使用 077 的同一个真实生成元 Q。 -/
def canonicalCLM (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ) :
    AugmentedSpace →L[ℝ] AugmentedSpace :=
  augmentedMatrixEquiv.symm (augmentedGenerator h K)

theorem canonicalCLM_apply (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ)
    (x : AugmentedSpace) :
    canonicalCLM h K x =
      (0, euclid (blochMatrix h K *ᵥ (fun i => x.2 i)) + x.1 • euclid (drift K)) := by
  change augmentedCoords.symm (augmentedGenerator h K *ᵥ augmentedCoords x) = _
  apply Prod.ext
  · exact augmentedGenerator_mulVec_head h K _
  · change euclid (spatialPart (augmentedGenerator h K *ᵥ augmentedCoords x)) = _
    rw [augmentedGenerator_mulVec_spatial, spatialPart_augmentedCoords, augmentedCoords_head]
    rfl

def hamiltonianCLM (h : BlochVec) : AugmentedSpace →L[ℝ] AugmentedSpace :=
  augmentedCLM (Matrix.toEuclideanCLM (𝕜 := ℝ) (crossMatrix h)) 0

theorem blochMatrix_eq_cross_sub (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ) :
    blochMatrix h K = crossMatrix h - canonicalD (K.map Complex.re) := by
  ext i j
  simp only [blochMatrix, canonicalD, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul]
  ring

/-- Hamiltonian 与耗散两部分之和就是原始规范生成元。 -/
theorem canonicalCLM_eq_add (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ) :
    canonicalCLM h K = hamiltonianCLM h + dissipativeCLM K := by
  apply ContinuousLinearMap.ext
  intro x
  rw [canonicalCLM_apply, blochMatrix_eq_cross_sub]
  change ((0 : ℝ), euclid ((crossMatrix h - canonicalD (K.map Complex.re)) *ᵥ (fun i => x.2 i)) +
    x.1 • euclid (drift K)) =
    (0, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 3) (crossMatrix h) x.2 + x.1 • (0 : R3)) +
    (0, (-Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 3) (canonicalD (K.map Complex.re))) x.2 +
      x.1 • euclid (drift K))
  simp only [smul_zero, add_zero, Prod.mk_add_mk]
  apply congrArg (fun r : R3 => ((0 : ℝ), r))
  change Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 3)
    (crossMatrix h - canonicalD (K.map Complex.re)) x.2 + _ = _
  simp [sub_eq_add_neg, add_assoc]

/-- 指数同构对应完整输入作用，不另假设表示关系。 -/
theorem augmentedCoords_exp_canonical (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ)
    (t : ℝ) (x : AugmentedSpace) :
    augmentedCoords ((NormedSpace.exp (t • canonicalCLM h K)) x) =
      canonicalEvolution h K t *ᵥ augmentedCoords x := by
  have he := augmentedMatrixEquiv_mulVec (NormedSpace.exp (t • canonicalCLM h K)) x
  rw [augmentedMatrixEquiv_exp, map_smul] at he
  simpa only [canonicalCLM, AlgEquiv.apply_symm_apply, canonicalEvolution] using he.symm

theorem trace_realGeneralizedState (v : AugmentedVector) :
    Matrix.trace (realGeneralizedState v) = (v 0 : ℂ) := by
  simp [realGeneralizedState, generalizedState, Matrix.trace_smul, Matrix.trace_add,
    pauli_trace]
  ring

theorem realGeneralizedState_unit_slice (r : R3) :
    realGeneralizedState (augmentedCoords (1, r)) = blochState (fun i => r i) := by
  rw [realGeneralizedState_affine, spatialPart_augmentedCoords, augmentedCoords_head]
  simp

/-- PSD 且单位迹的真实编码给出增广范数不超过 1。 -/
theorem norm_le_one_of_positive_trace_one (x : AugmentedSpace)
    (hp : (realGeneralizedState (augmentedCoords x)).PosSemidef)
    (ht : Matrix.trace (realGeneralizedState (augmentedCoords x)) = 1) : ‖x‖ ≤ 1 := by
  rw [trace_realGeneralizedState, augmentedCoords_head] at ht
  have hx : x.1 = 1 := by exact_mod_cast ht
  rw [realGeneralizedState_affine, spatialPart_augmentedCoords, augmentedCoords_head, hx] at hp
  simp only [sub_self, Complex.ofReal_zero, zero_smul, zero_add] at hp
  have hn := (blochState_posSemidef_iff _).mp hp
  change ‖x.2‖ ≤ 1 at hn
  rw [Prod.norm_def, hx, norm_one]
  exact max_le le_rfl hn

/-- 真实 GKSL 正性、保迹性和 Bloch 球刻画推出完整增广传播子的收缩性。 -/
theorem norm_exp_canonicalCLM_le (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ)
    (hK : K.PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    ‖NormedSpace.exp (t • canonicalCLM h K)‖ ≤ 1 := by
  obtain ⟨A, hA⟩ := exists_evolution_for_canonical h K hK
  apply norm_le_one_of_unit_slice
  intro r hr
  let x := (NormedSpace.exp (t • canonicalCLM h K)) (1, r)
  have he : realGeneralizedState (augmentedCoords x) =
      gkslSuperoperatorEvolution (hamiltonian h) A t (blochState (fun i => r i)) := by
    dsimp [x]
    rw [augmentedCoords_exp_canonical, hA, realGeneralizedState_unit_slice]
  have hp : (blochState (fun i => r i)).PosSemidef :=
    (blochState_posSemidef_iff _).mpr hr
  apply norm_le_one_of_positive_trace_one x
  · rw [he]
    exact gkslSuperoperatorEvolution_posSemidef _ A t (hamiltonian_hermitian h) ht hp
  · rw [he, gkslSuperoperatorEvolution_trace _ A t (hamiltonian_hermitian h) ht,
      blochState_trace]

@[simp] theorem dissipativeCLM_zero : dissipativeCLM 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  simp [dissipativeCLM, canonicalD, drift, euclid, augmentedCLM_apply]

theorem norm_exp_hamiltonianCLM_le (h : BlochVec) {t : ℝ} (ht : 0 ≤ t) :
    ‖NormedSpace.exp (t • hamiltonianCLM h)‖ ≤ 1 := by
  simpa only [canonicalCLM_eq_add, dissipativeCLM_zero, add_zero] using
    norm_exp_canonicalCLM_le h 0 Matrix.PosSemidef.zero ht

/-- 全 Hamiltonian、全非负时间的一次扰动界，常数为 4d。 -/
theorem norm_canonical_perturbation_le (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ)
    (hK : K.PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    ‖NormedSpace.exp (t • canonicalCLM h K) - NormedSpace.exp (t • hamiltonianCLM h)‖ ≤
      4 * dissipationSize K * t := by
  have hb := norm_exp_add_sub_le_of_bounds (hamiltonianCLM h) (dissipativeCLM K) t ht 1 1
    (fun s hs => norm_exp_hamiltonianCLM_le h hs.1)
    (fun s hs => by rw [← canonicalCLM_eq_add]; exact norm_exp_canonicalCLM_le h K hK hs.1)
  rw [← canonicalCLM_eq_add] at hb
  simp only [one_mul, mul_one] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right (norm_dissipativeCLM_le K hK) ht)

/-- 精确一阶 Duhamel 项的二次余项：与 Hamiltonian 大小及绕圈数无关。 -/
theorem norm_canonical_first_order_remainder_le
    (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ) (hK : K.PosSemidef)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖NormedSpace.exp (t • canonicalCLM h K) - NormedSpace.exp (t • hamiltonianCLM h) -
      expFirstOrder (hamiltonianCLM h) (dissipativeCLM K) t‖ ≤
      8 * dissipationSize K ^ 2 * t ^ 2 := by
  have hb := norm_exp_first_order_remainder_le_of_contractions
    (hamiltonianCLM h) (dissipativeCLM K) t ht
    (fun s hs => norm_exp_hamiltonianCLM_le h hs.1)
    (fun s hs => by rw [← canonicalCLM_eq_add]; exact norm_exp_canonicalCLM_le h K hK hs.1)
  rw [← canonicalCLM_eq_add] at hb
  calc
    _ ≤ ‖dissipativeCLM K‖ ^ 2 * t ^ 2 / 2 := hb
    _ ≤ (4 * dissipationSize K) ^ 2 * t ^ 2 / 2 := by
      gcongr
      exact norm_dissipativeCLM_le K hK
    _ = 8 * dissipationSize K ^ 2 * t ^ 2 := by ring

/-- s=±1 分别读取计算基的两个对角元。 -/
def diagonalReadout (s : ℝ) : AugmentedSpace →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x : AugmentedSpace => (x.1 + s * x.2 2) / 2
      map_add' := by intro x y; simp; ring
      map_smul' := by intro c x; simp; ring }

@[simp] theorem diagonalReadout_apply (s : ℝ) (x : AugmentedSpace) :
    diagonalReadout s x = (x.1 + s * x.2 2) / 2 := rfl

theorem norm_diagonalReadout_le (s : ℝ) (hs : |s| ≤ 1) : ‖diagonalReadout s‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  have hfst : |x.1| ≤ ‖x‖ := le_max_left _ _
  have hc : |x.2 2| ≤ ‖x‖ := (PiLp.norm_apply_le x.2 2).trans (le_max_right _ _)
  have hm : |s * x.2 2| ≤ ‖x‖ := by
    rw [abs_mul]
    exact (mul_le_mul hs hc (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  change |(x.1 + s * x.2 2) / 2| ≤ 1 * ‖x‖
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), one_mul]
  linarith [abs_add_le x.1 (s * x.2 2)]

def basisInitial (s : ℝ) : AugmentedSpace := (1, euclid ![0, 0, s])

theorem norm_basisInitial_le (s : ℝ) (hs : |s| ≤ 1) : ‖basisInitial s‖ ≤ 1 := by
  have hn : ‖euclid ![0, 0, s]‖ ≤ 1 := by
    have hq : ‖euclid ![0, 0, s]‖ ^ 2 = s ^ 2 := by
      rw [norm_euclid_sq]
      simp
    have hss : s ^ 2 ≤ 1 := by
      simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg s) zero_le_one).mpr hs
    nlinarith [norm_nonneg (euclid ![0, 0, s])]
  change max ‖(1 : ℝ)‖ ‖euclid ![0, 0, s]‖ ≤ 1
  simpa using max_le (by norm_num : ‖(1 : ℝ)‖ ≤ 1) hn

theorem abs_diagonalReadout_operator_le (s : ℝ) (hs : |s| ≤ 1)
    (T : AugmentedSpace →L[ℝ] AugmentedSpace) :
    |diagonalReadout s (T (basisInitial s))| ≤ ‖T‖ := by
  have hread := (diagonalReadout s).le_opNorm (T (basisInitial s))
  have hnorm := norm_diagonalReadout_le s hs
  have hin := norm_basisInitial_le s hs
  calc
    |diagonalReadout s (T (basisInitial s))| ≤ ‖diagonalReadout s‖ * ‖T (basisInitial s)‖ := hread
    _ ≤ 1 * (‖T‖ * ‖basisInitial s‖) :=
      mul_le_mul hnorm (T.le_opNorm _) (norm_nonneg _) zero_le_one
    _ ≤ ‖T‖ := by simpa using mul_le_mul_of_nonneg_left hin (norm_nonneg T)

theorem diagonalReadout_evolution_formula (h : BlochVec)
    (K : Matrix (Fin 3) (Fin 3) ℂ) (t s : ℝ) :
    diagonalReadout s ((NormedSpace.exp (t • canonicalCLM h K)) (basisInitial s)) =
      (1 + s * canonicalEvolution h K t 3 0 + s * s * canonicalEvolution h K t 3 3) / 2 := by
  have he := augmentedCoords_exp_canonical h K t (basisInitial s)
  have h0 := congrFun he 0
  have h3 := congrFun he 3
  change ((NormedSpace.exp (t • canonicalCLM h K)) (basisInitial s)).1 = _ at h0
  change ((NormedSpace.exp (t • canonicalCLM h K)) (basisInitial s)).2 2 = _ at h3
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, augmentedCoords,
    basisInitial, canonicalEvolution_head, Matrix.one_apply, euclid] at h0 h3
  change ((NormedSpace.exp (t • canonicalCLM h K)) (basisInitial s)).1 = 1 at h0
  change ((NormedSpace.exp (t • canonicalCLM h K)) (basisInitial s)).2 2 =
    canonicalEvolution h K t 3 0 + canonicalEvolution h K t 3 3 * s at h3
  rw [diagonalReadout_apply, h0, h3]
  ring

theorem canonicalOutput_fst_eq_readout (h : BlochVec)
    (K : Matrix (Fin 3) (Fin 3) ℂ) (t : ℝ) :
    (canonicalOutput h K t).1 =
      diagonalReadout 1 ((NormedSpace.exp (t • canonicalCLM h K)) (basisInitial 1)) := by
  rw [diagonalReadout_evolution_formula]
  simp only [canonicalOutput, one_mul]
  ring

theorem canonicalOutput_snd_eq_readout (h : BlochVec)
    (K : Matrix (Fin 3) (Fin 3) ℂ) (t : ℝ) :
    (canonicalOutput h K t).2 =
      diagonalReadout (-1) ((NormedSpace.exp (t • canonicalCLM h K)) (basisInitial (-1))) := by
  rw [diagonalReadout_evolution_formula]
  simp only [canonicalOutput]
  ring

def unitaryReturn (h : BlochVec) (t s : ℝ) : ℝ :=
  diagonalReadout s ((NormedSpace.exp (t • hamiltonianCLM h)) (basisInitial s))

def firstOrderReturn (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ) (t s : ℝ) : ℝ :=
  diagonalReadout s ((expFirstOrder (hamiltonianCLM h) (dissipativeCLM K) t) (basisInitial s))

/-- 实际两态读出的统一一次扰动估计。 -/
theorem abs_readout_perturbation_le (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ)
    (hK : K.PosSemidef) {t : ℝ} (ht : 0 ≤ t) (s : ℝ) (hs : |s| ≤ 1) :
    |diagonalReadout s ((NormedSpace.exp (t • canonicalCLM h K)) (basisInitial s)) -
      unitaryReturn h t s| ≤ 4 * dissipationSize K * t := by
  have hb := abs_diagonalReadout_operator_le s hs
    (NormedSpace.exp (t • canonicalCLM h K) - NormedSpace.exp (t • hamiltonianCLM h))
  simp only [_root_.sub_apply, map_sub] at hb
  exact hb.trans (norm_canonical_perturbation_le h K hK ht)

/-- 实际两态读出的一阶展开，二次余项常数为 8。 -/
theorem abs_readout_first_order_remainder_le (h : BlochVec)
    (K : Matrix (Fin 3) (Fin 3) ℂ) (hK : K.PosSemidef) {t : ℝ} (ht : 0 ≤ t)
    (s : ℝ) (hs : |s| ≤ 1) :
    |diagonalReadout s ((NormedSpace.exp (t • canonicalCLM h K)) (basisInitial s)) -
      unitaryReturn h t s - firstOrderReturn h K t s| ≤
      8 * dissipationSize K ^ 2 * t ^ 2 := by
  have hb := abs_diagonalReadout_operator_le s hs
    (NormedSpace.exp (t • canonicalCLM h K) - NormedSpace.exp (t • hamiltonianCLM h) -
      expFirstOrder (hamiltonianCLM h) (dissipativeCLM K) t)
  simp only [_root_.sub_apply, map_sub] at hb
  exact hb.trans (norm_canonical_first_order_remainder_le h K hK ht)

theorem canonicalOutput_perturbation_le (h : BlochVec)
    (K : Matrix (Fin 3) (Fin 3) ℂ) (hK : K.PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    |(canonicalOutput h K t).1 - unitaryReturn h t 1| ≤ 4 * dissipationSize K * t ∧
    |(canonicalOutput h K t).2 - unitaryReturn h t (-1)| ≤ 4 * dissipationSize K * t := by
  rw [canonicalOutput_fst_eq_readout, canonicalOutput_snd_eq_readout]
  exact ⟨abs_readout_perturbation_le h K hK ht 1 (by norm_num),
    abs_readout_perturbation_le h K hK ht (-1) (by norm_num)⟩

theorem canonicalOutput_first_order_remainder_le (h : BlochVec)
    (K : Matrix (Fin 3) (Fin 3) ℂ) (hK : K.PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    |(canonicalOutput h K t).1 - unitaryReturn h t 1 - firstOrderReturn h K t 1| ≤
      8 * dissipationSize K ^ 2 * t ^ 2 ∧
    |(canonicalOutput h K t).2 - unitaryReturn h t (-1) - firstOrderReturn h K t (-1)| ≤
      8 * dissipationSize K ^ 2 * t ^ 2 := by
  rw [canonicalOutput_fst_eq_readout, canonicalOutput_snd_eq_readout]
  exact ⟨abs_readout_first_order_remainder_le h K hK ht 1 (by norm_num),
    abs_readout_first_order_remainder_le h K hK ht (-1) (by norm_num)⟩

/-- 无漂移 Hamiltonian 演化固定纯迹方向。 -/
theorem canonicalEvolution_zero_drift_column (h : BlochVec) (t : ℝ) :
    canonicalEvolution h 0 t 3 0 = 0 := by
  have hz : ∀ j, (t • augmentedGenerator h 0).transpose 0 j = 0 := by
    intro j
    fin_cases j <;> simp [augmentedGenerator, drift]
  have he := matrix_exp_zero_row _ hz 3
  rw [Matrix.exp_transpose] at he
  simpa [canonicalEvolution, Matrix.one_apply] using he

def unitaryProbability (h : BlochVec) (t : ℝ) : ℝ :=
  (1 + canonicalEvolution h 0 t 3 3) / 2

theorem unitaryReturn_eq_probability (h : BlochVec) (t s : ℝ) (hs : s * s = 1) :
    unitaryReturn h t s = unitaryProbability h t := by
  have he := diagonalReadout_evolution_formula h 0 t s
  simpa only [canonicalCLM_eq_add, dissipativeCLM_zero, add_zero,
    canonicalEvolution_zero_drift_column, mul_zero, hs, one_mul, unitaryReturn,
    unitaryProbability] using he

theorem canonicalOutput_perturbation_common_le (h : BlochVec)
    (K : Matrix (Fin 3) (Fin 3) ℂ) (hK : K.PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    |(canonicalOutput h K t).1 - unitaryProbability h t| ≤ 4 * dissipationSize K * t ∧
    |(canonicalOutput h K t).2 - unitaryProbability h t| ≤ 4 * dissipationSize K * t := by
  simpa only [unitaryReturn_eq_probability h t 1 (by norm_num),
    unitaryReturn_eq_probability h t (-1) (by norm_num)] using
    canonicalOutput_perturbation_le h K hK ht

theorem canonicalOutput_first_order_common_le (h : BlochVec)
    (K : Matrix (Fin 3) (Fin 3) ℂ) (hK : K.PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    |(canonicalOutput h K t).1 - unitaryProbability h t - firstOrderReturn h K t 1| ≤
      8 * dissipationSize K ^ 2 * t ^ 2 ∧
    |(canonicalOutput h K t).2 - unitaryProbability h t - firstOrderReturn h K t (-1)| ≤
      8 * dissipationSize K ^ 2 * t ^ 2 := by
  simpa only [unitaryReturn_eq_probability h t 1 (by norm_num),
    unitaryReturn_eq_probability h t (-1) (by norm_num)] using
    canonicalOutput_first_order_remainder_le h K hK ht

/-- 当输入迹坐标为零，概率读出的范数界多一个二分之一。 -/
theorem abs_diagonalReadout_trace_zero_le (s : ℝ) (hs : |s| ≤ 1)
    (x : AugmentedSpace) (hx : x.1 = 0) : |diagonalReadout s x| ≤ ‖x‖ / 2 := by
  rw [diagonalReadout_apply, hx, zero_add, abs_div, abs_mul]
  have hc : |x.2 2| ≤ ‖x‖ := (PiLp.norm_apply_le x.2 2).trans (le_max_right _ _)
  have hm := mul_le_mul hs hc (abs_nonneg _) zero_le_one
  norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), one_mul] at *
  linarith

@[simp] theorem dissipativeCLM_head (K : Matrix (Fin 3) (Fin 3) ℂ) (x : AugmentedSpace) :
    (dissipativeCLM K x).1 = 0 := rfl

theorem norm_dissipativeCLM_trace_zero_le (K : Matrix (Fin 3) (Fin 3) ℂ)
    (hK : K.PosSemidef) (x : AugmentedSpace) (hx : x.1 = 0) :
    ‖dissipativeCLM K x‖ ≤ 2 * dissipationSize K * ‖x‖ := by
  have hd := norm_canonicalD_le (K.map Complex.re) (real_part_posSemidef K hK)
  change ‖(0, (-Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 3)
    (canonicalD (K.map Complex.re))) x.2 + x.1 • euclid (drift K))‖ ≤ _
  rw [hx, zero_smul, add_zero, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _),
    _root_.neg_apply, norm_neg]
  exact ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 3)
    (canonicalD (K.map Complex.re))).le_opNorm x.2).trans
    (mul_le_mul hd (le_max_right _ _) (norm_nonneg _) (by
      exact mul_nonneg (by norm_num) (dissipationSize_nonneg K hK)))

theorem real_part_real_smul (s : ℝ) (K : Matrix (Fin 3) (Fin 3) ℂ) :
    (s • K).map Complex.re = s • K.map Complex.re := by
  ext i j
  simp [Matrix.map_apply, Matrix.smul_apply, Complex.real_smul]

theorem drift_real_smul (s : ℝ) (K : Matrix (Fin 3) (Fin 3) ℂ) :
    drift (s • K) = s • drift K := by
  ext i
  fin_cases i <;> simp [drift, smul_eq_mul, Complex.mul_im, Complex.real_smul] <;> ring

theorem canonicalD_real_smul (s : ℝ) (S : Matrix (Fin 3) (Fin 3) ℝ) :
    canonicalD (s • S) = s • canonicalD S := by
  simp only [canonicalD, Matrix.trace_smul, smul_smul, smul_sub]
  module

theorem dissipativeCLM_real_smul (s : ℝ) (K : Matrix (Fin 3) (Fin 3) ℂ) :
    dissipativeCLM (s • K) = s • dissipativeCLM K := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [dissipativeCLM, real_part_real_smul, canonicalD_real_smul,
    drift_real_smul, map_smul, augmentedCLM_apply, _root_.smul_apply]
  apply Prod.ext
  · simp
  · change (-(s • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 3)
      (canonicalD (K.map Complex.re)))) x.2 + x.1 • (s • euclid (drift K)) =
        s • ((-Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 3)
          (canonicalD (K.map Complex.re))) x.2 + x.1 • euclid (drift K))
    simp only [_root_.neg_apply, _root_.smul_apply, smul_add, smul_neg]
    rw [smul_comm x.1 s]

theorem dissipationSize_real_smul (s : ℝ) (K : Matrix (Fin 3) (Fin 3) ℂ) :
    dissipationSize (s • K) = s * dissipationSize K := by
  simp only [dissipationSize, real_part_real_smul, Matrix.trace_smul, smul_eq_mul]

/-- 实际首阶项就是两个 Hamiltonian 传播子夹持耗散项的标量积分。 -/
theorem firstOrderReturn_eq_integral (h : BlochVec)
    (K : Matrix (Fin 3) (Fin 3) ℂ) (t s : ℝ) :
    firstOrderReturn h K t s =
      ∫ r in (0 : ℝ)..t, diagonalReadout s
        ((NormedSpace.exp ((t - r) • hamiltonianCLM h))
          (dissipativeCLM K ((NormedSpace.exp (r • hamiltonianCLM h)) (basisInitial s)))) := by
  let L : (AugmentedSpace →L[ℝ] AugmentedSpace) →L[ℝ] ℝ :=
    (diagonalReadout s).comp (ContinuousLinearMap.apply ℝ AugmentedSpace (basisInitial s))
  have hi := L.intervalIntegral_comp_comm (μ := MeasureTheory.volume)
    ((continuous_duhamel_kernel (hamiltonianCLM h) (hamiltonianCLM h)
      (dissipativeCLM K) t).intervalIntegrable 0 t)
  simpa only [L, firstOrderReturn, expFirstOrder, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, mul_apply_eq_comp] using hi.symm

theorem firstOrderReturn_real_smul (h : BlochVec)
    (K : Matrix (Fin 3) (Fin 3) ℂ) (t s a : ℝ) :
    firstOrderReturn h (a • K) t s = a * firstOrderReturn h K t s := by
  rw [firstOrderReturn_eq_integral, firstOrderReturn_eq_integral]
  simp only [dissipativeCLM_real_smul, _root_.smul_apply, map_smul, smul_eq_mul]
  rw [intervalIntegral.integral_const_mul]

end TwoStateQuantumEmbedding.GKSLBounds
#print axioms TwoStateQuantumEmbedding.GKSLBounds.blochState_posSemidef_iff
#print axioms TwoStateQuantumEmbedding.GKSLBounds.norm_drift_le
#print axioms TwoStateQuantumEmbedding.GKSLBounds.norm_canonicalD_le
#print axioms TwoStateQuantumEmbedding.GKSLBounds.norm_dissipativeCLM_le
#print axioms TwoStateQuantumEmbedding.GKSLBounds.norm_exp_canonicalCLM_le
#print axioms TwoStateQuantumEmbedding.GKSLBounds.norm_canonical_perturbation_le
#print axioms TwoStateQuantumEmbedding.GKSLBounds.norm_canonical_first_order_remainder_le
#print axioms TwoStateQuantumEmbedding.GKSLBounds.canonicalOutput_perturbation_common_le
#print axioms TwoStateQuantumEmbedding.GKSLBounds.canonicalOutput_first_order_common_le
#print axioms TwoStateQuantumEmbedding.GKSLBounds.firstOrderReturn_eq_integral
#print axioms TwoStateQuantumEmbedding.GKSLBounds.firstOrderReturn_real_smul
