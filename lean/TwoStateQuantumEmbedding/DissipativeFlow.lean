import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! 耗散矩阵指数流的实际欧氏范数估计。 -/
noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.L2Operator
open NormedSpace

namespace TwoStateQuantumEmbedding.DissipativeFlow
set_option backward.isDefEq.respectTransparency false

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- 指数轨迹的导数直接由 Banach 代数指数导数得到。 -/
theorem hasDerivAt_flow (A : E →L[ℝ] E) (v : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => exp (s • A) v) (A (exp (t • A) v)) t := by
  simpa using (hasDerivAt_exp_smul_const' A t).clm_apply (hasDerivAt_const t v)

/-- 二次型上界推出指数流增长界；允许任意实数增长率。 -/
theorem norm_exp_apply_le (A : E →L[ℝ] E) (c : ℝ)
    (hA : ∀ x : E, ⟪x, A x⟫ ≤ c * ‖x‖ ^ 2)
    (v : E) {t : ℝ} (ht : 0 ≤ t) :
    ‖exp (t • A) v‖ ≤ Real.exp (c * t) * ‖v‖ := by
  let f : ℝ → ℝ := fun s => Real.exp (-2 * c * s) * ‖exp (s • A) v‖ ^ 2
  let f' : ℝ → ℝ := fun s =>
    Real.exp (-2 * c * s) * (-2 * c) * ‖exp (s • A) v‖ ^ 2 +
      Real.exp (-2 * c * s) * (2 * ⟪exp (s • A) v, A (exp (s • A) v)⟫)
  have hd (s : ℝ) : HasDerivAt f (f' s) s := by
    simpa only [f, f', id_eq, mul_one] using (((hasDerivAt_id s).const_mul (-2 * c)).exp).fun_mul
      (hasDerivAt_flow A v s).norm_sq
  have hnon (s : ℝ) : f' s ≤ 0 := by
    have h := mul_le_mul_of_nonneg_left (hA (exp (s • A) v))
      (Real.exp_pos (-2 * c * s)).le
    dsimp [f']
    nlinarith
  have hbound := (antitone_of_hasDerivAt_nonpos hd hnon) ht
  have h0 : f 0 = ‖v‖ ^ 2 := by simp [f]
  rw [h0] at hbound
  have hmul := mul_le_mul_of_nonneg_left hbound (Real.exp_pos (2 * c * t)).le
  have hcancel : Real.exp (2 * c * t) * Real.exp (-2 * c * t) = 1 := by
    rw [← Real.exp_add]
    rw [show 2 * c * t + -2 * c * t = 0 by ring, Real.exp_zero]
  have heq : Real.exp (2 * c * t) = Real.exp (c * t) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  dsimp [f] at hmul
  rw [← mul_assoc, hcancel, one_mul, heq] at hmul
  have hpos : 0 ≤ Real.exp (c * t) * ‖v‖ := mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  nlinarith [norm_nonneg (exp (t • A) v)]

/-- 二次型下界经精确逆流转为最小伸长率下界。 -/
theorem exp_mul_norm_le_norm_exp_apply (A : E →L[ℝ] E) (c : ℝ)
    (hA : ∀ x : E, -c * ‖x‖ ^ 2 ≤ ⟪x, A x⟫)
    (v : E) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-c * t) * ‖v‖ ≤ ‖exp (t • A) v‖ := by
  let : NormedAlgebra ℚ (E →L[ℝ] E) := .restrictScalars ℚ ℝ _
  have hneg (x : E) : ⟪x, (-A) x⟫ ≤ c * ‖x‖ ^ 2 := by
    simp only [neg_apply, inner_neg_right]
    nlinarith [hA x]
  have hi : exp (t • (-A)) (exp (t • A) v) = v := by
    rw [← mul_apply_eq_comp, smul_neg,
      ← exp_add_of_commute (Commute.refl (t • A)).neg_left]
    simp
  have h := norm_exp_apply_le (-A) c hneg (exp (t • A) v) ht
  rw [hi] at h
  have hm := mul_le_mul_of_nonneg_left h (Real.exp_pos (-c * t)).le
  have hc : Real.exp (-c * t) * Real.exp (c * t) = 1 := by
    rw [← Real.exp_add]
    rw [show -c * t + c * t = 0 by ring, Real.exp_zero]
  rwa [← mul_assoc, hc, one_mul] at hm

/-- 算符范数也由逐向量估计得到。 -/
theorem norm_exp_le (A : E →L[ℝ] E) (c : ℝ)
    (hA : ∀ x : E, ⟪x, A x⟫ ≤ c * ‖x‖ ^ 2)
    {t : ℝ} (ht : 0 ≤ t) : ‖exp (t • A)‖ ≤ Real.exp (c * t) := by
  exact ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
    (fun v => norm_exp_apply_le A c hA v ht)

end Hilbert

section Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- 实反对称矩阵的二次型为零。 -/
theorem inner_skew_eq_zero (Ω : Matrix n n ℝ) (hΩ : Ω.transpose = -Ω)
    (x : EuclideanSpace ℝ n) : ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := n) Ω x⟫ = 0 := by
  rw [Matrix.inner_toEuclideanCLM]
  have h := Matrix.dotProduct_transpose_mulVec Ω (fun i => x i) (fun i => x i)
  rw [hΩ, Matrix.neg_mulVec, dotProduct_neg] at h
  linarith

/-- PSD 与欧氏二次型非负直接相接。 -/
theorem inner_posSemidef_nonneg (D : Matrix n n ℝ) (hD : D.PosSemidef)
    (x : EuclideanSpace ℝ n) : 0 ≤ ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := n) D x⟫ := by
  rw [Matrix.inner_toEuclideanCLM]
  simpa using hD.dotProduct_mulVec_nonneg (fun i => x i)

/-- 矩阵指数在标准正交基下就是对应连续线性映射的指数。 -/
theorem toEuclideanCLM_exp (M : Matrix n n ℝ) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (n := n) (exp M) = exp (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := n) M) := by
  let : NormedAlgebra ℚ (Matrix n n ℝ) := .restrictScalars ℚ ℝ _
  exact NormedSpace.map_exp (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := n))
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := n)).toAlgEquiv.toLinearMap.continuous_of_finiteDimensional M

/-- 全部有限维实耗散矩阵都产生欧氏压缩流。 -/
theorem matrix_contraction (Ω D : Matrix n n ℝ) (hΩ : Ω.transpose = -Ω)
    (hD : D.PosSemidef) (v : EuclideanSpace ℝ n) {t : ℝ} (ht : 0 ≤ t) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := n) (exp (t • (Ω - D))) v‖ ≤ ‖v‖ := by
  rw [toEuclideanCLM_exp, map_smul]
  have hb (x : EuclideanSpace ℝ n) :
      ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := n) (Ω - D) x⟫ ≤ 0 * ‖x‖ ^ 2 := by
    simp only [map_sub, sub_apply, inner_sub_right, inner_skew_eq_zero Ω hΩ]
    have := inner_posSemidef_nonneg D hD x
    linarith
  simpa using norm_exp_apply_le (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := n) (Ω - D)) 0 hb v ht

/-- 上界 λI−D 的 PSD 性给出精确指数最小伸长率。 -/
theorem matrix_lower_bound (Ω D : Matrix n n ℝ) (hΩ : Ω.transpose = -Ω)
    (c : ℝ) (hDupper : (c • (1 : Matrix n n ℝ) - D).PosSemidef)
    (v : EuclideanSpace ℝ n) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-c * t) * ‖v‖ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := n) (exp (t • (Ω - D))) v‖ := by
  rw [toEuclideanCLM_exp, map_smul]
  apply exp_mul_norm_le_norm_exp_apply _ c _ v ht
  intro x
  have hu := inner_posSemidef_nonneg _ hDupper x
  simp only [map_sub, map_smul, map_one, sub_apply, smul_apply, one_apply_eq_self,
    inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq] at hu
  simp only [map_sub, sub_apply, inner_sub_right, inner_skew_eq_zero Ω hΩ]
  linarith

/-- 逆矩阵指数的范数使用 L2Operator 实例，绝非 Frobenius 范数。 -/
theorem matrix_inverse_norm (Ω D : Matrix n n ℝ) (hΩ : Ω.transpose = -Ω)
    (c : ℝ) (hDupper : (c • (1 : Matrix n n ℝ) - D).PosSemidef)
    {t : ℝ} (ht : 0 ≤ t) : ‖exp ((-t) • (Ω - D))‖ ≤ Real.exp (c * t) := by
  change ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := n) (exp ((-t) • (Ω - D)))‖ ≤ _
  rw [toEuclideanCLM_exp, map_smul]
  rw [show (-t) • (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := n) (Ω - D)) =
      t • (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := n) (Ω - D))) by
        exact (neg_smul t (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := n) (Ω - D))).trans
          (smul_neg t (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := n) (Ω - D))).symm]
  apply norm_exp_le _ c _ ht
  intro x
  have hu := inner_posSemidef_nonneg _ hDupper x
  simp only [map_sub, map_smul, map_one, sub_apply, smul_apply, one_apply_eq_self,
    inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq] at hu
  simp only [neg_apply, inner_neg_right, map_sub, sub_apply, inner_sub_right,
    inner_skew_eq_zero Ω hΩ]
  linarith

/-- PSD 矩阵的每个特征值不超过迹，因此迹补矩阵仍为 PSD。 -/
theorem trace_complement_posSemidef (S : Matrix n n ℝ) (hS : S.PosSemidef) :
    (S.trace • (1 : Matrix n n ℝ) - S).PosSemidef := by
  let U := hS.isHermitian.eigenvectorUnitary
  let F := Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) U
  have heig (i : n) : hS.isHermitian.eigenvalues i ≤ S.trace := by
    rw [hS.isHermitian.trace_eq_sum_eigenvalues]
    simpa using Finset.single_le_sum (fun j _ => hS.eigenvalues_nonneg j) (Finset.mem_univ i)
  have hd : (Matrix.diagonal (fun i => S.trace - hS.isHermitian.eigenvalues i)).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    exact sub_nonneg.mpr (heig i)
  have hs : F (Matrix.diagonal hS.isHermitian.eigenvalues) = S := by
    simpa [F, U, Function.comp_def] using hS.isHermitian.spectral_theorem.symm
  have hid : Matrix.diagonal (fun i => S.trace - hS.isHermitian.eigenvalues i) =
      S.trace • (1 : Matrix n n ℝ) - Matrix.diagonal hS.isHermitian.eigenvalues := by
    rw [← Matrix.diagonal_sub]
    congr 1
    ext i j
    simp [Matrix.diagonal_apply, Matrix.one_apply]
  have hf : F (Matrix.diagonal (fun i => S.trace - hS.isHermitian.eigenvalues i)) =
      S.trace • (1 : Matrix n n ℝ) - S := by
    rw [hid, map_sub, hs]
    simp
  rw [← hf]
  simpa [F, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
    hd.mul_mul_conjTranspose_same (U : Matrix n n ℝ)

/-- 规范 Bloch 耗散矩阵。 -/
def canonicalD (S : Matrix n n ℝ) : Matrix n n ℝ :=
  (2 : ℝ) • (S.trace • (1 : Matrix n n ℝ) - S)

theorem canonicalD_posSemidef (S : Matrix n n ℝ) (hS : S.PosSemidef) :
    (canonicalD S).PosSemidef :=
  (trace_complement_posSemidef S hS).smul (by norm_num : (0 : ℝ) ≤ 2)

theorem canonicalD_upper (S : Matrix n n ℝ) (hS : S.PosSemidef) :
    ((2 * S.trace) • (1 : Matrix n n ℝ) - canonicalD S).PosSemidef := by
  have heq : (2 * S.trace) • (1 : Matrix n n ℝ) - canonicalD S = (2 : ℝ) • S := by
    ext i j
    simp only [canonicalD, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [heq]
  exact hS.smul (by norm_num : (0 : ℝ) ≤ 2)

end Matrix

/-- 三维实际 Bloch 矩阵：向量使用欧氏二范数，矩阵使用 L2 算符范数。 -/
theorem canonical_bloch_flow_bounds
    (Ω S : Matrix (Fin 3) (Fin 3) ℝ) (hΩ : Ω.transpose = -Ω) (hS : S.PosSemidef)
    (v : EuclideanSpace ℝ (Fin 3)) {t : ℝ} (ht : 0 ≤ t) :
    ‖WithLp.toLp 2 ((exp (t • (Ω - canonicalD S))) *ᵥ (fun i => v i))‖ ≤ ‖v‖ ∧
    Real.exp (-(2 * S.trace) * t) * ‖v‖ ≤
      ‖WithLp.toLp 2 ((exp (t • (Ω - canonicalD S))) *ᵥ (fun i => v i))‖ ∧
    ‖exp ((-t) • (Ω - canonicalD S))‖ ≤ Real.exp ((2 * S.trace) * t) := by
  exact ⟨matrix_contraction Ω (canonicalD S) hΩ (canonicalD_posSemidef S hS) v ht,
    matrix_lower_bound Ω (canonicalD S) hΩ (2 * S.trace) (canonicalD_upper S hS) v ht,
    matrix_inverse_norm Ω (canonicalD S) hΩ (2 * S.trace) (canonicalD_upper S hS) ht⟩

#print axioms norm_exp_apply_le
#print axioms exp_mul_norm_le_norm_exp_apply
#print axioms matrix_contraction
#print axioms matrix_lower_bound
#print axioms matrix_inverse_norm
#print axioms trace_complement_posSemidef
#print axioms canonical_bloch_flow_bounds

end TwoStateQuantumEmbedding.DissipativeFlow

