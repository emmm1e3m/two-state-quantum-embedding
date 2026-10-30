import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Tactic

/-! 三维矩阵指数行列式与欧氏二维体积界。 -/

noncomputable section
open Matrix NormedSpace
open scoped Matrix Matrix.Norms.L2Operator

namespace TwoStateQuantumEmbedding

abbrev RealMatrix3 := Matrix (Fin 3) (Fin 3) ℝ

/-- 三维线性矩阵微分方程的行列式导数，直接由六项行列式展开证明。 -/
theorem hasDerivAt_det_three_of_left_mul
    (F : ℝ → RealMatrix3) (M : RealMatrix3) (t : ℝ)
    (hF : HasDerivAt F (M * F t) t) :
    HasDerivAt (fun s => (F s).det) (M.trace * (F t).det) t := by
  have hij (i j : Fin 3) : HasDerivAt (fun s => F s i j) ((M * F t) i j) t :=
    hasDerivAt_pi.mp (hasDerivAt_pi.mp hF i) j
  have h := (((((hij 0 0).mul (hij 1 1)).mul (hij 2 2)).sub
      (((hij 0 0).mul (hij 1 2)).mul (hij 2 1))).sub
      (((hij 0 1).mul (hij 1 0)).mul (hij 2 2))).add
      (((hij 0 1).mul (hij 1 2)).mul (hij 2 0))
  have h := (h.add (((hij 0 2).mul (hij 1 0)).mul (hij 2 1))).sub
      (((hij 0 2).mul (hij 1 1)).mul (hij 2 0))
  convert h using 1
  · ext s
    exact det_fin_three (F s)
  · simp only [Matrix.mul_apply, Matrix.trace, Matrix.diag, Fin.sum_univ_three,
      Matrix.det_fin_three, Pi.mul_apply]
    ring

/-- 对实际的有限矩阵指数，行列式满足系数为 trace M 的标量方程。 -/
theorem hasDerivAt_det_exp_three (M : RealMatrix3) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (exp (s • M)).det)
      (M.trace * (exp (t • M)).det) t :=
  hasDerivAt_det_three_of_left_mul _ M t (hasDerivAt_exp_smul_const' M t)

/-- 三维实矩阵的 Liouville 行列式恒等式，没有谱可对角化前提。 -/
theorem det_exp_three_smul (M : RealMatrix3) (t : ℝ) :
    (exp (t • M)).det = Real.exp (t * M.trace) := by
  let f : ℝ → ℝ := fun s => (exp (s • M)).det * Real.exp (-(s * M.trace))
  have hf (s : ℝ) : HasDerivAt f 0 s := by
    have he : HasDerivAt (fun s : ℝ => Real.exp (-(s * M.trace)))
        (Real.exp (-(s * M.trace)) * (-M.trace)) s := by
      simpa using (((hasDerivAt_id s).mul_const M.trace).neg.exp)
    convert (hasDerivAt_det_exp_three M s).mul he using 1
    ring
  have hc := is_const_of_deriv_eq_zero (fun s => (hf s).differentiableAt)
    (fun s => (hf s).deriv) t 0
  have hp : (exp (t • M)).det * Real.exp (-(t * M.trace)) = 1 := by
    simpa [f, NormedSpace.exp_zero] using hc
  calc
    (exp (t • M)).det =
        ((exp (t • M)).det * Real.exp (-(t * M.trace))) *
          Real.exp (t * M.trace) := by
      rw [mul_assoc, ← Real.exp_add]
      simp
    _ = Real.exp (t * M.trace) := by rw [hp, one_mul]

theorem det_exp_three (M : RealMatrix3) :
    (exp M).det = Real.exp M.trace := by
  simpa only [one_smul, one_mul] using det_exp_three_smul M 1

#print axioms det_exp_three

/-- 叉积在一般线性变换下的多项式恒等式，不要求矩阵可逆。 -/
theorem transpose_mulVec_cross_mulVec (B : RealMatrix3) (u v : Fin 3 → ℝ) :
    Bᵀ *ᵥ ((B *ᵥ u) ⨯₃ (B *ᵥ v)) = B.det • (u ⨯₃ v) := by
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.transpose_apply,
      cross_apply, Matrix.det_fin_three] <;> ring

/-- 可逆变换的叉积公式，显式使用逆转置。 -/
theorem cross_mulVec_of_det_ne_zero (B : RealMatrix3) (hB : B.det ≠ 0)
    (u v : Fin 3 → ℝ) :
    (B *ᵥ u) ⨯₃ (B *ᵥ v) = B.det • ((B⁻¹)ᵀ *ᵥ (u ⨯₃ v)) := by
  have hi : IsUnit Bᵀ.det := by simpa using (isUnit_iff_ne_zero.mpr hB)
  have h := congrArg (fun w => (Bᵀ)⁻¹ *ᵥ w) (transpose_mulVec_cross_mulVec B u v)
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hi, Matrix.one_mulVec] at h
  simpa only [Matrix.mulVec_smul, ← Matrix.transpose_nonsing_inv] using h

abbrev euclideanVector3 (v : Fin 3 → ℝ) : EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm v

theorem euclideanVector3_norm_sq (v : Fin 3 → ℝ) :
    ‖euclideanVector3 v‖ ^ 2 = v ⬝ᵥ v := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [euclideanVector3, dotProduct, pow_two]

/-- 两列 Gram 行列式等于其叉积的欧氏长度平方。 -/
theorem det_gram_two_eq_cross_sq (P : Matrix (Fin 3) (Fin 2) ℝ) :
    (Pᵀ * P).det =
      ‖euclideanVector3 ((fun i => P i 0) ⨯₃ (fun i => P i 1))‖ ^ 2 := by
  rw [euclideanVector3_norm_sq, cross_dot_cross]
  simp only [Matrix.det_fin_two, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_three, dotProduct]

/-- 逆转置叉积公式的欧氏算子范数版本。 -/
theorem norm_cross_mulVec_le (B : RealMatrix3) (hB : B.det ≠ 0)
    (u v : Fin 3 → ℝ) :
    ‖euclideanVector3 ((B *ᵥ u) ⨯₃ (B *ᵥ v))‖ ≤
      |B.det| * ‖B⁻¹‖ * ‖euclideanVector3 (u ⨯₃ v)‖ := by
  rw [cross_mulVec_of_det_ne_zero B hB, euclideanVector3, map_smul, norm_smul]
  have hm := Matrix.l2_opNorm_mulVec (B⁻¹)ᵀ (euclideanVector3 (u ⨯₃ v))
  have ht : ‖(B⁻¹)ᵀ‖ = ‖B⁻¹‖ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.l2_opNorm_conjTranspose B⁻¹
  calc
    ‖B.det‖ * ‖(EuclideanSpace.equiv (Fin 3) ℝ).symm ((B⁻¹)ᵀ *ᵥ (u ⨯₃ v))‖
        ≤ ‖B.det‖ * (‖(B⁻¹)ᵀ‖ * ‖euclideanVector3 (u ⨯₃ v)‖) :=
      mul_le_mul_of_nonneg_left hm (norm_nonneg _)
    _ = |B.det| * ‖B⁻¹‖ * ‖euclideanVector3 (u ⨯₃ v)‖ := by
      rw [ht, Real.norm_eq_abs, mul_assoc]

/-- 正交归一两列在可逆三维变换后的面积平方上界。 -/
theorem det_compressed_gram_le (B : RealMatrix3) (hB : B.det ≠ 0)
    (P : Matrix (Fin 3) (Fin 2) ℝ) (hP : Pᵀ * P = 1) :
    (Pᵀ * Bᵀ * B * P).det ≤ B.det ^ 2 * ‖B⁻¹‖ ^ 2 := by
  let u : Fin 3 → ℝ := fun i => P i 0
  let v : Fin 3 → ℝ := fun i => P i 1
  have hp2 : ‖euclideanVector3 (u ⨯₃ v)‖ ^ 2 = 1 := by
    change ‖euclideanVector3 ((fun i => P i 0) ⨯₃ (fun i => P i 1))‖ ^ 2 = 1
    rw [← det_gram_two_eq_cross_sq, hP, Matrix.det_one]
  have hp1 : ‖euclideanVector3 (u ⨯₃ v)‖ = 1 := by
    nlinarith [norm_nonneg (euclideanVector3 (u ⨯₃ v))]
  have hb := norm_cross_mulVec_le B hB u v
  rw [hp1, mul_one] at hb
  have hb2 : ‖euclideanVector3 ((B *ᵥ u) ⨯₃ (B *ᵥ v))‖ ^ 2 ≤
      B.det ^ 2 * ‖B⁻¹‖ ^ 2 := by
    have hs := (sq_le_sq₀ (norm_nonneg (euclideanVector3 ((B *ᵥ u) ⨯₃ (B *ᵥ v))))
      (mul_nonneg (abs_nonneg B.det) (norm_nonneg B⁻¹))).mpr hb
    simpa only [mul_pow, sq_abs] using hs
  calc
    (Pᵀ * Bᵀ * B * P).det = ((B * P)ᵀ * (B * P)).det := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = ‖euclideanVector3 ((fun i => (B * P) i 0) ⨯₃
        (fun i => (B * P) i 1))‖ ^ 2 := det_gram_two_eq_cross_sq (B * P)
    _ ≤ B.det ^ 2 * ‖B⁻¹‖ ^ 2 := by
      have h0 : (fun i => (B * P) i 0) = B *ᵥ u := rfl
      have h1 : (fun i => (B * P) i 1) = B *ᵥ v := rfl
      rw [h0, h1]
      exact hb2

/-- 实矩阵指数自动满足可逆前提，供半程动力学直接调用。 -/
theorem det_compressed_exp_gram_le (M : RealMatrix3)
    (P : Matrix (Fin 3) (Fin 2) ℝ) (hP : Pᵀ * P = 1) :
    (Pᵀ * (exp M)ᵀ * exp M * P).det ≤
      Real.exp (2 * M.trace) * ‖(exp M)⁻¹‖ ^ 2 := by
  have hd : (exp M).det ≠ 0 := by rw [det_exp_three]; exact Real.exp_ne_zero _
  have h := det_compressed_gram_le (exp M) hd P hP
  rw [det_exp_three] at h
  have he : Real.exp (2 * M.trace) = Real.exp M.trace ^ 2 := by
    rw [two_mul, Real.exp_add, pow_two]
  simpa only [he] using h

#print axioms cross_mulVec_of_det_ne_zero
#print axioms det_gram_two_eq_cross_sq
#print axioms norm_cross_mulVec_le
#print axioms det_compressed_gram_le
#print axioms det_compressed_exp_gram_le

end TwoStateQuantumEmbedding
