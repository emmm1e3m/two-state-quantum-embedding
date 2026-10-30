import TwoStateQuantumEmbedding.GKSLAlgebra
import Mathlib.Data.Matrix.Basis
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-! 实线性矩阵泛函在 Hermitian 方向上的实际迹梯度。 -/
noncomputable section
open Matrix Complex
open scoped BigOperators Matrix.Norms.Operator

namespace TwoStateQuantumEmbedding.TraceGradient
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- 未对称化的复矩阵表示实线性泛函，虚部符号来自实迹配对。 -/
def rawGradient (L : Matrix n n ℂ →L[ℝ] ℝ) : Matrix n n ℂ :=
  fun i j => (L (Matrix.single j i 1) : ℂ) -
    Complex.I * (L (Matrix.single j i Complex.I) : ℂ)

theorem apply_single (L : Matrix n n ℂ →L[ℝ] ℝ) (i j : n) (z : ℂ) :
    L (Matrix.single i j z) = z.re * L (Matrix.single i j 1) +
      z.im * L (Matrix.single i j Complex.I) := by
  have h : Matrix.single i j z =
      z.re • Matrix.single i j (1 : ℂ) + z.im • Matrix.single i j Complex.I := by
    rw [Matrix.smul_single, Matrix.smul_single, ← Matrix.single_add]
    congr 1
    apply Complex.ext <;> simp
  rw [h, map_add, map_smul, map_smul]
  rfl

theorem rawGradient_pairing (L : Matrix n n ℂ →L[ℝ] ℝ) (W : Matrix n n ℂ) :
    (rawGradient L * W).trace.re = L W := by
  have hL : L W = ∑ i, ∑ j,
      ((W i j).re * L (Matrix.single i j 1) +
        (W i j).im * L (Matrix.single i j Complex.I)) := by
    calc
      L W = L (∑ i, ∑ j, Matrix.single i j (W i j)) :=
        congrArg L (Matrix.matrix_eq_sum_single W)
      _ = _ := by
        simp only [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact apply_single L i j (W i j)
  rw [hL]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum, rawGradient,
    Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, Complex.sub_im, Complex.mul_im,
    mul_zero, zero_mul, sub_zero, zero_add, one_mul, zero_sub, neg_mul, sub_neg_eq_add]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Hermitian 投影不改变 Hermitian 方向上的实迹配对。 -/
theorem re_trace_adjoint_pairing (A W : Matrix n n ℂ) (hW : W.IsHermitian) :
    (A.conjTranspose * W).trace.re = (A * W).trace.re := by
  have h : (A.conjTranspose * W).trace = star ((W * A).trace) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hW.eq]
  rw [h, Matrix.trace_mul_comm W A]
  rfl

def hermitianGradient (L : Matrix n n ℂ →L[ℝ] ℝ) : Matrix n n ℂ :=
  (1/2 : ℝ) • (rawGradient L + (rawGradient L).conjTranspose)

theorem hermitianGradient_isHermitian (L : Matrix n n ℂ →L[ℝ] ℝ) :
    (hermitianGradient L).IsHermitian := by
  rw [Matrix.IsHermitian, hermitianGradient, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
  simp only [star_trivial]
  rw [add_comm]

theorem hermitianGradient_pairing (L : Matrix n n ℂ →L[ℝ] ℝ)
    (W : Matrix n n ℂ) (hW : W.IsHermitian) :
    (hermitianGradient L * W).trace.re = L W := by
  simp only [hermitianGradient, Matrix.smul_mul, Matrix.add_mul,
    Matrix.trace_smul, Matrix.trace_add, Complex.smul_re, Complex.add_re, smul_eq_mul]
  rw [re_trace_adjoint_pairing _ W hW, rawGradient_pairing]
  ring

#print axioms rawGradient_pairing
#print axioms hermitianGradient_pairing
#print axioms hermitianGradient_isHermitian
end TwoStateQuantumEmbedding.TraceGradient
