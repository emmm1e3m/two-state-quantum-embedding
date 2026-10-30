import TwoStateQuantumEmbedding.SwapCore
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

/-! 已证明首阶复二次型的精确方向 Hessian；实际指数首阶桥由083提供。 -/
noncomputable section
open Matrix
namespace TwoStateQuantumEmbedding.SwapLeadingJacobian

abbrev Directions := Fin 4 → ℝ
def direction (u : Directions) : Fin 3 → ℂ := Swap.rankOneDirection (u 0) (u 1) (u 2) (u 3)
def leadingDefect (u : Directions) : ℝ := Swap.qa 0 (direction u) - Swap.slope * Swap.qb 0 (direction u)
def baseDirection : Directions := ![0, Swap.rootTwo / 2, 0, 0]
def beta : ℝ := 1 + 2 * Swap.rootTwo / Real.pi

theorem beta_pos : 0 < beta := by
  unfold beta
  positivity [Swap.rootTwo_pos, Real.pi_pos]

theorem leadingQb_at_base : Swap.qb 0 (direction baseDirection) = beta := by
  simpa [direction, baseDirection, beta] using Swap.equality_direction_value

theorem leadingDefect_eq : leadingDefect = fun u =>
    Swap.gap * (u 0 ^ 2 + (u 1 - Swap.rootTwo / 2) ^ 2 + (u 2 ^ 2 + u 3 ^ 2) / 2) := by
  funext u
  exact Swap.full_complex_leading_square _ _ _ _

def leadingGradient (u : Directions) : Directions :=
  ![2 * Swap.gap * u 0, 2 * Swap.gap * (u 1 - Swap.rootTwo / 2), Swap.gap * u 2, Swap.gap * u 3]

theorem leadingDefect_gradient (u : Directions) (j : Fin 4) :
    fderiv ℝ leadingDefect u (Pi.single j 1) = leadingGradient u j := by
  rw [leadingDefect_eq]
  have h0 := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) u).pow 2
  have h1 := ((hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 4) u).sub_const (Swap.rootTwo / 2)).pow 2
  have h2 := (hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 4) u).pow 2
  have h3 := (hasFDerivAt_apply (𝕜 := ℝ) (3 : Fin 4) u).pow 2
  have h := ((h0.add h1).add ((h2.add h3).mul_const (1 / 2 : ℝ))).const_mul Swap.gap
  have heq : (fun u : Directions =>
      Swap.gap * (u 0 ^ 2 + (u 1 - Swap.rootTwo / 2) ^ 2 + (u 2 ^ 2 + u 3 ^ 2) / 2)) =
      (fun u => Swap.gap * (u 0 ^ 2 + (u 1 - Swap.rootTwo / 2) ^ 2 + (u 2 ^ 2 + u 3 ^ 2) * (1 / 2))) := by
    funext u
    ring
  rw [heq]
  rw [show fderiv ℝ (fun u : Directions => Swap.gap *
    (u 0 ^ 2 + (u 1 - Swap.rootTwo / 2) ^ 2 + (u 2 ^ 2 + u 3 ^ 2) * (1 / 2))) u = _ from h.fderiv]
  fin_cases j <;> simp [leadingGradient] <;> ring

def directionHessian : Directions →L[ℝ] Directions :=
  ({ toFun := fun u => ![2 * Swap.gap * u 0, 2 * Swap.gap * u 1, Swap.gap * u 2, Swap.gap * u 3]
     map_add' := by
       intro u v
       ext i
       fin_cases i <;> simp <;> ring
     map_smul' := by
       intro s u
       ext i
       fin_cases i <;> simp [smul_eq_mul] <;> ring } : Directions →ₗ[ℝ] Directions).toContinuousLinearMap

theorem leadingGradient_eq : leadingGradient = fun u => directionHessian u - directionHessian baseDirection := by
  funext u
  ext i
  fin_cases i <;> simp [leadingGradient, directionHessian, baseDirection]
  all_goals ring

theorem leadingGradient_hasFDerivAt (u : Directions) :
    HasFDerivAt leadingGradient directionHessian u := by
  rw [leadingGradient_eq]
  exact directionHessian.hasFDerivAt.sub_const _

theorem leadingDefect_hessian (u : Directions) :
    fderiv ℝ (fun v : Directions => fun j : Fin 4 => fderiv ℝ leadingDefect v (Pi.single j 1)) u =
      directionHessian := by
  simp_rw [leadingDefect_gradient]
  exact (leadingGradient_hasFDerivAt u).fderiv

theorem leadingGradient_at_base : leadingGradient baseDirection = 0 := by
  rw [leadingGradient_eq]
  simp

theorem leadingDefect_at_base : leadingDefect baseDirection = 0 := by
  rw [leadingDefect_eq]
  simp [baseDirection]

theorem scale_multiplier_derivative :
    deriv (fun μ : ℝ => Swap.qa 0 (direction baseDirection) -
      μ * Swap.qb 0 (direction baseDirection)) Swap.slope = -beta := by
  simp [leadingQb_at_base]

def directionHessianMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![2 * Swap.gap, 2 * Swap.gap, Swap.gap, Swap.gap]

theorem directionHessianMatrix_eq (i j : Fin 4) :
    directionHessianMatrix i j = directionHessian (Pi.single j 1) i := by
  fin_cases i <;> fin_cases j <;> simp [directionHessianMatrix, directionHessian, Matrix.diagonal]

theorem directionHessianMatrix_det : directionHessianMatrix.det = 4 * Swap.gap ^ 4 := by
  simp [directionHessianMatrix, Matrix.det_diagonal, Fin.prod_univ_succ]
  ring

theorem directionHessianMatrix_nonsingular : directionHessianMatrix.det ≠ 0 := by
  rw [directionHessianMatrix_det]
  exact ne_of_gt (by positivity [Swap.gap_pos])

#print axioms leadingDefect_eq
#print axioms beta_pos
#print axioms leadingQb_at_base
#print axioms leadingDefect_gradient
#print axioms leadingGradient_eq
#print axioms leadingGradient_hasFDerivAt
#print axioms leadingDefect_hessian
#print axioms leadingGradient_at_base
#print axioms leadingDefect_at_base
#print axioms scale_multiplier_derivative
#print axioms directionHessianMatrix_eq
#print axioms directionHessianMatrix_det
#print axioms directionHessianMatrix_nonsingular
end TwoStateQuantumEmbedding.SwapLeadingJacobian
