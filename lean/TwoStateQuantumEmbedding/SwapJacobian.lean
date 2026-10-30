import TwoStateQuantumEmbedding.SwapHamiltonianBlock
import TwoStateQuantumEmbedding.SwapLeadingJacobian
import TwoStateQuantumEmbedding.SwapDissipativeBlock
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic

/-! 实际七变量 Jacobian；各矩阵块从实际函数导数导出。 -/
noncomputable section
open Matrix Filter
open scoped Topology ContDiff Matrix.Norms.Operator

namespace TwoStateQuantumEmbedding.ActualSwapSystem
open SwapLeadingJacobian

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

def systemAtZero (y : Parameters) : Parameters := stationarity (0, y)

def jacobian : Matrix (Fin 7) (Fin 7) ℝ :=
  fun i j => fderiv ℝ systemAtZero baseParameters (Pi.single j 1) i

theorem analytic_systemAtZero (y : Parameters) : AnalyticAt ℝ systemAtZero y :=
  (analytic_stationarity (0, y)).comp (f := fun z : Parameters => (0, z))
    ((ContinuousLinearMap.inr ℝ ℝ Parameters).analyticAt y)

theorem jacobian_entry (i j : Fin 7) : jacobian i j =
    fderiv ℝ (fun y => systemAtZero y i) baseParameters (Pi.single j 1) := by
  have h := (hasFDerivAt_apply (𝕜 := ℝ) i (systemAtZero baseParameters)).comp baseParameters
    (analytic_systemAtZero baseParameters).differentiableAt.hasFDerivAt
  rw [show fderiv ℝ (fun y => systemAtZero y i) baseParameters = _ from h.fderiv]
  rfl

theorem systemAtZero_row_zero : (fun y => systemAtZero y 0) =
    fun y => fderiv ℝ frozenObjective y (Pi.single 0 1) := by
  funext y
  simp [systemAtZero, stationarity_at_zero]

theorem systemAtZero_row_one : (fun y => systemAtZero y 1) =
    fun y => fderiv ℝ frozenObjective y (Pi.single 1 1) := by
  funext y
  simp [systemAtZero, stationarity_at_zero]

theorem jacobian_row_zero (j : Fin 7) : jacobian 0 j =
    if j = 0 then Swap.gap / 2 else 0 := by
  rw [jacobian_entry, systemAtZero_row_zero]
  have h := frozenObjective_fderiv_hasFDerivAt_base.clm_apply
    (hasFDerivAt_const (Pi.single (0 : Fin 7) (1 : ℝ)) baseParameters)
  rw [show fderiv ℝ (fun y => fderiv ℝ frozenObjective y (Pi.single 0 1)) baseParameters = _ from h.fderiv]
  fin_cases j <;> simp [frozenHessian, smul_eq_mul]
  all_goals ring

theorem jacobian_row_one (j : Fin 7) : jacobian 1 j =
    if j = 1 then 8 * Swap.gap / Real.pi ^ 2 else 0 := by
  rw [jacobian_entry, systemAtZero_row_one]
  have h := frozenObjective_fderiv_hasFDerivAt_base.clm_apply
    (hasFDerivAt_const (Pi.single (1 : Fin 7) (1 : ℝ)) baseParameters)
  rw [show fderiv ℝ (fun y => fderiv ℝ frozenObjective y (Pi.single 1 1)) baseParameters = _ from h.fderiv]
  fin_cases j <;> simp [frozenHessian, smul_eq_mul]
  all_goals ring

theorem systemAtZero_first_two : systemAtZero baseParameters 0 = 0 ∧
    systemAtZero baseParameters 1 = 0 := by
  rw [show systemAtZero baseParameters 0 = _ from congrFun systemAtZero_row_zero baseParameters,
    show systemAtZero baseParameters 1 = _ from congrFun systemAtZero_row_one baseParameters,
    frozenObjective_hasFDerivAt_base.fderiv]
  simp

theorem systemAtZero_row_scale : (fun y => systemAtZero y 2) = scaleAtZero := by
  funext y
  simp [systemAtZero, stationarity_at_zero]

theorem systemAtZero_row_direction (j : Fin 4) :
    (fun y => systemAtZero y (directionIndex j)) = zeroDivided j := by
  funext y
  fin_cases j <;> simp [systemAtZero, stationarity, directionIndex, zeroDivided]

theorem jacobian_scale_multiplier : jacobian 2 2 = -beta := by
  rw [jacobian_entry, systemAtZero_row_scale, scaleAtZero_multiplier_derivative]

theorem jacobian_scale_direction (j : Fin 4) : jacobian 2 (directionIndex j) = 0 := by
  rw [jacobian_entry, systemAtZero_row_scale]
  exact scaleAtZero_direction_derivative j

theorem jacobian_direction_block (i j : Fin 4) :
    jacobian (directionIndex i) (directionIndex j) = directionHessianMatrix i j := by
  rw [jacobian_entry, systemAtZero_row_direction]
  exact (zeroDivided_direction_derivative i j).trans (directionHessianMatrix_eq i j).symm

theorem systemAtZero_base : systemAtZero baseParameters = 0 := by
  simp [systemAtZero, stationarity_at_zero, frozenObjective_hasFDerivAt_base.fderiv,
    scaleAtZero_base, scaleAtZero_direction_derivative]

theorem jacobian_lower_triangular : jacobian.IsLowerTriangular := by
  have hs0 := jacobian_scale_direction 0
  have hs1 := jacobian_scale_direction 1
  have hs2 := jacobian_scale_direction 2
  have hs3 := jacobian_scale_direction 3
  have h01 := jacobian_direction_block 0 1
  have h02 := jacobian_direction_block 0 2
  have h03 := jacobian_direction_block 0 3
  have h12 := jacobian_direction_block 1 2
  have h13 := jacobian_direction_block 1 3
  have h23 := jacobian_direction_block 2 3
  norm_num [directionIndex, directionHessianMatrix, Matrix.diagonal] at hs0 hs1 hs2 hs3 h01 h02 h03 h12 h13 h23
  intro i j hij
  change i < j at hij
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals simp_all [jacobian_row_zero, jacobian_row_one]

theorem jacobian_determinant :
    jacobian.det = -(16 * beta * Swap.gap ^ 6) / Real.pi ^ 2 := by
  have h0 := jacobian_direction_block 0 0
  have h1 := jacobian_direction_block 1 1
  have h2 := jacobian_direction_block 2 2
  have h3 := jacobian_direction_block 3 3
  norm_num [directionIndex, directionHessianMatrix, Matrix.diagonal] at h0 h1 h2 h3
  rw [Matrix.det_of_isLowerTriangular jacobian jacobian_lower_triangular]
  simp [Fin.prod_univ_succ, jacobian_row_zero, jacobian_row_one,
    jacobian_scale_multiplier, h0, h1, h2, h3]
  ring

theorem jacobian_nonsingular : jacobian.det ≠ 0 := by
  rw [jacobian_determinant]
  apply div_ne_zero
  · exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt beta_pos))
      (pow_ne_zero _ (ne_of_gt Swap.gap_pos)))
  · exact pow_ne_zero _ Real.pi_ne_zero

#print axioms analytic_systemAtZero
#print axioms jacobian_entry
#print axioms systemAtZero_row_zero
#print axioms systemAtZero_row_one
#print axioms jacobian_row_zero
#print axioms jacobian_row_one
#print axioms systemAtZero_first_two
#print axioms systemAtZero_row_scale
#print axioms systemAtZero_row_direction
#print axioms jacobian_scale_multiplier
#print axioms jacobian_scale_direction
#print axioms jacobian_direction_block
#print axioms systemAtZero_base
#print axioms jacobian_lower_triangular
#print axioms jacobian_determinant
#print axioms jacobian_nonsingular

end TwoStateQuantumEmbedding.ActualSwapSystem
