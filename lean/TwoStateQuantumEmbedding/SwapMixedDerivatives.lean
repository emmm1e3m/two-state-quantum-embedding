import TwoStateQuantumEmbedding.ActualSwapSystem
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic

/-! 实际驻点系统中混合导数与尺度行的连接。 -/
noncomputable section
open scoped Topology ContDiff Matrix.Norms.Operator

namespace TwoStateQuantumEmbedding.ActualSwapSystem

theorem objective_second_direction (p u v : Input) :
    fderiv ℝ (fun q => fderiv ℝ objective q u) p v =
      fderiv ℝ (fderiv ℝ objective) p v u := by
  rw [fderiv_clm_apply (analytic_objective p).fderiv.differentiableAt (differentiableAt_const u)]
  simp

theorem objective_mixed_symmetry (p u v : Input) :
    fderiv ℝ (fun q => fderiv ℝ objective q u) p v =
      fderiv ℝ (fun q => fderiv ℝ objective q v) p u := by
  rw [objective_second_direction, objective_second_direction]
  exact (analytic_objective p).contDiffAt.isSymmSndFDerivAt_of_omega v u

/-- k=0 处的尺度驻点行仍保留所有七个参数。 -/
def scaleAtZero (y : Parameters) : ℝ := fderiv ℝ objective (0, y) (1, 0)

def frozenObjective (y : Parameters) : ℝ := objective (0, y)

theorem analytic_frozenObjective (y : Parameters) : AnalyticAt ℝ frozenObjective y :=
  (analytic_objective (0, y)).comp (f := fun z : Parameters => (0, z))
    ((ContinuousLinearMap.inr ℝ ℝ Parameters).analyticAt y)

theorem analytic_scaleAtZero (y : Parameters) : AnalyticAt ℝ scaleAtZero y :=
  (analytic_objective_direction (1, 0) (0, y)).comp (f := fun z : Parameters => (0, z))
    ((ContinuousLinearMap.inr ℝ ℝ Parameters).analyticAt y)

theorem objective_parameter_direction_at_zero (y v : Parameters) :
    fderiv ℝ objective (0, y) (0, v) = fderiv ℝ frozenObjective y v := by
  have h := (analytic_objective (0, y)).differentiableAt.hasFDerivAt.comp y
    (hasFDerivAt_prodMk_right (0 : ℝ) y)
  rw [show fderiv ℝ frozenObjective y = _ from h.fderiv]
  rfl

theorem dividedDirection_zero_eq_scale_direction (j : Fin 4) (y : Parameters) :
    dividedDirection j (0, y) = fderiv ℝ scaleAtZero y (directionVector j) := by
  have hleft : deriv (fun k : ℝ => fderiv ℝ objective (k, y) (0, directionVector j)) 0 =
      fderiv ℝ (fun p => fderiv ℝ objective p (0, directionVector j)) (0, y) (1, 0) := by
    have hi : HasDerivAt (fun k : ℝ => (k, y)) (1, 0) 0 :=
      (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 y)
    exact ((analytic_objective_direction (0, directionVector j) (0, y)).differentiableAt.hasFDerivAt.comp_hasDerivAt 0 hi).deriv
  have hright : fderiv ℝ scaleAtZero y (directionVector j) =
      fderiv ℝ (fun p => fderiv ℝ objective p (1, 0)) (0, y) (0, directionVector j) := by
    have h := (analytic_objective_direction (1, 0) (0, y)).differentiableAt.hasFDerivAt.comp y
      (hasFDerivAt_prodMk_right (0 : ℝ) y)
    rw [show fderiv ℝ scaleAtZero y = _ from h.fderiv]
    rfl
  rw [← dividedDirection_zero_eq_mixed_derivative, hleft, hright]
  exact objective_mixed_symmetry _ _ _

/-- 基点超平面上的实际系统完全由冻结目标和尺度行的导数组成。 -/
theorem stationarity_at_zero (y : Parameters) : stationarity (0, y) =
    ![fderiv ℝ frozenObjective y (Pi.single 0 1),
      fderiv ℝ frozenObjective y (Pi.single 1 1), scaleAtZero y,
      fderiv ℝ scaleAtZero y (directionVector 0),
      fderiv ℝ scaleAtZero y (directionVector 1),
      fderiv ℝ scaleAtZero y (directionVector 2),
      fderiv ℝ scaleAtZero y (directionVector 3)] := by
  ext i
  fin_cases i <;> simp [stationarity]
  · exact objective_parameter_direction_at_zero _ _
  · exact objective_parameter_direction_at_zero _ _
  · rfl
  all_goals exact dividedDirection_zero_eq_scale_direction _ _

#print axioms objective_second_direction
#print axioms objective_mixed_symmetry
#print axioms dividedDirection_zero_eq_scale_direction
#print axioms analytic_frozenObjective
#print axioms analytic_scaleAtZero
#print axioms objective_parameter_direction_at_zero
#print axioms stationarity_at_zero

end TwoStateQuantumEmbedding.ActualSwapSystem
