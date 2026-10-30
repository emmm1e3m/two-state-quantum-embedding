import TwoStateQuantumEmbedding.SwapScaleDerivative
import TwoStateQuantumEmbedding.SwapLeadingJacobian
import Mathlib.Tactic

/-! 实际尺度行和四方向行的基点值及导数块。 -/
noncomputable section
open scoped Topology ContDiff Matrix.Norms.Operator
namespace TwoStateQuantumEmbedding.ActualSwapSystem
open SwapLeadingJacobian

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

def directionInsertion : Directions →L[ℝ] Parameters :=
  ({ toFun := fun u => ![0, 0, 0, u 0, u 1, u 2, u 3]
     map_add' := by intro u v; ext i; fin_cases i <;> simp
     map_smul' := by intro s u; ext i; fin_cases i <;> simp } : Directions →ₗ[ℝ] Parameters).toContinuousLinearMap

def directionSection (u : Directions) : Parameters :=
  ![Real.pi, 0, Swap.slope, 0, 0, 0, 0] + directionInsertion u

theorem directionInsertion_single (j : Fin 4) :
    directionInsertion (Pi.single j 1) = directionVector j := by
  ext i
  fin_cases j <;> fin_cases i <;>
    simp [directionInsertion, directionVector, directionIndex]

@[simp] theorem directionSection_base : directionSection baseDirection = baseParameters := by
  ext i
  fin_cases i <;> simp [directionSection, directionInsertion, baseDirection, baseParameters]

theorem directionSection_hasFDerivAt (u : Directions) :
    HasFDerivAt directionSection directionInsertion u :=
  directionInsertion.hasFDerivAt.const_add _

theorem scaleAtZero_directionSection (u : Directions) :
    scaleAtZero (directionSection u) = leadingDefect u := by
  have h := scaleAtZero_swap (directionSection u)
    (by simp [directionSection, directionInsertion]) (by simp [directionSection, directionInsertion])
  simpa [leadingDefect, direction, jumpDirection, directionSection, directionInsertion] using h

def zeroDivided (j : Fin 4) (y : Parameters) : ℝ := dividedDirection j (0, y)

theorem analytic_zeroDivided (j : Fin 4) (y : Parameters) : AnalyticAt ℝ (zeroDivided j) y :=
  (analytic_dividedDirection j (0, y)).comp (f := fun z : Parameters => (0, z))
    ((ContinuousLinearMap.inr ℝ ℝ Parameters).analyticAt y)

theorem zeroDivided_directionSection (j : Fin 4) (u : Directions) :
    zeroDivided j (directionSection u) = leadingGradient u j := by
  have hc := (analytic_scaleAtZero (directionSection u)).differentiableAt.hasFDerivAt.comp u
    (directionSection_hasFDerivAt u)
  have hf : (scaleAtZero ∘ directionSection) = leadingDefect := funext scaleAtZero_directionSection
  rw [hf] at hc
  have he := congrArg (fun L : Directions →L[ℝ] ℝ => L (Pi.single j 1)) hc.fderiv
  rw [leadingDefect_gradient] at he
  change leadingGradient u j = fderiv ℝ scaleAtZero (directionSection u)
    (directionInsertion (Pi.single j 1)) at he
  rw [directionInsertion_single, ← dividedDirection_zero_eq_scale_direction] at he
  exact he.symm

theorem scaleAtZero_base : scaleAtZero baseParameters = 0 := by
  rw [← directionSection_base, scaleAtZero_directionSection, leadingDefect_at_base]

theorem zeroDivided_base (j : Fin 4) : zeroDivided j baseParameters = 0 := by
  rw [← directionSection_base, zeroDivided_directionSection, leadingGradient_at_base]
  rfl

theorem scaleAtZero_direction_derivative (j : Fin 4) :
    fderiv ℝ scaleAtZero baseParameters (directionVector j) = 0 := by
  rw [← dividedDirection_zero_eq_scale_direction]
  exact zeroDivided_base j

theorem zeroDivided_direction_derivative (j l : Fin 4) :
    fderiv ℝ (zeroDivided j) baseParameters (directionVector l) =
      directionHessian (Pi.single l 1) j := by
  have hc := (analytic_zeroDivided j (directionSection baseDirection)).differentiableAt.hasFDerivAt.comp baseDirection
    (directionSection_hasFDerivAt baseDirection)
  rw [directionSection_base] at hc
  have hf : (zeroDivided j ∘ directionSection) = fun u => leadingGradient u j :=
    funext (zeroDivided_directionSection j)
  rw [hf] at hc
  have hg := (hasFDerivAt_apply (𝕜 := ℝ) j (leadingGradient baseDirection)).comp baseDirection
    (leadingGradient_hasFDerivAt baseDirection)
  have he := congrArg (fun L : Directions →L[ℝ] ℝ => L (Pi.single l 1)) (hc.unique hg)
  change fderiv ℝ (zeroDivided j) baseParameters (directionInsertion (Pi.single l 1)) = _ at he
  simpa [directionInsertion_single] using he

def multiplierSection (μ : ℝ) : Parameters :=
  baseParameters + (μ - Swap.slope) • Pi.single 2 1

@[simp] theorem multiplierSection_base : multiplierSection Swap.slope = baseParameters := by
  simp [multiplierSection]

theorem multiplierSection_hasDerivAt :
    HasDerivAt multiplierSection (Pi.single 2 1) Swap.slope := by
  convert (((hasDerivAt_id Swap.slope).sub_const Swap.slope).smul_const
      (Pi.single 2 1 : Parameters)).const_add baseParameters using 1
  · rfl
  · funext i
    change (Pi.single 2 1 : Parameters) i = (1 : ℝ) * (Pi.single 2 1 : Parameters) i
    simp

theorem scaleAtZero_multiplierSection (μ : ℝ) :
    scaleAtZero (multiplierSection μ) =
      Swap.qa 0 (direction baseDirection) - μ * Swap.qb 0 (direction baseDirection) := by
  have h := scaleAtZero_swap (multiplierSection μ)
    (by simp [multiplierSection, baseParameters]) (by simp [multiplierSection, baseParameters])
  simpa [multiplierSection, baseParameters, jumpDirection, direction, baseDirection] using h

theorem scaleAtZero_multiplier_derivative :
    fderiv ℝ scaleAtZero baseParameters (Pi.single 2 1) = -beta := by
  have hc := (analytic_scaleAtZero (multiplierSection Swap.slope)).differentiableAt.hasFDerivAt.comp_hasDerivAt
    Swap.slope multiplierSection_hasDerivAt
  rw [multiplierSection_base] at hc
  have he := hc.deriv
  have hf : (scaleAtZero ∘ multiplierSection) = fun μ =>
      Swap.qa 0 (direction baseDirection) - μ * Swap.qb 0 (direction baseDirection) :=
    funext scaleAtZero_multiplierSection
  rw [hf, scale_multiplier_derivative] at he
  exact he.symm

#print axioms directionInsertion_single
#print axioms directionSection_base
#print axioms directionSection_hasFDerivAt
#print axioms scaleAtZero_directionSection
#print axioms analytic_zeroDivided
#print axioms zeroDivided_directionSection
#print axioms scaleAtZero_base
#print axioms zeroDivided_base
#print axioms scaleAtZero_direction_derivative
#print axioms zeroDivided_direction_derivative
#print axioms multiplierSection_base
#print axioms multiplierSection_hasDerivAt
#print axioms scaleAtZero_multiplierSection
#print axioms scaleAtZero_multiplier_derivative

end TwoStateQuantumEmbedding.ActualSwapSystem
