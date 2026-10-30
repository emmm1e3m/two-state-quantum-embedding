import TwoStateQuantumEmbedding.SwapMixedDerivatives
import TwoStateQuantumEmbedding.HamiltonianHessian
import Mathlib.Tactic

/-! 将真实二维 Hamiltonian Hessian 接到七变量冻结目标。 -/
noncomputable section
open Filter
open scoped Topology ContDiff Matrix.Norms.Operator

namespace TwoStateQuantumEmbedding.ActualSwapSystem

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000


abbrev omegaDual : Parameters →L[ℝ] ℝ := ContinuousLinearMap.proj 0
abbrev hDual : Parameters →L[ℝ] ℝ := ContinuousLinearMap.proj 1
abbrev multiplierDual : Parameters →L[ℝ] ℝ := ContinuousLinearMap.proj 2
def hamiltonianProjection : Parameters →L[ℝ] HamiltonianHessian.Point := omegaDual.prod hDual

@[simp] theorem hamiltonianProjection_base : hamiltonianProjection baseParameters = HamiltonianHessian.base := by
  simp [hamiltonianProjection, baseParameters, HamiltonianHessian.base]

def frozenModel (y : Parameters) : ℝ :=
  (1 - y 2) * HamiltonianHessian.explicitProbability (hamiltonianProjection y)

def frozenGradient (y : Parameters) : Parameters →L[ℝ] ℝ :=
  (-HamiltonianHessian.explicitProbability (hamiltonianProjection y)) • multiplierDual +
    (1 - y 2) • (HamiltonianHessian.gradientExpression (hamiltonianProjection y)).comp hamiltonianProjection

def frozenHessian : Parameters →L[ℝ] (Parameters →L[ℝ] ℝ) :=
  Swap.gap • ((1 / 2 : ℝ) • omegaDual.smulRight omegaDual +
    (8 / Real.pi ^ 2) • hDual.smulRight hDual)

theorem hamiltonianProjection_tendsto :
    Tendsto hamiltonianProjection (𝓝 baseParameters) (𝓝 HamiltonianHessian.base) := by
  rw [← hamiltonianProjection_base]
  exact hamiltonianProjection.continuous.continuousAt

theorem radius_positive_eventually :
    ∀ᶠ y in 𝓝 baseParameters, 0 < HamiltonianHessian.radiusFunction (hamiltonianProjection y) := by
  exact hamiltonianProjection_tendsto.eventually
    (HamiltonianHessian.radiusFunction_continuous.continuousAt.eventually (lt_mem_nhds HamiltonianHessian.radiusFunction_base_pos))

theorem frozenObjective_eventually_eq_model :
    frozenObjective =ᶠ[𝓝 baseParameters] frozenModel := by
  have he := hamiltonianProjection_tendsto.eventually
    (HamiltonianHessian.canonicalOutput_eventually_eq_diagonal.and HamiltonianHessian.actual_eventually_eq_explicit)
  filter_upwards [he] with y hy
  have hc := probability_eq_canonical (0, y)
  simp only [kossakowskiMatrix, zero_smul] at hc
  have hd : (probabilityA (0, y), probabilityB (0, y)) =
      (HamiltonianHessian.explicitProbability (hamiltonianProjection y), HamiltonianHessian.explicitProbability (hamiltonianProjection y)) := by
    rw [hc]
    convert hy.1.trans (congrArg (fun x : ℝ => (x, x)) hy.2) using 1
    rfl
  have ha := congrArg Prod.fst hd
  have hb := congrArg Prod.snd hd
  change probabilityA (0, y) - y 2 * probabilityB (0, y) = _
  dsimp only at ha hb
  rw [ha, hb]
  unfold frozenModel
  ring

theorem frozenModel_hasFDerivAt (y : Parameters)
    (hy : 0 < HamiltonianHessian.radiusFunction (hamiltonianProjection y)) :
    HasFDerivAt frozenModel (frozenGradient y) y := by
  have hp := (HamiltonianHessian.explicitProbability_hasFDerivAt (hamiltonianProjection y) hy).comp y
    hamiltonianProjection.hasFDerivAt
  have hm := (hasFDerivAt_const (1 : ℝ) y).sub multiplierDual.hasFDerivAt
  convert hm.mul hp using 1
  · rfl
  · ext v
    simp [frozenGradient, smul_eq_mul]
    ring

theorem explicitProbability_at_base : HamiltonianHessian.explicitProbability HamiltonianHessian.base = 0 := by
  rw [← HamiltonianHessian.actual_eventually_eq_explicit.eq_of_nhds, HamiltonianHessian.actual_base]

theorem frozenGradient_at_base : frozenGradient baseParameters = 0 := by
  simp [frozenGradient, HamiltonianHessian.gradientExpression_base, explicitProbability_at_base]

theorem frozenObjective_hasFDerivAt_base :
    HasFDerivAt frozenObjective (0 : Parameters →L[ℝ] ℝ) baseParameters := by
  have hd := frozenModel_hasFDerivAt baseParameters (by simpa using HamiltonianHessian.radiusFunction_base_pos)
  rw [frozenGradient_at_base] at hd
  exact hd.congr_of_eventuallyEq frozenObjective_eventually_eq_model

theorem frozenGradient_hasFDerivAt_base :
    HasFDerivAt frozenGradient frozenHessian baseParameters := by
  have hg0 : HamiltonianHessian.gradientExpression (Real.pi, 0) = 0 :=
    HamiltonianHessian.gradientExpression_base
  have hp := (HamiltonianHessian.explicitProbability_hasFDerivAt HamiltonianHessian.base HamiltonianHessian.radiusFunction_base_pos).comp baseParameters
    hamiltonianProjection.hasFDerivAt
  have hg := HamiltonianHessian.gradientExpression_hasFDerivAt_base.comp baseParameters
    hamiltonianProjection.hasFDerivAt
  have hc := hg.clm_comp (hasFDerivAt_const hamiltonianProjection baseParameters)
  have hm := (hasFDerivAt_const (1 : ℝ) baseParameters).sub multiplierDual.hasFDerivAt
  convert (hp.neg.smul_const multiplierDual).add (hm.smul hc) using 1
  · rfl
  · ext v w
    simp [frozenHessian, hg0,
      hamiltonianProjection, HamiltonianHessian.expectedHessian, baseParameters, HamiltonianHessian.base, Swap.gap,
      smul_eq_mul]

theorem frozenObjective_fderiv_hasFDerivAt_base :
    HasFDerivAt (fderiv ℝ frozenObjective) frozenHessian baseParameters := by
  have hg : fderiv ℝ frozenModel =ᶠ[𝓝 baseParameters] frozenGradient := by
    filter_upwards [radius_positive_eventually] with y hy
    exact (frozenModel_hasFDerivAt y hy).fderiv
  exact frozenGradient_hasFDerivAt_base.congr_of_eventuallyEq
    (frozenObjective_eventually_eq_model.fderiv.trans hg)

theorem frozenObjective_hessian_apply (v w : Parameters) :
    fderiv ℝ (fderiv ℝ frozenObjective) baseParameters v w =
      Swap.gap * (v 0 * w 0 / 2 + (8 / Real.pi ^ 2) * v 1 * w 1) := by
  rw [frozenObjective_fderiv_hasFDerivAt_base.fderiv]
  simp [frozenHessian, smul_eq_mul]
  ring

#print axioms hamiltonianProjection_base
#print axioms hamiltonianProjection_tendsto
#print axioms radius_positive_eventually
#print axioms frozenObjective_eventually_eq_model
#print axioms frozenModel_hasFDerivAt
#print axioms explicitProbability_at_base
#print axioms frozenGradient_at_base
#print axioms frozenObjective_hasFDerivAt_base
#print axioms frozenGradient_hasFDerivAt_base
#print axioms frozenObjective_fderiv_hasFDerivAt_base
#print axioms frozenObjective_hessian_apply

end TwoStateQuantumEmbedding.ActualSwapSystem

