import TwoStateQuantumEmbedding.SwapJacobian
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic

/-! 实际七变量系统的解析隐函数与真实概率的再参数化。 -/
noncomputable section
open Filter Set
open scoped Topology ContDiff Matrix.Norms.Operator
namespace TwoStateQuantumEmbedding.ActualSwapSystem
open SwapLeadingJacobian

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

theorem systemDerivative_matrix :
    LinearMap.toMatrix' (fderiv ℝ systemAtZero baseParameters).toLinearMap = jacobian := by
  ext i j
  rfl

theorem systemDerivative_isInvertible : (fderiv ℝ systemAtZero baseParameters).IsInvertible := by
  have hd : IsUnit (fderiv ℝ systemAtZero baseParameters).toLinearMap.det := by
    rw [← LinearMap.det_toMatrix', systemDerivative_matrix]
    exact isUnit_iff_ne_zero.mpr jacobian_nonsingular
  refine ⟨(LinearMap.equivOfIsUnitDet hd).toContinuousLinearEquiv, ?_⟩
  ext y i
  simp

theorem stationarity_partial_isInvertible :
    (fderiv ℝ stationarity basePoint ∘L ContinuousLinearMap.inr ℝ ℝ Parameters).IsInvertible := by
  have hc := (analytic_stationarity basePoint).differentiableAt.hasFDerivAt.comp baseParameters
    (hasFDerivAt_prodMk_right (0 : ℝ) baseParameters)
  have he : fderiv ℝ systemAtZero baseParameters =
      fderiv ℝ stationarity basePoint ∘L ContinuousLinearMap.inr ℝ ℝ Parameters := hc.fderiv
  rw [← he]
  exact systemDerivative_isInvertible

theorem actual_analytic_stationary_branch :
    ∃ (ψ : ℝ → Parameters) (U : Set ℝ) (V : Set Parameters),
      IsOpen U ∧ (0 : ℝ) ∈ U ∧ IsOpen V ∧ baseParameters ∈ V ∧
      ψ 0 = baseParameters ∧ AnalyticOnNhd ℝ ψ U ∧ MapsTo ψ U V ∧
      (∀ k ∈ U, stationarity (k, ψ k) = 0) ∧
      (∀ k ∈ U, ∀ y ∈ V, stationarity (k, y) = 0 ↔ ψ k = y) := by
  exact QuantumEmbedding.AnalyticFoundation.analytic_implicit_open_neighborhoods
    (analytic_stationarity basePoint) systemAtZero_base stationarity_partial_isInvertible

def zeroProbabilityB (y : Parameters) : ℝ := probabilityB (0, y)

theorem zeroProbabilityB_eq : zeroProbabilityB = HamiltonianHessian.actualB ∘ hamiltonianProjection := by
  funext y
  have h := congrArg Prod.snd (probability_eq_canonical (0, y))
  simpa [zeroProbabilityB, HamiltonianHessian.actualB, hamiltonianProjection,
    hamiltonianVector, kossakowskiMatrix] using h

theorem zeroProbabilityB_hasFDerivAt_base :
    HasFDerivAt zeroProbabilityB (0 : Parameters →L[ℝ] ℝ) baseParameters := by
  rw [zeroProbabilityB_eq]
  have h : HasFDerivAt HamiltonianHessian.actualB (0 : HamiltonianHessian.Point →L[ℝ] ℝ)
      (hamiltonianProjection baseParameters) := by
    simpa using HamiltonianHessian.actualB_hasFDerivAt_base
  simpa using h.comp baseParameters hamiltonianProjection.hasFDerivAt

theorem probabilityB_base : probabilityB basePoint = 0 := by
  change zeroProbabilityB baseParameters = 0
  rw [zeroProbabilityB_eq]
  simp [HamiltonianHessian.actualB_base]

theorem probabilityB_parameter_derivative (v : Parameters) :
    fderiv ℝ probabilityB basePoint (0, v) = 0 := by
  have hc := (analytic_probabilityB basePoint).differentiableAt.hasFDerivAt.comp baseParameters
    (hasFDerivAt_prodMk_right (0 : ℝ) baseParameters)
  have he := congrArg (fun L : Parameters →L[ℝ] ℝ => L v)
    (hc.unique zeroProbabilityB_hasFDerivAt_base)
  exact he

theorem probabilityB_scale_derivative : fderiv ℝ probabilityB basePoint (1, 0) = beta := by
  have hb := hasDerivAt_probabilityB_swap baseParameters (by simp [baseParameters]) (by simp [baseParameters])
  have hv : Swap.qb 0 (jumpDirection baseParameters) = beta := by
    simpa [jumpDirection, baseParameters, direction, baseDirection] using leadingQb_at_base
  rw [hv] at hb
  have hi : HasDerivAt (fun k : ℝ => (k, baseParameters)) (1, 0) 0 :=
    (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 baseParameters)
  have hc := (analytic_probabilityB (0, baseParameters)).differentiableAt.hasFDerivAt.comp_hasDerivAt 0 hi
  exact hc.unique hb

theorem probabilityB_derivative_apply (v : Input) : fderiv ℝ probabilityB basePoint v = v.1 * beta := by
  have he : v = v.1 • (1, (0 : Parameters)) + (0, v.2) := by ext <;> simp
  conv_lhs => rw [he]
  rw [map_add, map_smul, probabilityB_scale_derivative, probabilityB_parameter_derivative]
  simp [smul_eq_mul]

theorem probabilityB_along_analytic_curve {ψ : ℝ → Parameters}
    (hψ : AnalyticAt ℝ ψ 0) (hbase : ψ 0 = baseParameters) :
    AnalyticAt ℝ (fun k => probabilityB (k, ψ k)) 0 ∧
      HasDerivAt (fun k => probabilityB (k, ψ k)) beta 0 := by
  have hp : AnalyticAt ℝ probabilityB (0, ψ 0) := by
    simpa [hbase, basePoint] using analytic_probabilityB basePoint
  have ha := hp.comp (f := fun k : ℝ => (k, ψ k)) (analyticAt_id.prod hψ)
  have hi := (hasDerivAt_id (0 : ℝ)).prodMk hψ.differentiableAt.hasDerivAt
  have hb := hp.differentiableAt.hasFDerivAt.comp_hasDerivAt 0 hi
  refine ⟨ha, ?_⟩
  have he : fderiv ℝ probabilityB (0, ψ 0) (1, deriv ψ 0) = beta := by
    rw [hbase]
    simpa [basePoint] using probabilityB_derivative_apply (1, deriv ψ 0)
  rw [he] at hb
  convert hb using 1
  rfl

/-- 实际驻点解析支路及以真实 b 为参数的解析局部逆同时存在。 -/
theorem actual_stationary_arc_reparameterized :
    ∃ (ψ : ℝ → Parameters) (U : Set ℝ) (V : Set Parameters) (κ : ℝ → ℝ),
      IsOpen U ∧ (0 : ℝ) ∈ U ∧ IsOpen V ∧ baseParameters ∈ V ∧
      ψ 0 = baseParameters ∧ AnalyticOnNhd ℝ ψ U ∧ MapsTo ψ U V ∧
      (∀ k ∈ U, stationarity (k, ψ k) = 0) ∧
      (∀ k ∈ U, ∀ y ∈ V, stationarity (k, y) = 0 ↔ ψ k = y) ∧
      HasDerivAt (fun k => probabilityB (k, ψ k)) beta 0 ∧
      AnalyticAt ℝ κ 0 ∧ κ 0 = 0 ∧ AnalyticAt ℝ (ψ ∘ κ) 0 ∧
      (∀ᶠ k in 𝓝 0, κ (probabilityB (k, ψ k)) = k) ∧
      (∀ᶠ k in 𝓝 0, (ψ ∘ κ) (probabilityB (k, ψ k)) = ψ k) ∧
      (∀ᶠ b in 𝓝 0, probabilityB (κ b, ψ (κ b)) = b) := by
  obtain ⟨ψ, U, V, hU, h0, hV, hv, hbase, hψ, hmap, hsol, huniq⟩ :=
    actual_analytic_stationary_branch
  obtain ⟨hb, hdb⟩ := probabilityB_along_analytic_curve (hψ 0 h0) hbase
  have hd : deriv (fun k => probabilityB (k, ψ k)) 0 ≠ 0 := by
    rw [hdb.deriv]
    exact ne_of_gt beta_pos
  obtain ⟨κ, hκ, hk0, hleft, hright⟩ :=
    QuantumEmbedding.AnalyticFoundation.analytic_local_reparameterization hb hd
  have hb0 : probabilityB (0, ψ 0) = 0 := by
    simpa [hbase, basePoint] using probabilityB_base
  simp only [hb0] at hκ hk0 hright
  have hcurve : AnalyticAt ℝ (ψ ∘ κ) 0 := by
    apply AnalyticAt.comp
    · simpa [hk0] using hψ 0 h0
    · exact hκ
  have hcurveleft : ∀ᶠ k in 𝓝 0, (ψ ∘ κ) (probabilityB (k, ψ k)) = ψ k :=
    hleft.mono fun k hk => by simp [hk]
  exact ⟨ψ, U, V, κ, hU, h0, hV, hv, hbase, hψ, hmap, hsol, huniq,
    hdb, hκ, hk0, hcurve, hleft, hcurveleft, hright⟩

#print axioms systemDerivative_matrix
#print axioms systemDerivative_isInvertible
#print axioms stationarity_partial_isInvertible
#print axioms actual_analytic_stationary_branch
#print axioms zeroProbabilityB_eq
#print axioms zeroProbabilityB_hasFDerivAt_base
#print axioms probabilityB_base
#print axioms probabilityB_parameter_derivative
#print axioms probabilityB_scale_derivative
#print axioms probabilityB_derivative_apply
#print axioms probabilityB_along_analytic_curve
#print axioms actual_stationary_arc_reparameterized

end TwoStateQuantumEmbedding.ActualSwapSystem
