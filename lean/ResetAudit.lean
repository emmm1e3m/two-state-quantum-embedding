import TwoStateQuantumEmbedding.ResetSharpLaws

open Filter
open scoped Topology
open TwoStateQuantumEmbedding

/-! 两个主定理直接展开到原始概率闭包的最大增益，排除隐藏的装配前提。 -/
example : Tendsto
    (fun ε : ℝ => Real.log (1 / ε) / ε * ResetEndpoint.resetGain ε)
    (𝓝[>] 0) (𝓝 (4 / Real.exp 1)) := by
  have h := ResetFinal.reset_sharp_law
  unfold ResetEndpoint.ResetLaw at h
  convert h using 1
  funext ε
  simp only [ResetEndpoint.scaledGain, ResetEndpoint.resetGain, pow_one]

example : Tendsto
    (fun ε : ℝ => Real.log (1 / ε) ^ 2 / ε * ResetEndpoint.diagonalResetGain ε)
    (𝓝[>] 0) (𝓝 (64 / Real.exp 1 ^ 2)) := by
  have h := ResetFinal.diagonal_reset_sharp_law
  unfold ResetEndpoint.DiagonalResetLaw at h
  convert h using 1
  funext ε
  rfl

#check ResetFinal.reset_sharp_law
#check ResetFinal.diagonal_reset_sharp_law
#check ResetFinal.actual_stationary_saturation
#check ResetDisplayedAsymptotics.displayed_finite_matching
#check ResetDiagonalFamily.every_small_actual_error_unit

#print axioms ResetFinal.reset_sharp_law
#print axioms ResetFinal.diagonal_reset_sharp_law
#print axioms ResetFinal.actual_stationary_saturation
#print axioms ResetDisplayedAsymptotics.displayed_finite_matching
#print axioms ResetDiagonalFamily.every_small_actual_error_unit
