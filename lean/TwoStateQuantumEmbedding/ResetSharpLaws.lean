import TwoStateQuantumEmbedding.ResetActualSharpBounds
import TwoStateQuantumEmbedding.ResetSaturationBridge
import TwoStateQuantumEmbedding.ResetDiagonalActual
import TwoStateQuantumEmbedding.ResetEnvelopeUniform
import TwoStateQuantumEmbedding.ResetDisplayedAsymptotics
import TwoStateQuantumEmbedding.ResetEndpointTolerance

noncomputable section
open Set Filter Matrix Complex
open scoped Topology ComplexOrder

namespace TwoStateQuantumEmbedding.ResetFinal
open ResetEndpoint ResetActual PureStationary

theorem refined_envelope_exact : ∀ η : ℝ, 0 < η → ∃ δ > 0,
    ∀ ρ p ν A B : ℝ, 0 < ρ → ρ < δ → 0 ≤ p → 0 ≤ ν → p+ν ≤ ρ →
      0 ≤ A → 0 ≤ B → Real.log (1/ρ)*ResetEnvelope.envelope p ν A B ≤
        (4/Real.exp 1)*p+η*ρ := by
  simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using
    ResetEnvelope.refined_envelope_uniform

/-- K016下界直接使用论文显示的同一个有限单跳跃族。 -/
theorem displayed_actual_finite_lower (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ ε ∈ Ioo (0 : ℝ) δ, ∃ a : ℝ,
      (a,1-ε) ∈ finiteOutputs ∧
        4/Real.exp 1-η ≤ Real.log (1/ε)/ε*(ε-a) := by
  obtain ⟨δ,hδ,hcover⟩ := ResetDisplayedAsymptotics.displayed_finite_matching η hη
  refine ⟨δ,hδ,?_⟩
  intro ε hε
  obtain ⟨L,a,hL,he,hout,ha,hclose⟩ := hcover ε hε
  refine ⟨a,ha,?_⟩
  have hl := (abs_lt.mp hclose).1
  linarith

/-- K016：全部原始有限GKSL输出的概率闭包在固定实际误差下的无条件尖锐律。 -/
theorem reset_sharp_law : ResetLaw :=
  resetLaw_of_tolerance_bounds
    (actual_finite_upper_of_refined_envelope refined_envelope_exact)
    displayed_actual_finite_lower

/-- K016饱和序列的任意稳态选择都满足谱预算分配、相干与纯度必要条件。 -/
theorem actual_stationary_saturation
    (N : ℕ → ℕ) (H : ℕ → QubitMatrix) (J : ∀ n, Fin (N n) → QubitMatrix)
    (t : ℕ → ℝ) (ρ : ℕ → QubitMatrix)
    (hH : ∀ n, (H n).IsHermitian) (ht : ∀ n, 0 ≤ t n)
    (hρ : ∀ n, (ρ n).PosSemidef ∧ (ρ n).trace=1 ∧ gkslAction (H n) (J n) (ρ n)=0)
    (hε : Tendsto (fun n => outputError (finiteOutput (H n) (J n) (t n)))
      atTop (𝓝[>] (0 : ℝ)))
    (hsat : Tendsto (fun n =>
      Real.log (1/outputError (finiteOutput (H n) (J n) (t n))) /
        outputError (finiteOutput (H n) (J n) (t n)) *
          outputGain (finiteOutput (H n) (J n) (t n))) atTop (𝓝 (4/Real.exp 1))) :
    ∃ (ν p : ℕ → ℝ) (U : ℕ → QubitMatrix),
      (∀ᶠ n in atTop, 0 ≤ ν n ∧ ν n < 1/2 ∧ 0 ≤ p n ∧ p n < 1/2 ∧
        (U n)ᴴ*U n=1 ∧ U n*(U n)ᴴ=1 ∧
        ρ n=conjugate (U n) (ResetMixed.state 1 (ν n) 0) ∧
        p n=normSq (U n 0 1)) ∧
      Tendsto (fun n => p n/outputError (finiteOutput (H n) (J n) (t n))) atTop (𝓝 1) ∧
      Tendsto (fun n => ν n/outputError (finiteOutput (H n) (J n) (t n))) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖ρ n 0 1‖^2/outputError (finiteOutput (H n) (J n) (t n)))
        atTop (𝓝 1) ∧
      Tendsto (fun n => (1-(ρ n*ρ n).trace.re) /
        outputError (finiteOutput (H n) (J n) (t n))) atTop (𝓝 0) :=
  actual_stationary_saturation_of_refined_envelope refined_envelope_exact
    N H J t ρ hH ht hρ hε hsat

#check reset_sharp_law
#check diagonal_reset_sharp_law
#check actual_stationary_saturation
#print axioms reset_sharp_law
#print axioms displayed_actual_finite_lower
#print axioms diagonal_reset_sharp_law
#print axioms actual_stationary_saturation
end TwoStateQuantumEmbedding.ResetFinal
