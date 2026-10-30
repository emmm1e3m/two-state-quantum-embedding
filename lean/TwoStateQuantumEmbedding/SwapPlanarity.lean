import TwoStateQuantumEmbedding.SwapReflection
import TwoStateQuantumEmbedding.SwapAnalyticBranch

/-! 从实际七变量系统的固定邻域唯一性推出精确平面性。 -/
noncomputable section
open Set Filter
open scoped Topology

namespace TwoStateQuantumEmbedding.ActualSwapSystem

set_option maxRecDepth 3000
set_option maxHeartbeats 1200000

def Planar (y : Parameters) : Prop := y 1 = 0 ∧ y 3 = 0 ∧ y 6 = 0

theorem planar_of_reflection_fixed (y : Parameters) (hy : reflectParameters y = y) : Planar y := by
  have h1 := congrArg (fun v : Parameters => v 1) hy
  have h3 := congrArg (fun v : Parameters => v 3) hy
  have h6 := congrArg (fun v : Parameters => v 6) hy
  norm_num [reflectionSigns] at h1 h3 h6
  exact ⟨by linarith, by linarith, by linarith⟩

def reflectedNeighborhood (V : Set Parameters) : Set Parameters :=
  V ∩ reflectParameters ⁻¹' V

theorem reflectedNeighborhood_open {V : Set Parameters} (hV : IsOpen V) :
    IsOpen (reflectedNeighborhood V) := hV.inter (hV.preimage reflectParameters.continuous)

theorem reflectedNeighborhood_base {V : Set Parameters} (hv : baseParameters ∈ V) :
    baseParameters ∈ reflectedNeighborhood V := by
  exact ⟨hv, by simpa using hv⟩

theorem reflectedNeighborhood_invariant (V : Set Parameters) :
    MapsTo reflectParameters (reflectedNeighborhood V) (reflectedNeighborhood V) := by
  intro y hy
  exact ⟨hy.2, by simpa using hy.1⟩

/-- 此接口可用于 080 的任一固定邻域唯一支路，保留该支路本身不变。 -/
theorem unique_stationary_branch_eventually_planar
    {ψ : ℝ → Parameters} {U : Set ℝ} {V : Set Parameters}
    (hU : IsOpen U) (h0 : (0 : ℝ) ∈ U) (hV : IsOpen V) (hv : baseParameters ∈ V)
    (hbase : ψ 0 = baseParameters) (hcont : ContinuousAt ψ 0)
    (hsol : ∀ k ∈ U, stationarity (k, ψ k) = 0)
    (huniq : ∀ k ∈ U, ∀ y ∈ V, stationarity (k, y) = 0 ↔ ψ k = y) :
    ∀ᶠ k in 𝓝 (0 : ℝ), Planar (ψ k) := by
  have hc : ContinuousAt (fun k => reflectParameters (ψ k)) 0 :=
    reflectParameters.continuous.continuousAt.comp hcont
  have hb : reflectParameters (ψ 0) ∈ V := by simpa [hbase] using hv
  have hm := hc.tendsto.eventually (hV.mem_nhds hb)
  filter_upwards [hU.mem_nhds h0, hm] with k hk hr
  have hs : stationarity (k, reflectParameters (ψ k)) = 0 :=
    (stationarity_reflect_zero_iff (k, ψ k)).mpr (hsol k hk)
  exact planar_of_reflection_fixed (ψ k) ((huniq k hk _ hr).mp hs).symm

/-- 精确平面性也给出 B12 所需三个坐标的一阶导数严格为零。 -/
theorem planar_curve_derivative_zero {ψ : ℝ → Parameters}
    (hp : ∀ᶠ k in 𝓝 (0 : ℝ), Planar (ψ k)) :
    deriv (fun k => ψ k 1) 0 = 0 ∧ deriv (fun k => ψ k 3) 0 = 0 ∧
      deriv (fun k => ψ k 6) 0 = 0 := by
  have h1 : (fun k => ψ k 1) =ᶠ[𝓝 (0 : ℝ)] (fun _ => 0) := hp.mono fun _ h => h.1
  have h3 : (fun k => ψ k 3) =ᶠ[𝓝 (0 : ℝ)] (fun _ => 0) := hp.mono fun _ h => h.2.1
  have h6 : (fun k => ψ k 6) =ᶠ[𝓝 (0 : ℝ)] (fun _ => 0) := hp.mono fun _ h => h.2.2
  exact ⟨by simpa using h1.deriv_eq, by simpa using h3.deriv_eq, by simpa using h6.deriv_eq⟩

/-- 真正的解析分支存在，并可在一个固定反射不变邻域内保持唯一且精确平面。 -/
theorem actual_planar_analytic_stationary_branch :
    ∃ (ψ : ℝ → Parameters) (U : Set ℝ) (V : Set Parameters),
      IsOpen U ∧ (0 : ℝ) ∈ U ∧ IsOpen V ∧ baseParameters ∈ V ∧
      ψ 0 = baseParameters ∧ AnalyticOnNhd ℝ ψ U ∧ MapsTo ψ U V ∧
      MapsTo reflectParameters V V ∧
      (∀ k ∈ U, stationarity (k, ψ k) = 0) ∧
      (∀ k ∈ U, ∀ y ∈ V, stationarity (k, y) = 0 ↔ ψ k = y) ∧
      (∀ k ∈ U, Planar (ψ k)) := by
  obtain ⟨ψ, U, V, hU, h0, hV, hv, hbase, hψ, _, hsol, huniq⟩ :=
    actual_analytic_stationary_branch
  let W := reflectedNeighborhood V
  have hW : IsOpen W := reflectedNeighborhood_open hV
  have hwb : baseParameters ∈ W := reflectedNeighborhood_base hv
  have hpre : ψ ⁻¹' W ∈ 𝓝 (0 : ℝ) :=
    (hψ 0 h0).continuousAt.preimage_mem_nhds (by simpa [hbase] using hW.mem_nhds hwb)
  obtain ⟨U', hU'sub, hU', h0'⟩ := mem_nhds_iff.mp (inter_mem (hU.mem_nhds h0) hpre)
  have hsub : U' ⊆ U := fun k hk => (hU'sub hk).1
  have hmap : MapsTo ψ U' W := fun k hk => (hU'sub hk).2
  refine ⟨ψ, U', W, hU', h0', hW, hwb, hbase, hψ.mono hsub, hmap,
    reflectedNeighborhood_invariant V, ?_, ?_, ?_⟩
  · exact fun k hk => hsol k (hsub hk)
  · exact fun k hk y hy => huniq k (hsub hk) y hy.1
  · intro k hk
    have hr : reflectParameters (ψ k) ∈ V := (hmap hk).2
    have hs : stationarity (k, reflectParameters (ψ k)) = 0 :=
      (stationarity_reflect_zero_iff (k, ψ k)).mpr (hsol k (hsub hk))
    exact planar_of_reflection_fixed (ψ k) ((huniq k (hsub hk) _ hr).mp hs).symm

#print axioms unique_stationary_branch_eventually_planar
#print axioms planar_curve_derivative_zero
#print axioms actual_planar_analytic_stationary_branch

end TwoStateQuantumEmbedding.ActualSwapSystem
