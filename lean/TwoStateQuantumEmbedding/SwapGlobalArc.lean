import TwoStateQuantumEmbedding.MinimizerCoordinates
import TwoStateQuantumEmbedding.ArcIdentificationTopology
import TwoStateQuantumEmbedding.SwapAnalyticBranch

noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace TwoStateQuantumEmbedding.GlobalSwapArc
open ActualSwapSystem GKSLAlgebra
set_option maxHeartbeats 1000000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false

/-- 任意已证实际唯一支路及真实局部逆，都与同一个原始下边界最终相同。 -/
theorem lowerBoundary_eq_stationary_arc
    (ψ : ℝ → ActualSwapSystem.Parameters) (κ : ℝ → ℝ)
    (U : Set ℝ) (V : Set ActualSwapSystem.Parameters)
    (hU : IsOpen U) (h0 : (0:ℝ)∈U) (hV : IsOpen V) (hv : baseParameters∈V)
    (huniq : ∀ k∈U, ∀ y∈V, stationarity (k,y)=0 ↔ ψ k=y)
    (hleft : ∀ᶠ k in 𝓝 (0:ℝ), κ (probabilityB (k,ψ k))=k) :
    ∀ᶠ b in 𝓝[>] (0:ℝ), probabilityA (κ b,ψ (κ b))=lowerBoundary b := by
  let H : ℝ → BlochVec := fun b => (selectedMinimizer b).1
  let K : ℝ → KMatrix := fun b => (selectedMinimizer b).2
  let k : ℝ → ℝ := fun b => minimizingScale (H b) (K b)
  let y : ℝ → ActualSwapSystem.Parameters := fun b => minimizingParameters (H b) (K b)
  have hb : Tendsto (id : ℝ → ℝ) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hm := selectedMinimizer_eventually
  have hk : Tendsto k (𝓝[>] (0:ℝ)) (𝓝 0) :=
    minimizing_scale_tendsto H K id hb hm
  have hy : Tendsto y (𝓝[>] (0:ℝ)) (𝓝 baseParameters) :=
    minimizing_parameters_tendsto H K id hb hm
  have hG : ∀ᶠ b in 𝓝[>] (0:ℝ), stationarity (k b,y b)=0 :=
    minimizing_stationarity_eventually H K id hb hm
  have hread : ∀ᶠ b in 𝓝[>] (0:ℝ),
      (probabilityA (k b,y b),probabilityB (k b,y b))=(lowerBoundary b,b) :=
    minimizing_probabilities_eventually H K id hb hm
  have hB : ∀ᶠ b in 𝓝[>] (0:ℝ), probabilityB (k b,y b)=b :=
    hread.mono fun b hb => congrArg Prod.snd hb
  have hid := eventual_branch_identification k y id hk hy hG hB ψ κ U V hU h0 hV hv huniq hleft
  filter_upwards [hid,hread] with b hbi hri
  exact hbi.symm.trans (congrArg Prod.fst hri)

theorem probabilityA_base_zero : probabilityA basePoint=0 := by
  have he := congrArg Prod.fst (probability_eq_canonical basePoint)
  simpa [basePoint, baseParameters, ActualSwapSystem.hamiltonianVector,
    kossakowskiMatrix, canonicalOutput_x_zero] using he

/-- B11：原始 Q2 的真实下边界在同一正区间上有双侧实解析延拓。 -/
theorem lowerBoundary_analytic_near_swap :
    ∃ (farc : ℝ → ℝ) (b0 : ℝ), 0<b0 ∧
      AnalyticOnNhd ℝ farc (Ioo (-b0) b0) ∧
      ∀ b∈Ico (0:ℝ) b0, farc b=lowerBoundary b := by
  obtain ⟨ψ,U,V,κ,hU,h0,hV,hv,hbase,hψ,hmap,hsol,huniq,
      hdb,hκ,hκ0,hcurve,hleft,hleftCurve,hright⟩ := actual_stationary_arc_reparameterized
  let farc : ℝ → ℝ := fun b => probabilityA (κ b,ψ (κ b))
  have hfar : AnalyticAt ℝ farc 0 :=
    analytic_reparameterized_probabilityA ψ κ (hψ 0 h0) hκ hκ0
  have heq : ∀ᶠ b in 𝓝[>] (0:ℝ), farc b=lowerBoundary b :=
    lowerBoundary_eq_stationary_arc ψ κ U V hU h0 hV hv huniq hleft
  have hf0 : farc 0=0 := by
    dsimp [farc]
    rw [hκ0,hbase]
    exact probabilityA_base_zero
  obtain ⟨δa,hδa,ha⟩ := analytic_symmetric_interval hfar
  obtain ⟨δe,hδe,he⟩ := eventually_positive_interval heq
  refine ⟨farc,min δa δe,lt_min hδa hδe,?_,?_⟩
  · intro b hb
    apply ha b
    exact ⟨lt_of_le_of_lt (neg_le_neg (min_le_left δa δe)) hb.1,
      hb.2.trans_le (min_le_left δa δe)⟩
  · intro b hb
    by_cases hb0 : b=0
    · simpa only [hb0,lowerBoundary_zero] using hf0
    · exact he b (lt_of_le_of_ne hb.1 (Ne.symm hb0))
        (hb.2.trans_le (min_le_right δa δe))

#print axioms lowerBoundary_eq_stationary_arc
#print axioms probabilityA_base_zero
#print axioms lowerBoundary_analytic_near_swap
end TwoStateQuantumEmbedding.GlobalSwapArc
