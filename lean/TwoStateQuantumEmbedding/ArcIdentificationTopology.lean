import TwoStateQuantumEmbedding.ActualSwapSystem
import Mathlib.Topology.Order.LeftRightNhds

noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace TwoStateQuantumEmbedding.GlobalSwapArc
open ActualSwapSystem

/-- 正侧最终性质给出单一正区间，量词覆盖该区间内全部参数。 -/
theorem eventually_positive_interval {P : ℝ → Prop}
    (hP : ∀ᶠ b in 𝓝[>] (0:ℝ), P b) :
    ∃ δ>0, ∀ b : ℝ, 0<b → b<δ → P b := by
  obtain ⟨δ,hδ,hall⟩ := (nhdsGT_basis (0:ℝ)).eventually_iff.mp hP
  exact ⟨δ,hδ,fun b hb hbδ => hall ⟨hb,hbδ⟩⟩

/-- 在零点解析确实给出双侧实开区间上的解析性。 -/
theorem analytic_symmetric_interval {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) :
    ∃ δ>0, AnalyticOnNhd ℝ f (Ioo (-δ) δ) := by
  obtain ⟨δ,hδ,hall⟩ := Metric.eventually_nhds_iff.mp hf.eventually_analyticAt
  refine ⟨δ,hδ,?_⟩
  intro b hb
  apply hall
  simpa only [Real.dist_eq, sub_zero, abs_lt, Set.mem_Ioo] using hb

/-- 固定 IFT 邻域的统一识别，适用于整族变化的真实极小参数。 -/
theorem eventual_branch_identification {ι : Type*} {F : Filter ι}
    (k : ι → ℝ) (y : ι → Parameters) (b : ι → ℝ)
    (hk : Tendsto k F (𝓝 0)) (hy : Tendsto y F (𝓝 baseParameters))
    (hG : ∀ᶠ i in F, stationarity (k i,y i)=0)
    (hB : ∀ᶠ i in F, probabilityB (k i,y i)=b i)
    (ψ : ℝ → Parameters) (κ : ℝ → ℝ) (U : Set ℝ) (V : Set Parameters)
    (hU : IsOpen U) (h0 : (0:ℝ)∈U) (hV : IsOpen V) (hv : baseParameters∈V)
    (huniq : ∀ k∈U, ∀ y∈V, stationarity (k,y)=0 ↔ ψ k=y)
    (hleft : ∀ᶠ k in 𝓝 (0:ℝ), κ (probabilityB (k,ψ k))=k) :
    ∀ᶠ i in F, probabilityA (k i,y i)=probabilityA (κ (b i),ψ (κ (b i))) := by
  have hku := hk.eventually (hU.mem_nhds h0)
  have hyv := hy.eventually (hV.mem_nhds hv)
  have hkl := hk.eventually hleft
  filter_upwards [hku,hyv,hG,hB,hkl] with i hki hyi hGi hBi hli
  have he := (huniq (k i) hki (y i) hyi).mp hGi
  have hbe : probabilityB (k i,ψ (k i))=b i := by rw [he]; exact hBi
  have hke : κ (b i)=k i := by rw [← hbe]; exact hli
  rw [hke,he]

/-- 实际 A 读出的反参数化沿双侧解析支路保持解析。 -/
theorem analytic_reparameterized_probabilityA (ψ : ℝ → Parameters) (κ : ℝ → ℝ)
    (hψ : AnalyticAt ℝ ψ 0)
    (hκ : AnalyticAt ℝ κ 0) (hκ0 : κ 0=0) :
    AnalyticAt ℝ (fun b => probabilityA (κ b,ψ (κ b))) 0 := by
  have hc : AnalyticAt ℝ (fun b => ψ (κ b)) 0 := by
    exact (hκ0 ▸ hψ).comp hκ
  exact (analytic_probabilityA _).comp (hκ.prod hc)

#print axioms eventual_branch_identification
#print axioms analytic_reparameterized_probabilityA
end TwoStateQuantumEmbedding.GlobalSwapArc

