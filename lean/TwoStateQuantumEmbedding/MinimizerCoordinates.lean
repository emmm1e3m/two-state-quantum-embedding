import TwoStateQuantumEmbedding.CanonicalStationarity
import TwoStateQuantumEmbedding.SwapFiniteAttainment
import TwoStateQuantumEmbedding.SwapRankOneNeighborhood
import TwoStateQuantumEmbedding.RankOneChart

noncomputable section
open Matrix Filter Set
open scoped Topology ComplexOrder Matrix.Norms.Operator
namespace TwoStateQuantumEmbedding.GlobalSwapArc
open GKSLAlgebra CanonicalBloch GKSLBounds CanonicalGradient SwapFiniteAttainment
set_option maxHeartbeats 1600000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false

abbrev KMatrix := Matrix (Fin 3) (Fin 3) ℂ

def normalizedData (h : BlochVec) (K : KMatrix) : SwapRankOne.NormalizedParameters :=
  ((NearSwap.gaugeHamiltonian h, NearSwap.gaugeNoise h K),
    NearSwap.normalizedNoise (NearSwap.gaugeNoise h K))

def minimizingScale (h : BlochVec) (K : KMatrix) : ℝ :=
  RankOneChart.scale (NearSwap.gaugeNoise h K)

def minimizingParameters (h : BlochVec) (K : KMatrix) : ActualSwapSystem.Parameters :=
  RankOneChart.parameters ((NearSwap.gaugeHamiltonian h) 0)
    ((NearSwap.gaugeHamiltonian h) 2/2) (SwapRankOne.multiplier (normalizedData h K))
    (RankOneChart.chart (NearSwap.gaugeNoise h K))

theorem referenceProjector_eq_referenceW :
    RankOneChart.referenceProjector=SwapRankOne.referenceW :=
  SwapRankOne.referenceW_eq_normalized.symm

theorem kernelProjector_eq_referenceW : NearSwap.kernelProjector=SwapRankOne.referenceW :=
  NearSwap.kernelProjector_eq_outer.trans SwapRankOne.referenceW_eq_outer.symm

theorem normalizedNoise_eq_real_smul (K : KMatrix) :
    NearSwap.normalizedNoise K=(dissipationSize K)⁻¹ • K := by
  ext i j
  simp [NearSwap.normalizedNoise, Matrix.smul_apply, Complex.real_smul]

/-- 真实下边界的每个达到点自动满足固定 Hamiltonian 的 PSD 局部极小条件。 -/
theorem localMinimum_of_swapMinimizer {h : BlochVec} {K : KMatrix} {b : ℝ}
    (hm : IsSwapMinimizer h K b) :
    IsLocalMinOn (fun W => (canonicalOutput h W 1).1)
      {W | W.PosSemidef ∧ (canonicalOutput h W 1).2=(canonicalOutput h K 1).2} K := by
  have hb : b∈Icc (0:ℝ) 1 := by
    have hmem := canonicalOutput_mem_Q2 h K hm.1 1 (by norm_num)
    rw [hm.2] at hmem
    exact (Q2_subset_unitSquare hmem).2
  filter_upwards [self_mem_nhdsWithin] with W hW
  have hwb : (canonicalOutput h W 1).2=b := by simpa only [hm.2] using hW.2
  have hmem := canonicalOutput_mem_Q2 h W hW.1 1 (by norm_num)
  have hmem' : ((canonicalOutput h W 1).1,b)∈Q2 := by
    simpa only [← hwb, Prod.mk.eta] using hmem
  simpa only [hm.2, Prod.fst] using lowerBoundary_le_of_mem hb hmem'

theorem gauge_swapMinimizer {h : BlochVec} {K : KMatrix} {b : ℝ}
    (hm : IsSwapMinimizer h K b) :
    IsSwapMinimizer (NearSwap.gaugeHamiltonian h) (NearSwap.gaugeNoise h K) b :=
  ⟨NearSwap.gaugeNoise_posSemidef h K hm.1,
    (NearSwap.gaugeOutput_eq h K hm.1.isHermitian 1).trans hm.2⟩

section UniformFamily
variable {ι : Type*} {F : Filter ι}
variable (h : ι → BlochVec) (K : ι → KMatrix) (b : ι → ℝ)
variable (hb : Tendsto b F (𝓝 0))
variable (hmin : ∀ᶠ i in F, 0<b i ∧ b i<smallRadius ∧ IsSwapMinimizer (h i) (K i) (b i))
include hb hmin

/-- 对任意变化的极小元族的统一归一化收敛，不固定某个生成元。 -/
theorem minimizing_normalized_tendsto :
    Tendsto (fun i => normalizedData (h i) (K i)) F (𝓝 SwapRankOne.referenceNormalized) := by
  have hlegal : ∀ᶠ i in F, (K i).PosSemidef := hmin.mono fun i hi => hi.2.2.1
  have hbpos : ∀ᶠ i in F, 0<(canonicalOutput (h i) (K i) 1).2 := by
    filter_upwards [hmin] with i hi
    simpa only [hi.2.2.2] using hi.1
  have hbe : (fun i => (canonicalOutput (h i) (K i) 1).2)=ᶠ[F] b := by
    filter_upwards [hmin] with i hi
    exact congrArg Prod.snd hi.2.2.2
  have hbout := hb.congr' hbe.symm
  have hnear : ∀ᶠ i in F, (canonicalOutput (h i) (K i) 1).1≤
      Swap.slope*(canonicalOutput (h i) (K i) 1).2+
        41*(canonicalOutput (h i) (K i) 1).2^2 := by
    filter_upwards [hmin] with i hi
    rw [hi.2.2.2]
    have hu := SwapMatching.lowerBoundary_small_upper hi.1
      (hi.2.1.le.trans (min_le_right _ _))
    dsimp
    nlinarith [sq_nonneg (b i)]
  have hc := NearSwap.canonical_normalized_parameters_tendsto F 41 (by norm_num)
    h K hlegal hbpos hbout hnear
  simpa only [normalizedData, SwapRankOne.referenceNormalized, SwapRankOne.referenceParameters,
    SwapRankOne.referenceH, kernelProjector_eq_referenceW] using hc

omit hb in
theorem minimizing_dissipation_eventually_pos :
    ∀ᶠ i in F, 0<dissipationSize (NearSwap.gaugeNoise (h i) (K i)) := by
  filter_upwards [hmin] with i hi
  have hl := all_minimizers_localized hi.1 hi.2.1 hi.2.2
  linarith [hl.dissipation_lower]

/-- 固定真实邻域与 PSD 极小条件强制全部最终极小元精确秩一。 -/
theorem minimizing_rank_one_eventually :
    ∀ᶠ i in F,
      0<kDerivative (1/2) (-1/2)
        (NearSwap.gaugeHamiltonian (h i),NearSwap.gaugeNoise (h i) (K i))
        (NearSwap.gaugeNoise (h i) (K i)) ∧
      (NearSwap.gaugeNoise (h i) (K i)).rank=1 := by
  have hc := minimizing_normalized_tendsto h K b hb hmin
  have hd := minimizing_dissipation_eventually_pos h K b hmin
  have hr := SwapRankOne.eventually_rank_one_of_tendsto
    (fun i => normalizedData (h i) (K i))
    (fun i => dissipationSize (NearSwap.gaugeNoise (h i) (K i))) hc ?_
  · exact hr.mono fun i hi => ⟨hi.1,hi.2.2.2⟩
  filter_upwards [hmin,hd] with i hi hdi
  have hm := gauge_swapMinimizer hi.2.2
  exact ⟨hdi, NearSwap.normalizedNoise_rescale _ hdi,hm.1,localMinimum_of_swapMinimizer hm⟩

theorem minimizing_scale_tendsto :
    Tendsto (fun i => minimizingScale (h i) (K i)) F (𝓝 0) := by
  have hc := minimizing_normalized_tendsto h K b hb hmin
  have hK0 := hc.fst_nhds.snd_nhds
  have ht := RankOneChart.scale_continuous.continuousAt.tendsto.comp hK0
  simpa only [Function.comp_def, minimizingScale, normalizedData, SwapRankOne.referenceNormalized,
    SwapRankOne.referenceParameters, RankOneChart.scale, Matrix.zero_apply, Complex.zero_re] using ht

theorem minimizing_scale_eventually_pos :
    ∀ᶠ i in F, 0<minimizingScale (h i) (K i) := by
  have hc := minimizing_normalized_tendsto h K b hb hmin
  have hW : Tendsto (fun i => (dissipationSize (NearSwap.gaugeNoise (h i) (K i)))⁻¹ •
      NearSwap.gaugeNoise (h i) (K i)) F (𝓝 RankOneChart.referenceProjector) := by
    simpa only [normalizedData, SwapRankOne.referenceNormalized,
      ← referenceProjector_eq_referenceW, normalizedNoise_eq_real_smul] using hc.snd_nhds
  exact RankOneChart.eventually_scale_pos_of_normalized _ _
    (minimizing_dissipation_eventually_pos h K b hmin) hW

theorem minimizing_parameters_tendsto :
    Tendsto (fun i => minimizingParameters (h i) (K i)) F (𝓝 ActualSwapSystem.baseParameters) := by
  have hc := minimizing_normalized_tendsto h K b hb hmin
  have hH := hc.fst_nhds.fst_nhds
  have hM := SwapRankOne.multiplier_tendsto_slope _ hc
  have hW : Tendsto (fun i => (dissipationSize (NearSwap.gaugeNoise (h i) (K i)))⁻¹ •
      NearSwap.gaugeNoise (h i) (K i)) F (𝓝 RankOneChart.referenceProjector) := by
    simpa only [normalizedData, SwapRankOne.referenceNormalized,
      ← referenceProjector_eq_referenceW, normalizedNoise_eq_real_smul] using hc.snd_nhds
  have hU := RankOneChart.chart_tendsto_of_normalized _ _
    (minimizing_dissipation_eventually_pos h K b hmin) hW
  have hcont : Continuous (fun z : BlochVec × (ℝ × RankOneChart.Directions) =>
      RankOneChart.parameters (z.1 0) (z.1 2/2) z.2.1 z.2.2) := by
    unfold RankOneChart.parameters
    fun_prop
  have hh := hcont.continuousAt.tendsto.comp (hH.prodMk_nhds (hM.prodMk_nhds hU))
  simpa [minimizingParameters, normalizedData, SwapRankOne.referenceNormalized,
    SwapRankOne.referenceParameters, SwapRankOne.referenceH, RankOneChart.parameters,
    RankOneChart.referenceDirections, ActualSwapSystem.baseParameters, Function.comp_def] using hh

/-- 同一个实际完整复坐标图精确读出真实下边界值。 -/
theorem minimizing_probabilities_eventually :
    ∀ᶠ i in F,
      (ActualSwapSystem.probabilityA (minimizingScale (h i) (K i),minimizingParameters (h i) (K i)),
        ActualSwapSystem.probabilityB (minimizingScale (h i) (K i),minimizingParameters (h i) (K i))) =
      (lowerBoundary (b i),b i) := by
  have hr := minimizing_rank_one_eventually h K b hb hmin
  have hk := minimizing_scale_eventually_pos h K b hb hmin
  filter_upwards [hmin,hr,hk] with i hi hri hki
  have hm := gauge_swapMinimizer hi.2.2
  have hp := RankOneChart.actualProbabilities_chart _ hm.1 hri.2 hki
    ((NearSwap.gaugeHamiltonian (h i)) 0) ((NearSwap.gaugeHamiltonian (h i)) 2/2)
    (SwapRankOne.multiplier (normalizedData (h i) (K i)))
  have hh : (![(NearSwap.gaugeHamiltonian (h i)) 0,0,
      2*((NearSwap.gaugeHamiltonian (h i)) 2/2)] : BlochVec)=NearSwap.gaugeHamiltonian (h i) := by
    ext j
    fin_cases j <;> simp [NearSwap.gaugeHamiltonian]
    ring
  rw [hh] at hp
  exact hp.trans hm.2

/-- 真正全局极小、实际径向非零和完整复坐标图推出全部七个方程。 -/
theorem minimizing_stationarity_eventually :
    ∀ᶠ i in F, ActualSwapSystem.stationarity
      (minimizingScale (h i) (K i),minimizingParameters (h i) (K i))=0 := by
  have hr := minimizing_rank_one_eventually h K b hb hmin
  have hk := minimizing_scale_eventually_pos h K b hb hmin
  have hd := minimizing_dissipation_eventually_pos h K b hmin
  filter_upwards [hmin,hr,hk,hd] with i hi hri hki hdi
  have hm := gauge_swapMinimizer hi.2.2
  have hμ := SwapRankOne.actual_multiplier_of_scale (normalizedData (h i) (K i)) hdi.ne'
    (NearSwap.normalizedNoise_rescale _ hdi)
  change CanonicalStationarity.multiplier (NearSwap.gaugeHamiltonian (h i))
    (NearSwap.gaugeNoise (h i) (K i))=SwapRankOne.multiplier (normalizedData (h i) (K i)) at hμ
  have hG := ActualSwapOptimality.stationarity_chart_of_lowerBoundary
    (NearSwap.gaugeHamiltonian (h i)) (NearSwap.gaugeNoise (h i) (K i))
    (by rfl) hm.1 hri.2 hki hri.1.ne' (b i) hm.2
  simpa only [minimizingScale,minimizingParameters,hμ] using hG
end UniformFamily

/-- 对每个 b 从真实有限极小元集合选取，范围外的值不参与后续论证。 -/
def selectedMinimizer (b : ℝ) : BlochVec × KMatrix :=
  Classical.epsilon (fun p => IsSwapMinimizer p.1 p.2 b)

theorem selectedMinimizer_spec {b : ℝ} (hb : 0<b) (hs : b<smallRadius) :
    IsSwapMinimizer (selectedMinimizer b).1 (selectedMinimizer b).2 b := by
  have he : ∃ p : BlochVec × KMatrix, IsSwapMinimizer p.1 p.2 b := by
    obtain ⟨h,K,hm⟩ := exists_swapMinimizer hb hs
    exact ⟨(h,K),hm⟩
  simpa only [selectedMinimizer] using Classical.epsilon_spec he

theorem selectedMinimizer_eventually :
    ∀ᶠ b in 𝓝[>] (0:ℝ), 0<b ∧ b<smallRadius ∧
      IsSwapMinimizer (selectedMinimizer b).1 (selectedMinimizer b).2 b := by
  have hs : ∀ᶠ b in 𝓝[>] (0:ℝ), b<smallRadius :=
    (gt_mem_nhds smallRadius_pos).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,hs] with b hb hs
  exact ⟨hb,hs,selectedMinimizer_spec hb hs⟩

#print axioms minimizing_normalized_tendsto
#print axioms minimizing_rank_one_eventually
#print axioms minimizing_parameters_tendsto
#print axioms minimizing_probabilities_eventually
#print axioms minimizing_stationarity_eventually
#print axioms selectedMinimizer_eventually
end TwoStateQuantumEmbedding.GlobalSwapArc

