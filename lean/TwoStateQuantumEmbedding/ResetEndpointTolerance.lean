import TwoStateQuantumEmbedding.ResetEndpoint

noncomputable section
open Set Filter Matrix
open scoped Topology

namespace TwoStateQuantumEmbedding.ResetEndpoint

/-- 两个重置尺度共用的归一化因子。 -/
def logarithmicScale (k : ℕ) (ε : ℝ) : ℝ := Real.log (1 / ε) ^ k / ε

theorem logarithmicScale_pos (k : ℕ) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) :
    0 < logarithmicScale k ε := by
  have hdiv : 1 < 1 / ε := (lt_div_iff₀ hε.1).mpr (by simpa using hε.2)
  exact div_pos (pow_pos (Real.log_pos hdiv) _) hε.1

theorem logarithmicScale_continuousAt (k : ℕ) {ε : ℝ} (hε : ε ≠ 0) :
    ContinuousAt (logarithmicScale k) ε := by
  unfold logarithmicScale
  exact (((continuousAt_const.div continuousAt_id hε).log (one_div_ne_zero hε)).pow k).div
    continuousAt_id hε

/-- 容差常数形式的归一化有限输出界，直接传递至概率闭包。
只在正 ε 处使用显式归一化因子的连续性，不要求连续余项。 -/
theorem scaled_output_bound_on_closure
    {S : Set (ℝ × ℝ)} (k : ℕ) {D δ : ℝ} (hδ : δ ≤ 1)
    (hfinite : ∀ ε ∈ Ioo (0 : ℝ) δ, ∀ a : ℝ, (a, 1 - ε) ∈ S →
      Real.log (1 / ε) ^ k / ε * (ε - a) ≤ D)
    {a ε : ℝ} (hp : (a, 1 - ε) ∈ closure S) (hε : ε ∈ Ioo (0 : ℝ) δ) :
    Real.log (1 / ε) ^ k / ε * (ε - a) ≤ D := by
  have hsmall {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) δ) : x ∈ Ioo (0 : ℝ) 1 :=
    ⟨hx.1, hx.2.trans_le hδ⟩
  have hc : ContinuousOn (fun x : ℝ => D / logarithmicScale k x) (Ioo 0 δ) := by
    intro x hx
    exact (continuousAt_const.div (logarithmicScale_continuousAt k hx.1.ne')
      (logarithmicScale_pos k (hsmall hx)).ne').continuousWithinAt
  have hu : ε - a ≤ D / logarithmicScale k ε :=
    output_bound_on_closure hc (by
      intro p hp hp0 hpδ
      apply (le_div_iff₀ (logarithmicScale_pos k (hsmall ⟨hp0, hpδ⟩))).mpr
      have hb := hfinite (1 - p.2) ⟨hp0, hpδ⟩ p.1 (by simpa using hp)
      simpa only [logarithmicScale, mul_comm] using hb) hp hε
  have hb := (le_div_iff₀ (logarithmicScale_pos k (hsmall hε))).mp hu
  simpa only [logarithmicScale, mul_comm] using hb

/-- 每个容差统一控制全部有限输出，且每个小实际误差有匹配见证，
即可得到闭包真实最大增益的极限；不选择全域见证函数。 -/
theorem scaledGain_closure_tendsto_of_tolerance_bounds
    {S : Set (ℝ × ℝ)} (hS : S ⊆ Q2) (k : ℕ) (C : ℝ)
    (hupper : ∀ η : ℝ, 0 < η → ∃ δ > 0, ∀ ε ∈ Ioo (0 : ℝ) δ,
      ∀ a : ℝ, (a, 1 - ε) ∈ S →
        Real.log (1 / ε) ^ k / ε * (ε - a) ≤ C + η)
    (hlower : ∀ η : ℝ, 0 < η → ∃ δ > 0, ∀ ε ∈ Ioo (0 : ℝ) δ,
      ∃ a : ℝ, (a, 1 - ε) ∈ S ∧
        C - η ≤ Real.log (1 / ε) ^ k / ε * (ε - a)) :
    Tendsto (scaledGain k (closure S)) (𝓝[>] 0) (𝓝 C) := by
  have hclosure : closure S ⊆ Q2 := closure_minimal hS Q2_isClosed
  apply tendsto_order.mpr
  constructor
  · intro c hc
    let η : ℝ := (C - c) / 2
    have hη : 0 < η := by dsimp [η]; linarith
    obtain ⟨δ, hδ, hl⟩ := hlower η hη
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        nhdsWithin_le_nhds] with ε hε hεδ hε1
    obtain ⟨a, hp, hlo⟩ := hl ε ⟨hε, hεδ⟩
    have hscale := (logarithmicScale_pos k ⟨hε, hε1⟩).le
    have hgain := mul_le_mul_of_nonneg_left
      (output_gain_le hclosure (subset_closure hp)) hscale
    change logarithmicScale k ε * (ε - a) ≤ scaledGain k (closure S) ε at hgain
    have hclt : c < C - η := by dsimp [η]; linarith
    exact hclt.trans_le (hlo.trans hgain)
  · intro c hc
    let η : ℝ := (c - C) / 2
    have hη : 0 < η := by dsimp [η]; linarith
    obtain ⟨δu, hδu, hu⟩ := hupper η hη
    obtain ⟨δl, hδl, hl⟩ := hlower 1 (by norm_num)
    let δ : ℝ := min δu 1
    have hδ : 0 < δ := lt_min hδu (by norm_num)
    have hδ1 : δ ≤ 1 := min_le_right _ _
    have hu' : ∀ ε ∈ Ioo (0 : ℝ) δ, ∀ a : ℝ, (a, 1 - ε) ∈ S →
        Real.log (1 / ε) ^ k / ε * (ε - a) ≤ C + η := by
      intro ε hε a hp
      exact hu ε ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩ a hp
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds,
      (eventually_lt_nhds hδl).filter_mono nhdsWithin_le_nhds]
      with ε hε hεδ hεδl
    obtain ⟨a, hp, _⟩ := hl ε ⟨hε, hεδl⟩
    have hne : (gainValues (closure S) ε).Nonempty :=
      ⟨ε - a, by simpa only [gainValues, mem_ofPred_eq, sub_sub_cancel]
        using (subset_closure hp : (a, 1 - ε) ∈ closure S)⟩
    have hmax := gain_isGreatest isClosed_closure hclosure hne
    have hb := scaled_output_bound_on_closure k hδ1 hu' hmax.1 ⟨hε, hεδ⟩
    have hbound : scaledGain k (closure S) ε ≤ C + η := by
      simpa only [scaledGain, sub_sub_cancel] using hb
    have hclt : C + η < c := by dsimp [η]; linarith
    exact hbound.trans_lt hclt

/-- K016 的容差装配接口；上下界前提均量化真实有限 GKSL 输出。 -/
theorem resetLaw_of_tolerance_bounds
    (hupper : ∀ η : ℝ, 0 < η → ∃ δ > 0, ∀ ε ∈ Ioo (0 : ℝ) δ,
      ∀ a : ℝ, (a, 1 - ε) ∈ finiteOutputs →
        Real.log (1 / ε) / ε * (ε - a) ≤ 4 / Real.exp 1 + η)
    (hlower : ∀ η : ℝ, 0 < η → ∃ δ > 0, ∀ ε ∈ Ioo (0 : ℝ) δ,
      ∃ a : ℝ, (a, 1 - ε) ∈ finiteOutputs ∧
        4 / Real.exp 1 - η ≤ Real.log (1 / ε) / ε * (ε - a)) : ResetLaw := by
  apply scaledGain_closure_tendsto_of_tolerance_bounds
    (S := finiteOutputs) subset_closure 1 (4 / Real.exp 1)
  · simpa only [pow_one] using hupper
  · simpa only [pow_one] using hlower

/-- K017 的容差装配接口；类中每个有限生成元至少有一个对角稳态。 -/
theorem diagonalResetLaw_of_tolerance_bounds
    (hupper : ∀ η : ℝ, 0 < η → ∃ δ > 0, ∀ ε ∈ Ioo (0 : ℝ) δ,
      ∀ a : ℝ, (a, 1 - ε) ∈ diagonalFiniteOutputs →
        Real.log (1 / ε) ^ 2 / ε * (ε - a) ≤ 64 / Real.exp 1 ^ 2 + η)
    (hlower : ∀ η : ℝ, 0 < η → ∃ δ > 0, ∀ ε ∈ Ioo (0 : ℝ) δ,
      ∃ a : ℝ, (a, 1 - ε) ∈ diagonalFiniteOutputs ∧
        64 / Real.exp 1 ^ 2 - η ≤ Real.log (1 / ε) ^ 2 / ε * (ε - a)) :
    DiagonalResetLaw := by
  exact scaledGain_closure_tendsto_of_tolerance_bounds
    (diagonalFiniteOutputs_subset_finiteOutputs.trans subset_closure)
    2 (64 / Real.exp 1 ^ 2) hupper hlower

end TwoStateQuantumEmbedding.ResetEndpoint

#print axioms TwoStateQuantumEmbedding.ResetEndpoint.scaled_output_bound_on_closure
#print axioms TwoStateQuantumEmbedding.ResetEndpoint.scaledGain_closure_tendsto_of_tolerance_bounds
#print axioms TwoStateQuantumEmbedding.ResetEndpoint.resetLaw_of_tolerance_bounds
#print axioms TwoStateQuantumEmbedding.ResetEndpoint.diagonalResetLaw_of_tolerance_bounds
