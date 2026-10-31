import TwoStateQuantumEmbedding.ResetActualEnvelope
import TwoStateQuantumEmbedding.ResetBudgetAsymptotics

noncomputable section
open Set Filter Matrix
open scoped Topology

namespace TwoStateQuantumEmbedding.ResetFinal
open ResetEndpoint ResetActual

/-- 这里只接合统一标量优化与原输出，优化前提在最终主声明中由150消除。 -/
theorem actual_finite_upper_of_refined_envelope
    (hsharp : ∀ η : ℝ, 0 < η → ∃ δ > 0,
      ∀ ρ p ν A B : ℝ, 0 < ρ → ρ < δ → 0 ≤ p → 0 ≤ ν → p+ν ≤ ρ →
        0 ≤ A → 0 ≤ B → Real.log (1/ρ)*ResetEnvelope.envelope p ν A B ≤
          (4/Real.exp 1)*p+η*ρ) :
    ∀ η : ℝ, 0 < η → ∃ δ > 0, ∀ ε ∈ Ioo (0 : ℝ) δ,
      ∀ a : ℝ, (a,1-ε) ∈ finiteOutputs →
        Real.log (1/ε)/ε*(ε-a) ≤ 4/Real.exp 1+η := by
  intro η hη
  obtain ⟨δ,hδ,hbound⟩ := envelope_to_actual_tolerance (4/Real.exp 1)
    (by positivity) ResetEnvelope.envelope hsharp η hη
  refine ⟨min δ (1/4), lt_min hδ (by norm_num), ?_⟩
  intro ε hε a ha
  have hequarter : ε < 1/4 := hε.2.trans_le (min_le_right _ _)
  have heone : ε ∈ Ioo (0 : ℝ) 1 := ⟨hε.1, by linarith⟩
  by_cases hg : 0 ≤ ε-a
  · obtain ⟨n,H,J,t,hH,ht,hout⟩ := ha
    have he : 1-(finiteOutput H J t).2 < 1/4 := by simpa [hout] using hequarter
    have hq : (finiteOutput H J t).1+(finiteOutput H J t).2-1 ≤ 0 := by
      simp only [hout, Prod.fst, Prod.snd]
      linarith
    obtain ⟨ν,p,A,B,hν0,hν,hp0,hp,hA,hB,hbudget,hl,hg'⟩ :=
      finiteOutput_mixed_comparison H J t hH ht he hq
    simp only [hout, Prod.fst, Prod.snd, sub_sub_cancel] at hbudget hg'
    exact hbound ε ⟨hε.1,hε.2.trans_le (min_le_left _ _)⟩
      p ν A B (ε-a) hp0 hν0 hbudget hA hB hg'
  · have hs : 0 ≤ Real.log (1/ε)/ε := div_nonneg (resetLog_pos heone).le hε.1.le
    have hzero := mul_nonpos_of_nonneg_of_nonpos hs (by linarith : ε-a ≤ 0)
    exact hzero.trans (by positivity)

#print axioms actual_finite_upper_of_refined_envelope
end TwoStateQuantumEmbedding.ResetFinal
