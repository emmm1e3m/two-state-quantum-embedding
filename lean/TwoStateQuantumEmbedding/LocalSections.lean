import TwoStateQuantumEmbedding.Envelope

/-! 从真实下边界的局部单调和已证填充得到完整固定和切片。 -/
noncomputable section
open Set

namespace TwoStateQuantumEmbedding.LocalSections
open CanonicalBias Envelope

def sumBoundary (b : ℝ) := lowerBoundary b + b

theorem coordinates_le_boundary_parameter {η s t : ℝ}
    (hs : s ≤ η) (ht : t ∈ Icc (0 : ℝ) η)
    (hst : sumBoundary t = s) (hmono : StrictMonoOn sumBoundary (Icc (0 : ℝ) η))
    {p : ℝ × ℝ} (hp : p ∈ Q2) (hpsum : p.1 + p.2 = s) : p.1 ≤ t ∧ p.2 ≤ t := by
  have hpbox := Q2_subset_unitSquare hp
  have hp1 : p.1 ∈ Icc (0 : ℝ) η := ⟨hpbox.1.1, by linarith [hpbox.2.1]⟩
  have hp2 : p.2 ∈ Icc (0 : ℝ) η := ⟨hpbox.2.1, by linarith [hpbox.1.1]⟩
  have hfirst : sumBoundary p.1 ≤ s := by
    have hf := lowerBoundary_le_of_mem hpbox.1 (Q2_swap hp)
    dsimp [sumBoundary]
    linarith
  have hsecond : sumBoundary p.2 ≤ s := by
    have hf := lowerBoundary_le_of_mem hpbox.2 hp
    dsimp [sumBoundary]
    linarith
  constructor
  · by_contra hh
    have hm := hmono ht hp1 (lt_of_not_ge hh)
    linarith
  · by_contra hh
    have hm := hmono ht hp2 (lt_of_not_ge hh)
    linarith

theorem F_eq_of_sumBoundary {η s t : ℝ}
    (hη : η ≤ 1) (hs : s ≤ η) (ht : t ∈ Icc (0 : ℝ) η)
    (hst : sumBoundary t = s) (hmono : StrictMonoOn sumBoundary (Icc (0 : ℝ) η)) :
    F (s - 1) = t - lowerBoundary t := by
  have htunit : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans hη⟩
  have hfb := lowerBoundary_bounds htunit
  have hs0 : 0 ≤ s := by dsimp [sumBoundary] at hst; linarith
  have hx : s - 1 ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hbpoint := lowerBoundary_mem_Q2 htunit
  have hpoint : outputFromXZ (s - 1) (lowerBoundary t - t) = (lowerBoundary t, t) := by
    ext <;> dsimp [outputFromXZ, sumBoundary] at * <;> linarith
  have hlow := (mem_Q2_iff.mp (hpoint.symm ▸ hbpoint)).2
  rw [abs_of_nonpos (sub_nonpos.mpr hfb.2)] at hlow
  have hhigh := (coordinates_le_boundary_parameter hs ht hst hmono (F_mem hx)
    (by dsimp [outputFromXZ]; ring)).1
  dsimp [outputFromXZ] at hhigh
  dsimp [sumBoundary] at hst
  linarith

theorem exact_local_section_of_monotonicity {η s t : ℝ}
    (hη : η ≤ 1) (hs : s ≤ η) (ht : t ∈ Icc (0 : ℝ) η)
    (hst : sumBoundary t = s) (hmono : StrictMonoOn sumBoundary (Icc (0 : ℝ) η)) :
    {a : ℝ | a ∈ Icc (0 : ℝ) s ∧ (a, s - a) ∈ Q2} = Icc (lowerBoundary t) t := by
  have htunit : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans hη⟩
  have hf := lowerBoundary_bounds htunit
  have hs0 : 0 ≤ s := by dsimp [sumBoundary] at hst; linarith
  have hx : s - 1 ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hF := F_eq_of_sumBoundary hη hs ht hst hmono
  ext a
  constructor
  · rintro ⟨_, hqa⟩
    have hh := coordinates_le_boundary_parameter hs ht hst hmono hqa (by simp)
    dsimp [sumBoundary] at hst
    exact ⟨by dsimp at hh; linarith, hh.1⟩
  · intro ha
    have hst' : lowerBoundary t + t = s := hst
    refine ⟨⟨by linarith [ha.1], by linarith [ha.2]⟩, ?_⟩
    have he : outputFromXZ (s - 1) (2 * a - s) = (a, s - a) := by
      ext <;> dsimp [outputFromXZ] <;> ring
    rw [← he, mem_Q2_iff, hF]
    exact ⟨hx, abs_le.mpr ⟨by linarith [ha.1], by linarith [ha.2]⟩⟩

#print axioms F_eq_of_sumBoundary
#print axioms exact_local_section_of_monotonicity

end TwoStateQuantumEmbedding.LocalSections
