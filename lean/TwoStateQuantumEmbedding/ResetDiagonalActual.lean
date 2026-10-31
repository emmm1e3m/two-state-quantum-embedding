import TwoStateQuantumEmbedding.ResetActualEnvelope
import TwoStateQuantumEmbedding.ResetDiagonalComparison
import TwoStateQuantumEmbedding.ResetDiagonalAttainment
import TwoStateQuantumEmbedding.ResetEndpointTolerance

noncomputable section
open Set Filter Matrix Complex
open scoped Topology Matrix.Norms.Operator

namespace TwoStateQuantumEmbedding.ResetFinal
open ResetEndpoint ResetActual

/-- 160的实际比较矩阵严格归一到151的总体时间/速率比参数。 -/
theorem diagonal_normalization (ν A B : ℝ) (hν0 : 0 ≤ ν) (hν : ν < 1/2)
    (hA : 0 < A) (hB : 0 < B) :
    let α := ResetEnvelope.alpha ν A
    let r := ResetEnvelope.up ν A B/α
    let c := ResetEnvelope.down ν A B/α
    0 < α ∧ 0 < B/A ∧ 0 ≤ r ∧ 0 ≤ c ∧
      r*c=ResetDiagonalEnvelope.feedback (ResetEnvelope.chi ν) (B/A) ∧
      NormedSpace.exp (ResetEnvelope.comparisonMatrix ν A B) 0 0=
        ResetComparison.comparisonFlow 1 r c
          (ResetDiagonalEnvelope.zeta (ResetEnvelope.chi ν) (B/A)) 1 0 α 0 := by
  dsimp only
  obtain ⟨hχ0,hχ1,_,_⟩ := ResetMixed.chi_properties ν hν0 hν
  change 0 ≤ ResetEnvelope.chi ν at hχ0
  change ResetEnvelope.chi ν < 1 at hχ1
  have hα : 0 < ResetEnvelope.alpha ν A := by unfold ResetEnvelope.alpha; positivity
  have hden : 1-ResetEnvelope.chi ν ≠ 0 := by linarith
  have hone : 1+ResetEnvelope.chi ν^2 ≠ 0 := by positivity
  have hr : 0 ≤ ResetEnvelope.up ν A B/ResetEnvelope.alpha ν A := by
    unfold ResetEnvelope.up
    exact div_nonneg (div_nonneg (by positivity) (by linarith)) hα.le
  have hc : 0 ≤ ResetEnvelope.down ν A B/ResetEnvelope.alpha ν A := by
    unfold ResetEnvelope.down
    exact div_nonneg (div_nonneg (by positivity) (by linarith)) hα.le
  have hprod : (ResetEnvelope.up ν A B/ResetEnvelope.alpha ν A)*
      (ResetEnvelope.down ν A B/ResetEnvelope.alpha ν A)=
      ResetDiagonalEnvelope.feedback (ResetEnvelope.chi ν) (B/A) := by
    have hs := Real.sq_sqrt (mul_nonneg hA.le hB.le)
    calc
      _ = 2*ResetEnvelope.chi ν*Real.sqrt (A*B)^2 /
          ((1-ResetEnvelope.chi ν)^2*A^2*(1+ResetEnvelope.chi ν^2)) := by
        unfold ResetEnvelope.up ResetEnvelope.down ResetEnvelope.alpha
        field_simp [hA.ne',hden,hone]
        <;> ring
      _ = _ := by
        rw [hs]
        unfold ResetDiagonalEnvelope.feedback
        field_simp [hA.ne',hden,hone]
        <;> ring
  have hlam : ResetEnvelope.lambda ν A B=ResetEnvelope.alpha ν A*
      ResetDiagonalEnvelope.zeta (ResetEnvelope.chi ν) (B/A) := by
    unfold ResetEnvelope.lambda ResetEnvelope.alpha ResetDiagonalEnvelope.zeta
    field_simp [hA.ne',hone]
    <;> ring
  have hmat : ResetEnvelope.comparisonMatrix ν A B = ResetEnvelope.alpha ν A •
      ResetComparison.comparisonMatrix 1 (ResetEnvelope.up ν A B/ResetEnvelope.alpha ν A)
        (ResetEnvelope.down ν A B/ResetEnvelope.alpha ν A)
        (ResetDiagonalEnvelope.zeta (ResetEnvelope.chi ν) (B/A)) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [ResetEnvelope.comparisonMatrix,ResetComparison.comparisonMatrix,
        Matrix.smul_apply,smul_eq_mul,hlam] <;> field_simp [hα.ne']
  refine ⟨hα,div_pos hB hA,hr,hc,hprod,?_⟩
  rw [hmat]
  simp [ResetComparison.comparisonFlow,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

/-- ν≤ε时，正增益的log²/ε尺度不大于log²/ν尺度。 -/
theorem diagonal_scale_mono (ν ε g : ℝ) (hν : 0 < ν) (hε : ε < 1)
    (hνε : ν ≤ ε) (hg : 0 ≤ g) :
    Real.log (1/ε)^2/ε*g ≤ g*Real.log (1/ν)^2/ν := by
  have hepos : 0 < ε := hν.trans_le hνε
  have hLε : 0 ≤ Real.log (1/ε) := Real.log_nonneg (by
    apply (le_div_iff₀ hepos).2
    linarith)
  have hlogs : Real.log (1/ε) ≤ Real.log (1/ν) :=
    Real.log_le_log (by positivity) (one_div_le_one_div_of_le hν hνε)
  have hsquares : Real.log (1/ε)^2 ≤ Real.log (1/ν)^2 := by nlinarith
  have hrat : Real.log (1/ε)^2/ε ≤ Real.log (1/ν)^2/ν := by
    exact (div_le_div_of_nonneg_right hsquares hepos.le).trans
      (div_le_div_of_nonneg_left (sq_nonneg _) hν hνε)
  calc
    _ ≤ Real.log (1/ν)^2/ν*g := mul_le_mul_of_nonneg_right hrat hg
    _ = _ := by ring

/-- 对角类真实有限输出的统一容差上界。 -/
theorem actual_diagonal_upper (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ ε ∈ Ioo (0 : ℝ) δ, ∀ a : ℝ,
      (a,1-ε) ∈ diagonalFiniteOutputs →
        Real.log (1/ε)^2/ε*(ε-a) ≤ 64/(Real.exp 1)^2+η := by
  obtain ⟨δ,hδ,hbound⟩ := ResetDiagonalEnvelope.diagonal_comparison_uniform η hη
  refine ⟨min δ (1/4),lt_min hδ (by norm_num),?_⟩
  intro ε hε a ha
  have hequarter : ε < 1/4 := hε.2.trans_le (min_le_right _ _)
  by_cases hg : 0 < ε-a
  · obtain ⟨n,H,J,t,hH,ht,hs,hout⟩ := ha
    have he : 1-(finiteOutput H J t).2 < 1/4 := by simpa [hout] using hequarter
    have hq : (finiteOutput H J t).1+(finiteOutput H J t).2-1 ≤ 0 := by
      simp only [hout]
      linarith
    obtain ⟨ν,A,B,hν0,hνε,hνhalf,hA,hB,hid,hcomp,hgain⟩ :=
      diagonal_finiteOutput_comparison H J t hH ht hs he hq
    simp only [hout,sub_sub_cancel] at hνε hid hcomp
    have hν : 0 < ν := by
      by_contra hn
      have hz : ν=0 := by linarith
      rw [hz,zero_mul] at hid
      linarith [hε.1]
    have hlower : lowerComparison 0 ν A B ≤ a+(1-ε)-1 := by
      simpa only [lowerComparison_zero_tilt] using hcomp
    obtain ⟨hAp,hBp⟩ := positive_rates_of_negative_diagonal_comparison hA hB (by linarith) hlower
    obtain ⟨hα,hτ,hr,hc,hprod,hflow⟩ := diagonal_normalization ν A B hν0 hνhalf hAp hBp
    rw [hflow] at hcomp
    have hb := hbound ν hν (hνε.trans_lt (hε.2.trans_le (min_le_left _ _)))
      (B/A) (ResetEnvelope.up ν A B/ResetEnvelope.alpha ν A)
      (ResetEnvelope.down ν A B/ResetEnvelope.alpha ν A) (ResetEnvelope.alpha ν A)
      (a+(1-ε)-1) hτ hr hc hprod hα.le hcomp
    have hmax : max (-(a+(1-ε)-1)) 0=ε-a := by rw [max_eq_left (by linarith)]; ring
    rw [hmax] at hb
    exact (diagonal_scale_mono ν ε (ε-a) hν (by linarith) hνε hg.le).trans hb
  · have hscale : 0 ≤ Real.log (1/ε)^2/ε := div_nonneg (sq_nonneg _) hε.1.le
    exact (mul_nonpos_of_nonneg_of_nonpos hscale (by linarith)).trans (by positivity)

/-- 153的同一有限生成元见证直接进入144对角输出集合。 -/
theorem actual_diagonal_lower (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ ε ∈ Ioo (0 : ℝ) δ, ∃ a : ℝ,
      (a,1-ε) ∈ diagonalFiniteOutputs ∧
        64/(Real.exp 1)^2-η ≤ Real.log (1/ε)^2/ε*(ε-a) := by
  obtain ⟨δ,hδ,hcover⟩ := ResetDiagonalFamily.every_small_actual_error_unit η hη
  refine ⟨δ,hδ,?_⟩
  intro ε hε
  obtain ⟨H,J,ν,a,hH,hν,hs,hout,hclose⟩ := hcover ε hε
  refine ⟨a,?_,?_⟩
  · refine ⟨1,H,J,1,hH,by norm_num,?_,hout⟩
    refine ⟨ν,⟨hν.1.le,hν.2.le⟩,?_⟩
    have hd : diagonalState ν=ResetDiagonalFamily.diagonalState ν := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [diagonalState,ResetDiagonalFamily.diagonalState]
    rw [hd]
    exact hs
  · have hl := (abs_lt.mp hclose).1
    linarith

/-- K017：对角稳态类的无条件实际误差渐近。 -/
theorem diagonal_reset_sharp_law : DiagonalResetLaw :=
  diagonalResetLaw_of_tolerance_bounds actual_diagonal_upper actual_diagonal_lower

#print axioms diagonal_normalization
#print axioms actual_diagonal_upper
#print axioms actual_diagonal_lower
#print axioms diagonal_reset_sharp_law
end TwoStateQuantumEmbedding.ResetFinal
