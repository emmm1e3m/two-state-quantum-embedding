import TwoStateQuantumEmbedding.ResetRemainder
import Mathlib.LinearAlgebra.Matrix.PosDef

noncomputable section
open Filter Topology Matrix
open scoped ComplexOrder
open TwoStateQuantumEmbedding TwoStateQuantumEmbedding.ResetFamily

namespace TwoStateQuantumEmbedding.ResetFamily

/-- 任意一个已证明的尾段性质都可随连续覆盖的见证一起保留。 -/
theorem cover_with_eventual (P : ℝ → Prop) (hP : ∀ᶠ L : ℝ in atTop, P L) :
    ∃ ε₀ > 0, ∀ ε ∈ Set.Ioo 0 ε₀, ∃ L : ℝ,
      2 < L ∧ 1 < curveA L ∧ curveEpsilon L = ε ∧ P L := by
  have hevent : ∀ᶠ L : ℝ in atTop,
      2 < L ∧ 1 < curveA L ∧ 0 < curveEpsilon L ∧ P L :=
    (eventually_gt_atTop (2 : ℝ)).and
      (curveA_eventually_gt_one.and (curveEpsilon_eventually_pos.and hP))
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp hevent
  refine ⟨curveEpsilon L₀, (hL₀ L₀ le_rfl).2.2.1, ?_⟩
  intro ε hε
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.mp
    (curveEpsilon_limit.eventually (eventually_lt_nhds hε.1))
  let M := max L₀ L₁
  have hm : L₀ ≤ M := le_max_left _ _
  have hεM : curveEpsilon M < ε := hL₁ M (le_max_right _ _)
  have hc : ContinuousOn curveEpsilon (Set.Icc L₀ M) := by
    intro x hx
    exact (curveEpsilon_continuousAt x (hL₀ x hx.1).1
      (hL₀ x hx.1).2.1).continuousWithinAt
  obtain ⟨L, hLint, hLe⟩ := intermediate_value_Icc' hm hc ⟨hεM.le, hε.2.le⟩
  exact ⟨L, (hL₀ L hLint.1).1, (hL₀ L hLint.1).2.1, hLe,
    (hL₀ L hLint.1).2.2.2⟩

/-- 对每个小 ε，以同一个常数实现原始有限 GKSL 概率及论文余项。 -/
theorem reset_every_small_epsilon_uniform :
    ∃ C > 0, ∃ ε₀ > 0, ∀ ε ∈ Set.Ioo 0 ε₀, ∃ L a : ℝ,
      2 < L ∧ 1 < curveA L ∧ 0 < curveTime L ∧
      (∀ μ : Fin 1, (unitJumps L μ).rank = 1) ∧
      finiteOutput 0 (unitJumps L) 1 = (a, 1 - ε) ∧
      (a, 1 - ε) ∈ finiteOutputs ∧ 0 < a ∧ a < ε ∧
      |a / ε - (1 - (4 / Real.exp 1) / Real.log (1 / ε))| ≤
        C * (Real.log (Real.log (1 / ε)) / Real.log (1 / ε) ^ 2) := by
  obtain ⟨C₀, hC₀⟩ := Asymptotics.isBigO_iff.mp finiteOutput_remainder_isBigO
  let C := |C₀| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hbound : ∀ᶠ L in atTop, ‖actualRemainder L‖ ≤ C * ‖actualRemainderScale L‖ := by
    filter_upwards [hC₀] with L hL
    exact hL.trans (mul_le_mul_of_nonneg_right
      (by dsimp [C]; linarith [le_abs_self C₀]) (norm_nonneg _))
  have htail : ∀ᶠ L : ℝ in atTop,
      0 < curveTime L ∧ (∀ μ : Fin 1, (unitJumps L μ).rank = 1) ∧
      (0 < (finiteOutput 0 (unitJumps L) 1).1 ∧
        (finiteOutput 0 (unitJumps L) 1).1 < 1 - (finiteOutput 0 (unitJumps L) 1).2) ∧
      ‖actualRemainder L‖ ≤ C * ‖actualRemainderScale L‖ ∧ 1 < logScale L := by
    filter_upwards [time_eventually_pos, unitJumps_eventually_rank_one,
      finiteOutput_nonclassical_tail, hbound, logScale_eventually_gt_one]
      with L ht hr hp hb hlog
    exact ⟨ht, hr, ⟨hp.1, hp.2.1⟩, hb, hlog⟩
  obtain ⟨ε₀, hε₀, hcover⟩ := cover_with_eventual _ htail
  refine ⟨C, hC, ε₀, hε₀, ?_⟩
  intro ε hε
  obtain ⟨L, hL, hA, he, ht, hr, hp, hb, hlog⟩ := hcover ε hε
  have hout := actual_unit_curve_output L hL hA
  have heactual : actualEpsilon L = ε := by
    simp only [actualEpsilon, hout, curvePoint, sub_sub_cancel, he]
  have hsecond : (finiteOutput 0 (unitJumps L) 1).2 = 1 - ε := by
    rw [hout]; simp only [curvePoint, he]
  have hpair : finiteOutput 0 (unitJumps L) 1 =
      ((finiteOutput 0 (unitJumps L) 1).1, 1 - ε) := Prod.ext rfl hsecond
  have hscale : 0 < Real.log (Real.log (1 / ε)) / Real.log (1 / ε) ^ 2 := by
    have hlog' : 1 < Real.log (1 / ε) := by simpa only [logScale, he] using hlog
    exact div_pos (Real.log_pos hlog') (sq_pos_of_pos (by linarith))
  refine ⟨L, (finiteOutput 0 (unitJumps L) 1).1, hL, hA, ht, hr, hpair,
    ⟨1, 0, unitJumps L, 1, by simp, by norm_num, hpair⟩, hp.1, ?_, ?_⟩
  · simpa only [hsecond, sub_sub_cancel] using hp.2
  · simpa only [actualRemainder, actualRemainderScale, heactual,
      Real.norm_eq_abs, abs_of_pos hscale] using hb

/-- 实构造的零模是归一化纯密度矩阵。 -/
theorem groundMode_is_pure_density (c s : ℝ) (hc : c ^ 2 + s ^ 2 = 1) :
    (groundMode c s).PosSemidef ∧ Matrix.trace (groundMode c s) = 1 ∧
      groundMode c s * groundMode c s = groundMode c s := by
  have hρ : groundMode c s =
      Matrix.vecMulVec ![(s : ℂ), c] (star ![(s : ℂ), c]) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [groundMode, conjugate, rotation, ground, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.vecMulVec]
  have hC : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hc
  refine ⟨?_, ?_, ?_⟩
  · rw [hρ]
    exact Matrix.posSemidef_vecMulVec_self_star _
  · rw [hρ]
    simp [Matrix.trace, Matrix.diag, Matrix.vecMulVec, Fin.sum_univ_two]
    linear_combination hC
  · rw [hρ]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.vecMulVec, Fin.sum_univ_two]
    · linear_combination (s : ℂ) ^ 2 * hC
    · linear_combination (s : ℂ) * (c : ℂ) * hC
    · linear_combination (s : ℂ) * (c : ℂ) * hC
    · linear_combination (c : ℂ) ^ 2 * hC

/-- 纯稳态接回同一个单位时间、已缩放的原始跳跃。 -/
theorem reset_pure_stationary (L : ℝ) (ht : 0 ≤ curveTime L) :
    ∃ ρ : QubitMatrix, ρ.PosSemidef ∧ Matrix.trace ρ = 1 ∧ ρ * ρ = ρ ∧
      gkslAction 0 (unitJumps L) ρ = 0 := by
  let ρ := groundMode (Real.cos (radius L)) (Real.sin (radius L))
  have hp := groundMode_is_pure_density (Real.cos (radius L))
    (Real.sin (radius L)) (Real.cos_sq_add_sin_sq _)
  refine ⟨ρ, hp.1, hp.2.1, hp.2.2, ?_⟩
  have hs := gkslAction_time_scaling (0 : QubitMatrix)
    (paperJumps (radius L) (rateRatio L)) ρ (curveTime L) ht
  simp only [smul_zero] at hs
  change gkslAction 0 (unitJumps L) ρ = _ at hs
  rw [hs]
  have he : gkslAction 0 (paperJumps (radius L) (rateRatio L)) ρ = 0 :=
    ground_eigen _ _ _ _ (Real.cos_sq_add_sin_sq _)
  rw [he, smul_zero]

theorem reset_pure_stationary_tail : ∀ᶠ L : ℝ in atTop,
    ∃ ρ : QubitMatrix, ρ.PosSemidef ∧ Matrix.trace ρ = 1 ∧ ρ * ρ = ρ ∧
      gkslAction 0 (unitJumps L) ρ = 0 := by
  filter_upwards [time_eventually_pos] with L ht
  exact reset_pure_stationary L ht.le

end TwoStateQuantumEmbedding.ResetFamily

#print axioms TwoStateQuantumEmbedding.ResetFamily.cover_with_eventual
#print axioms TwoStateQuantumEmbedding.ResetFamily.reset_every_small_epsilon_uniform
#print axioms TwoStateQuantumEmbedding.ResetFamily.reset_pure_stationary

