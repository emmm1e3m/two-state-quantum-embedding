import TwoStateQuantumEmbedding.ResetCore
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! 对角稳态上界的标量模块；实际矩阵比较连接单独列出。 -/
noncomputable section
open Filter Topology

namespace TwoStateQuantumEmbedding.ResetDiagonalEnvelope

def scalarD0 (β d : ℝ) : ℝ :=
  (1 - β) * d * (d * β / (1 + d)) ^ (β / (1 - β))

/-- 与既有精确幂优化器的代数连接。 -/
theorem scalarD0_eq_envelope (β d : ℝ) (hβ : 0 < β) (hβ1 : β < 1)
    (hd : 0 < d) :
    Reset.scalarEnvelope (1 + d) d ((1 - β) / β) = scalarD0 β d := by
  have hb : 0 < d * β / (1 + d) := by positivity
  have hβn : β ≠ 0 := ne_of_gt hβ
  have hbn : 1 - β ≠ 0 := ne_of_gt (sub_pos.mpr hβ1)
  have hdn : 1 + d ≠ 0 := by positivity
  have hbase : d / ((1 + (1 - β) / β) * (1 + d)) = d * β / (1 + d) := by
    field_simp
    <;> ring
  have hexp : (1 + (1 - β) / β) / ((1 - β) / β) = 1 + β / (1 - β) := by
    field_simp
    <;> ring
  unfold Reset.scalarEnvelope scalarD0
  rw [hbase, hexp, Real.rpow_add hb, Real.rpow_one]
  field_simp
  <;> ring

/-- 任意时间上的两指数精确上界，时间无上界约束。 -/
theorem scalarD0_exponential_bound (β d x : ℝ)
    (hβ : 0 < β) (hβ1 : β < 1) (hd : 0 < d) :
    d * Real.exp (-β * x) - (1 + d) * Real.exp (-x) ≤ scalarD0 β d := by
  have hk : 0 < (1 - β) / β := by positivity
  have h := Reset.scalar_envelope_bound (1 + d) d ((1 - β) / β)
    (Real.exp (-β * x)) (by positivity) hd hk (Real.exp_nonneg _)
  have he : (Real.exp (-β * x)) ^ (1 + (1 - β) / β) = Real.exp (-x) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    field_simp
    <;> ring
  rw [he, scalarD0_eq_envelope β d hβ hβ1 hd] at h
  exact h

theorem scalarD0_pos (β d : ℝ) (hβ : 0 < β) (hβ1 : β < 1)
    (hd : 0 < d) : 0 < scalarD0 β d := by
  unfold scalarD0
  positivity

def optimalTime (β d : ℝ) : ℝ := -Real.log (d * β / (1 + d)) / (1 - β)

theorem optimalTime_pos (β d : ℝ) (hβ : 0 < β) (hβ1 : β < 1)
    (hd : 0 < d) : 0 < optimalTime β d := by
  have hb : 0 < d * β / (1 + d) := by positivity
  have hb1 : d * β / (1 + d) < 1 := by
    apply (div_lt_one (by positivity)).2
    nlinarith
  exact div_pos (neg_pos.mpr (Real.log_neg hb hb1)) (sub_pos.mpr hβ1)

/-- 显式正时间达到 D0，供真实负反馈族复用。 -/
theorem scalarD0_exponential_attains (β d : ℝ)
    (hβ : 0 < β) (hβ1 : β < 1) (hd : 0 < d) :
    d * Real.exp (-β * optimalTime β d) -
      (1 + d) * Real.exp (-optimalTime β d) = scalarD0 β d := by
  have hb : 0 < d * β / (1 + d) := by positivity
  have hbn : 1 - β ≠ 0 := ne_of_gt (sub_pos.mpr hβ1)
  have hdn : 1 + d ≠ 0 := by positivity
  have hslow : Real.exp (-β * optimalTime β d) =
      (d * β / (1 + d)) ^ (β / (1 - β)) := by
    rw [Real.rpow_def_of_pos hb]
    congr 1
    unfold optimalTime
    ring
  have hfast : Real.exp (-optimalTime β d) =
      (d * β / (1 + d)) ^ (1 + β / (1 - β)) := by
    rw [Real.rpow_def_of_pos hb]
    congr 1
    unfold optimalTime
    field_simp
    <;> ring
  rw [hslow, hfast, Real.rpow_add hb, Real.rpow_one]
  unfold scalarD0
  field_simp
  <;> ring

/-- 保留自由人口项后的负部界。 -/
theorem signed_population_scalar_bound (q β d x : ℝ)
    (hβ : 0 < β) (hβ1 : β < 1) (hd : 0 < d)
    (hq : (1 + d) * Real.exp (-x) - d * Real.exp (-β * x) ≤ q) :
    max (-q) 0 ≤ scalarD0 β d := by
  apply max_le
  · linarith [scalarD0_exponential_bound β d x hβ hβ1 hd]
  · exact (scalarD0_pos β d hβ hβ1 hd).le


#print axioms scalarD0_exponential_bound
#print axioms scalarD0_exponential_attains
#print axioms signed_population_scalar_bound
end TwoStateQuantumEmbedding.ResetDiagonalEnvelope
