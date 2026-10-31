import TwoStateQuantumEmbedding.ResetCore
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section
open Filter Topology

namespace TwoStateQuantumEmbedding.ResetEnvelope.LowRatio

def rho (L : ℝ) : ℝ := Real.exp (-L)
def root (L : ℝ) : ℝ := Real.exp (-L / 2)
def floor (L : ℝ) : ℝ := Real.exp (-3 * L / 4)
def quarter (L : ℝ) : ℝ := Real.exp (-L / 4)
def logConstant : ℝ := Real.log 69
def residual (L : ℝ) : ℝ := 80 * root L + 4 * rho L + 35 * quarter L
def windowError (s : ℝ) : ℝ := 128 * Real.sqrt s + 256 * s
def windowMultiplier (s : ℝ) : ℝ := (1 + s) ^ 2 * Real.exp (2 * logConstant * s)
def totalWindowError (s : ℝ) : ℝ :=
  (windowMultiplier s * (1 + s) ^ 2 - 1) * (4 / Real.exp 1) +
    windowMultiplier s * windowError s / Real.exp 1

theorem rho_pos (L : ℝ) : 0 < rho L := Real.exp_pos _
theorem root_pos (L : ℝ) : 0 < root L := Real.exp_pos _
theorem floor_pos (L : ℝ) : 0 < floor L := Real.exp_pos _
theorem quarter_pos (L : ℝ) : 0 < quarter L := Real.exp_pos _

theorem root_sq (L : ℝ) : root L ^ 2 = rho L := by
  rw [root, pow_two, ← Real.exp_add, rho]
  congr 1
  ring

theorem sqrt_rho (L : ℝ) : Real.sqrt (rho L) = root L := by
  rw [← root_sq L, Real.sqrt_sq (root_pos L).le]

theorem rho_le_root (L : ℝ) (hL : 0 ≤ L) : rho L ≤ root L := by
  apply Real.exp_le_exp.mpr
  linarith

theorem floor_le_root (L : ℝ) (hL : 0 ≤ L) : floor L ≤ root L := by
  apply Real.exp_le_exp.mpr
  linarith

theorem root_floor (L : ℝ) : root L * floor L = rho L * quarter L := by
  unfold root floor rho quarter
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem floor_sq_le (L : ℝ) (hL : 0 ≤ L) : floor L ^ 2 ≤ rho L * quarter L := by
  unfold floor rho quarter
  rw [pow_two, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

/-- 加入严格正底限后的同一组对数界，包括原权重为零。 -/
theorem regularized_bounds (q L : ℝ) (hL : 0 ≤ L) (hq : 0 ≤ q)
    (hcoarse : q ≤ 68 * root L) :
    0 < q + floor L ∧ q + floor L ≤ 69 * root L ∧
      -L ≤ Real.log (q + floor L) ∧
      Real.log (q + floor L) ≤ -L / 2 + logConstant := by
  have hpos : 0 < q + floor L := by linarith [floor_pos L]
  have hu : q + floor L ≤ 69 * root L := by linarith [floor_le_root L hL]
  refine ⟨hpos, hu, ?_, ?_⟩
  · have hlog := Real.log_le_log (floor_pos L) (show floor L ≤ q + floor L by linarith)
    rw [floor, Real.log_exp] at hlog
    change -3 * L / 4 ≤ Real.log (q + floor L) at hlog
    linarith
  · have hlog := Real.log_le_log hpos hu
    rw [Real.log_mul (by norm_num) (root_pos L).ne', root, Real.log_exp] at hlog
    simpa only [logConstant, add_comm] using hlog

/-- 正底限只引入统一的 exp(-5L/4) 平方误差。 -/
theorem regularized_square (q L : ℝ) (hL : 0 ≤ L) (_hq : 0 ≤ q)
    (hcoarse : q ≤ 68 * root L) :
    (q + floor L) ^ 2 / 4 ≤ q ^ 2 / 4 + 35 * rho L * quarter L := by
  have hm := mul_le_mul_of_nonneg_right hcoarse (floor_pos L).le
  have he := root_floor L
  have hf := floor_sq_le L hL
  nlinarith [mul_pos (rho_pos L) (quarter_pos L)]

theorem exp_decay_limit (c : ℝ) (hc : 0 < c) :
    Tendsto (fun L : ℝ => Real.exp (-c * L)) atTop (𝓝 0) := by
  simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0 : ℝ) c hc

theorem linear_exp_decay_limit (c : ℝ) (hc : 0 < c) :
    Tendsto (fun L : ℝ => L * Real.exp (-c * L)) atTop (𝓝 0) := by
  simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) c hc

theorem root_limit : Tendsto root atTop (𝓝 0) := by
  have he : root = fun L : ℝ => Real.exp (-(1 / 2 : ℝ) * L) := by
    funext L
    unfold root
    congr 1
    ring
  rw [he]
  exact exp_decay_limit (1 / 2) (by norm_num)

theorem rho_limit : Tendsto rho atTop (𝓝 0) := by
  change Tendsto (fun L : ℝ => Real.exp (-L)) atTop (𝓝 0)
  simpa only [neg_mul, one_mul] using exp_decay_limit 1 (by norm_num)

theorem root_linear_limit : Tendsto (fun L : ℝ => L * root L) atTop (𝓝 0) := by
  have he : (fun L : ℝ => L * root L) =
      fun L : ℝ => L * Real.exp (-(1 / 2 : ℝ) * L) := by
    funext L
    unfold root
    congr 2
    ring
  rw [he]
  exact linear_exp_decay_limit (1 / 2) (by norm_num)

theorem residual_linear_limit : Tendsto (fun L : ℝ => L * residual L) atTop (𝓝 0) := by
  have h1 := root_linear_limit.const_mul 80
  have h2 := (linear_exp_decay_limit 1 (by norm_num)).const_mul 4
  have h3 := (linear_exp_decay_limit (1 / 4) (by norm_num)).const_mul 35
  have h := (h1.add h2).add h3
  convert h using 1
  · funext L
    unfold residual rho quarter
    have he : -(1 / 4 : ℝ) * L = -L / 4 := by ring
    rw [he]
    simp only [neg_mul, one_mul]
    ring
  · norm_num

theorem correction_limit :
    Tendsto (fun L : ℝ => Real.exp (256 * root L * L)) atTop (𝓝 1) := by
  have h := (root_linear_limit.const_mul 256).rexp
  convert h using 1
  · funext L
    congr 1
    ring
  · norm_num

theorem totalWindowError_continuous : ContinuousAt totalWindowError 0 := by
  unfold totalWindowError windowMultiplier windowError
  fun_prop

theorem totalWindowError_zero : totalWindowError 0 = 0 := by
  norm_num [totalWindowError, windowMultiplier, windowError]

theorem windowMultiplier_ge_one (s : ℝ) (hs : 0 ≤ s) : 1 ≤ windowMultiplier s := by
  have hC : 0 ≤ logConstant := Real.log_nonneg (by norm_num)
  have he : 1 ≤ Real.exp (2 * logConstant * s) := Real.one_le_exp (by positivity)
  have hp : 1 ≤ (1 + s) ^ 2 := by nlinarith
  unfold windowMultiplier
  nlinarith

/-- 领先单峰的统一最大值，不限制 τ 随 L 的变化方式。 -/
theorem profile_bound (L τ : ℝ) (hL : 0 < L) :
    L * τ * Real.exp (-τ * L) ≤ 1 / Real.exp 1 := by
  have h := Real.mul_exp_neg_le_exp_neg_one (L * τ)
  rw [Real.exp_neg 1] at h
  rw [show -τ * L = -(L * τ) by ring]
  simpa only [one_div] using h

end TwoStateQuantumEmbedding.ResetEnvelope.LowRatio

#print axioms TwoStateQuantumEmbedding.ResetEnvelope.LowRatio.regularized_bounds
#print axioms TwoStateQuantumEmbedding.ResetEnvelope.LowRatio.regularized_square
#print axioms TwoStateQuantumEmbedding.ResetEnvelope.LowRatio.residual_linear_limit
#print axioms TwoStateQuantumEmbedding.ResetEnvelope.LowRatio.totalWindowError_continuous
