import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! 非交换实 Banach 代数中的 Duhamel 恒等式；由指数导数和微积分基本定理推出。 -/

noncomputable section

open NormedSpace MeasureTheory Set
open scoped Interval

namespace TwoStateQuantumEmbedding

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄]

/-- 乘积路径的导数严格保留左右因子顺序，不使用 A、B 交换。 -/
theorem hasDerivAt_duhamel_path (A B : 𝔄) (t s : ℝ) :
    HasDerivAt
      (fun r : ℝ => exp ((t - r) • (A + B)) * exp (r • A))
      (-(exp ((t - s) • (A + B)) * B * exp (s • A))) s := by
  have hl : HasDerivAt (fun r : ℝ => exp ((t - r) • (A + B)))
      (-(exp ((t - s) • (A + B)) * (A + B))) s := by
    simpa [Function.comp_def] using
      (hasDerivAt_exp_smul_const (A + B) (t - s)).scomp s
        ((hasDerivAt_const s t).sub (hasDerivAt_id s))
  have hr := hasDerivAt_exp_smul_const' A s
  convert hl.mul hr using 1
  noncomm_ring

/-- 固定插入算符的传播子积分核连续，因此所有有限区间上可积。 -/
theorem continuous_duhamel_kernel (L R B : 𝔄) (t : ℝ) :
    Continuous (fun s : ℝ => exp ((t - s) • L) * B * exp (s • R)) := by
  have hl : Continuous (fun s : ℝ => exp ((t - s) • L)) :=
    (differentiable_exp_smul_const ℝ L).continuous.comp
      (continuous_const.sub continuous_id)
  have hr : Continuous (fun s : ℝ => exp (s • R)) :=
    (differentiable_exp_smul_const ℝ R).continuous
  exact (hl.mul continuous_const).mul hr

/-- 任意实时间的精确 Duhamel 恒等式，负时间采用定向区间积分。 -/
theorem exp_add_sub_exp_eq_integral (A B : 𝔄) (t : ℝ) :
    exp (t • (A + B)) - exp (t • A) =
      ∫ s in (0 : ℝ)..t, exp ((t - s) • (A + B)) * B * exp (s • A) := by
  have hc : Continuous
      (fun s : ℝ => -(exp ((t - s) • (A + B)) * B * exp (s • A))) := by
    exact (continuous_duhamel_kernel (A + B) A B t).neg
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := t)
    (fun s _ => hasDerivAt_duhamel_path A B t s)
    (hc.intervalIntegrable 0 t)
  have hn := congrArg Neg.neg hf
  simpa [intervalIntegral.integral_neg, NormedSpace.exp_zero] using hn.symm

/-- 用户所需的单位时间形式。 -/
theorem exp_add_sub_exp_eq_integral_unit (A B : 𝔄) :
    exp (A + B) - exp A =
      ∫ s in (0 : ℝ)..1, exp ((1 - s) • (A + B)) * B * exp (s • A) := by
  simpa only [one_smul] using exp_add_sub_exp_eq_integral A B 1

/-- 右侧放置含扰动传播子的等价 Duhamel 形式。 -/
theorem exp_add_sub_exp_eq_integral_right (A B : 𝔄) (t : ℝ) :
    exp (t • (A + B)) - exp (t • A) =
      ∫ s in (0 : ℝ)..t, exp ((t - s) • A) * B * exp (s • (A + B)) := by
  have h := congrArg Neg.neg (exp_add_sub_exp_eq_integral (A + B) (-B) t)
  simpa [mul_neg, neg_mul, intervalIntegral.integral_neg] using h

/-- 不预设 Hamiltonian 范数上界的一阶 Duhamel 项。 -/
def expFirstOrder (A B : 𝔄) (t : ℝ) : 𝔄 :=
  ∫ s in (0 : ℝ)..t, exp ((t - s) • A) * B * exp (s • A)

/-- 精确的一阶展开余项；此式没有把积分余项或 Duhamel 作为假设。 -/
theorem exp_first_order_remainder_eq_integral (A B : 𝔄) (t : ℝ) :
    exp (t • (A + B)) - exp (t • A) - expFirstOrder A B t =
      ∫ s in (0 : ℝ)..t, exp ((t - s) • A) * B *
        (exp (s • (A + B)) - exp (s • A)) := by
  rw [exp_add_sub_exp_eq_integral_right, expFirstOrder,
    ← intervalIntegral.integral_sub
      ((continuous_duhamel_kernel A (A + B) B t).intervalIntegrable 0 t)
      ((continuous_duhamel_kernel A A B t).intervalIntegrable 0 t)]
  simp only [mul_sub]

/-- 完整二阶有序积分余项；含扰动传播子位于最右端。 -/
theorem exp_first_order_remainder_eq_double_integral (A B : 𝔄) (t : ℝ) :
    exp (t • (A + B)) - exp (t • A) - expFirstOrder A B t =
      ∫ s in (0 : ℝ)..t, ∫ r in (0 : ℝ)..s,
        exp ((t - s) • A) * B * exp ((s - r) • A) * B * exp (r • (A + B)) := by
  rw [exp_first_order_remainder_eq_integral]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [exp_add_sub_exp_eq_integral_right]
  have hi := (ContinuousLinearMap.mul ℝ 𝔄 (exp ((t - s) • A) * B)).intervalIntegral_comp_comm
    (μ := volume)
    ((continuous_duhamel_kernel A (A + B) B s).intervalIntegrable 0 s)
  simpa only [ContinuousLinearMap.mul_apply', mul_assoc] using hi.symm

/-- 给定两个传播子在同一时间段上的范数界，得到一次扰动界。 -/
theorem norm_exp_add_sub_le_of_bounds (A B : 𝔄) (t : ℝ) (ht : 0 ≤ t)
    (CA CAB : ℝ)
    (hA : ∀ s ∈ Icc (0 : ℝ) t, ‖exp (s • A)‖ ≤ CA)
    (hAB : ∀ s ∈ Icc (0 : ℝ) t, ‖exp (s • (A + B))‖ ≤ CAB) :
    ‖exp (t • (A + B)) - exp (t • A)‖ ≤ CAB * ‖B‖ * CA * t := by
  have hCAB0 : 0 ≤ CAB := (norm_nonneg _).trans (hAB 0 ⟨le_rfl, ht⟩)
  rw [exp_add_sub_exp_eq_integral]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := t) (C := CAB * ‖B‖ * CA)
    (f := fun s : ℝ => exp ((t - s) • (A + B)) * B * exp (s • A))
    (fun s hs => ?_)
  · simpa [abs_of_nonneg ht] using hi
  · have hs' : s ∈ Ioc (0 : ℝ) t := by simpa only [uIoc_of_le ht] using hs
    have hsA := hA s ⟨hs'.1.le, hs'.2⟩
    have hsAB := hAB (t - s) ⟨sub_nonneg.mpr hs'.2, by linarith [hs'.1]⟩
    calc
      ‖exp ((t - s) • (A + B)) * B * exp (s • A)‖
          ≤ ‖exp ((t - s) • (A + B)) * B‖ * ‖exp (s • A)‖ := norm_mul_le _ _
      _ ≤ (CAB * ‖B‖) * CA :=
        mul_le_mul ((norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right hsAB (norm_nonneg B))) hsA
          (norm_nonneg _) (mul_nonneg hCAB0 (norm_nonneg B))

/-- 一阶展开的二阶范数余项；界仅依赖已给出的传播子界。 -/
theorem norm_exp_first_order_remainder_le_of_bounds
    (A B : 𝔄) (t : ℝ) (ht : 0 ≤ t) (CA CAB : ℝ)
    (hA : ∀ s ∈ Icc (0 : ℝ) t, ‖exp (s • A)‖ ≤ CA)
    (hAB : ∀ s ∈ Icc (0 : ℝ) t, ‖exp (s • (A + B))‖ ≤ CAB) :
    ‖exp (t • (A + B)) - exp (t • A) - expFirstOrder A B t‖ ≤
      CA ^ 2 * CAB * ‖B‖ ^ 2 * t ^ 2 / 2 := by
  have hCA0 : 0 ≤ CA := (norm_nonneg _).trans (hA 0 ⟨le_rfl, ht⟩)
  have hkernel : ∀ s ∈ Icc (0 : ℝ) t,
      ‖exp ((t - s) • A) * B * (exp (s • (A + B)) - exp (s • A))‖ ≤
        (CA ^ 2 * CAB * ‖B‖ ^ 2) * s := by
    intro s hs
    have hfirst := norm_exp_add_sub_le_of_bounds A B s hs.1 CA CAB
      (fun r hr => hA r ⟨hr.1, hr.2.trans hs.2⟩)
      (fun r hr => hAB r ⟨hr.1, hr.2.trans hs.2⟩)
    have hsA := hA (t - s) ⟨sub_nonneg.mpr hs.2, by linarith [hs.1]⟩
    calc
      ‖exp ((t - s) • A) * B * (exp (s • (A + B)) - exp (s • A))‖
          ≤ ‖exp ((t - s) • A) * B‖ * ‖exp (s • (A + B)) - exp (s • A)‖ :=
        norm_mul_le _ _
      _ ≤ (CA * ‖B‖) * (CAB * ‖B‖ * CA * s) :=
        mul_le_mul ((norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right hsA (norm_nonneg B))) hfirst
          (norm_nonneg _) (mul_nonneg hCA0 (norm_nonneg B))
      _ = (CA ^ 2 * CAB * ‖B‖ ^ 2) * s := by ring
  rw [exp_first_order_remainder_eq_integral]
  calc
    ‖∫ s in (0 : ℝ)..t, exp ((t - s) • A) * B *
        (exp (s • (A + B)) - exp (s • A))‖
      ≤ ∫ s in (0 : ℝ)..t, (CA ^ 2 * CAB * ‖B‖ ^ 2) * s := by
        apply intervalIntegral.norm_integral_le_of_norm_le ht
        · exact Filter.Eventually.of_forall (fun s hs => hkernel s ⟨hs.1.le, hs.2⟩)
        · exact (continuous_const.mul continuous_id).intervalIntegrable 0 t
    _ = CA ^ 2 * CAB * ‖B‖ ^ 2 * t ^ 2 / 2 := by
      rw [intervalIntegral.integral_const_mul, integral_id]
      ring

/-- 在两个传播子均为压缩的条件下，二阶常数精确为二分之一。 -/
theorem norm_exp_first_order_remainder_le_of_contractions
    (A B : 𝔄) (t : ℝ) (ht : 0 ≤ t)
    (hA : ∀ s ∈ Icc (0 : ℝ) t, ‖exp (s • A)‖ ≤ 1)
    (hAB : ∀ s ∈ Icc (0 : ℝ) t, ‖exp (s • (A + B))‖ ≤ 1) :
    ‖exp (t • (A + B)) - exp (t • A) - expFirstOrder A B t‖ ≤
      ‖B‖ ^ 2 * t ^ 2 / 2 := by
  simpa only [one_pow, one_mul] using
    norm_exp_first_order_remainder_le_of_bounds A B t ht 1 1 hA hAB

section Matrices

open scoped Matrix.Norms.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- 该非交换定理确实实例化到有限维复矩阵，而非仅有未实例化的抽象接口。 -/
theorem matrix_exp_add_sub_exp_eq_integral (A B : Matrix n n ℂ) (t : ℝ) :
    exp (t • (A + B)) - exp (t • A) =
      ∫ s in (0 : ℝ)..t, exp ((t - s) • (A + B)) * B * exp (s • A) :=
  exp_add_sub_exp_eq_integral A B t

/-- 有限维复矩阵的精确二阶有序积分余项。 -/
theorem matrix_exp_first_order_remainder_eq_double_integral
    (A B : Matrix n n ℂ) (t : ℝ) :
    exp (t • (A + B)) - exp (t • A) - expFirstOrder A B t =
      ∫ s in (0 : ℝ)..t, ∫ r in (0 : ℝ)..s,
        exp ((t - s) • A) * B * exp ((s - r) • A) * B * exp (r • (A + B)) :=
  exp_first_order_remainder_eq_double_integral A B t

end Matrices

#print axioms hasDerivAt_duhamel_path
#print axioms exp_add_sub_exp_eq_integral
#print axioms exp_add_sub_exp_eq_integral_unit
#print axioms exp_add_sub_exp_eq_integral_right
#print axioms exp_first_order_remainder_eq_integral
#print axioms exp_first_order_remainder_eq_double_integral
#print axioms norm_exp_add_sub_le_of_bounds
#print axioms norm_exp_first_order_remainder_le_of_bounds
#print axioms norm_exp_first_order_remainder_le_of_contractions
#print axioms matrix_exp_add_sub_exp_eq_integral
#print axioms matrix_exp_first_order_remainder_eq_double_integral

end TwoStateQuantumEmbedding
