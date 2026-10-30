import TwoStateQuantumEmbedding.Duhamel
import TwoStateQuantumEmbedding.CanonicalBloch
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Tactic

/-! 从真实 Duhamel 二次余项推出矩阵指数的 Fréchet 导数。 -/
noncomputable section
open NormedSpace MeasureTheory Set Filter
open scoped Topology Interval Matrix.Norms.Operator

namespace TwoStateQuantumEmbedding.ExponentialGradient

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄]
  [CompleteSpace 𝔄] [FiniteDimensional ℝ 𝔄]

/-- Duhamel 一阶项关于扰动的连续线性映射。 -/
def expDerivative (A : 𝔄) : 𝔄 →L[ℝ] 𝔄 :=
  LinearMap.toContinuousLinearMap {
    toFun := fun B => expFirstOrder A B 1
    map_add' := by
      intro B C
      simp only [expFirstOrder, mul_add, add_mul]
      exact intervalIntegral.integral_add
        ((continuous_duhamel_kernel A A B 1).intervalIntegrable _ _)
        ((continuous_duhamel_kernel A A C 1).intervalIntegrable _ _)
    map_smul' := by
      intro r B
      simp [expFirstOrder]
  }

@[simp] theorem expDerivative_apply (A B : 𝔄) :
    expDerivative A B =
      ∫ s in (0 : ℝ)..1, exp ((1-s) • A) * B * exp (s • A) := rfl

/-- 指数在单位邻域的一致二次余项；常数不依赖扰动方向。 -/
theorem exists_quadratic_remainder_bound (A : 𝔄) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : 𝔄, ‖B‖ < 1 →
      ‖exp (A+B) - exp A - expDerivative A B‖ ≤ C * ‖B‖^2 := by
  obtain ⟨c, hc⟩ := (isCompact_closedBall (0 : 𝔄) (‖A‖+1)).exists_bound_of_continuousOn
    ((continuous_iff_continuousAt.mpr fun X =>
      (exp_analytic (𝕂 := ℝ) X).continuousAt).continuousOn :
        ContinuousOn (exp : 𝔄 → 𝔄) _)
  let C := max c 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hb : ∀ X : 𝔄, ‖X‖ ≤ ‖A‖+1 → ‖exp X‖ ≤ C := by
    intro X hX
    exact (hc X (by simpa [Metric.mem_closedBall, dist_zero_right] using hX)).trans
      (le_max_left _ _)
  refine ⟨C^3/2, by positivity, ?_⟩
  intro B hB
  have hs : ∀ s ∈ Icc (0 : ℝ) 1, ‖s • A‖ ≤ ‖A‖+1 := by
    intro s hs
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact (mul_le_of_le_one_left (norm_nonneg A) hs.2).trans (by linarith)
  have hsB : ∀ s ∈ Icc (0 : ℝ) 1, ‖s • (A+B)‖ ≤ ‖A‖+1 := by
    intro s hs
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
    calc
      s * ‖A+B‖ ≤ ‖A+B‖ := mul_le_of_le_one_left (norm_nonneg _) hs.2
      _ ≤ ‖A‖+‖B‖ := norm_add_le _ _
      _ ≤ ‖A‖+1 := by linarith
  have hr := norm_exp_first_order_remainder_le_of_bounds A B 1 (by norm_num) C C
    (fun s ht => hb _ (hs s ht)) (fun s ht => hb _ (hsB s ht))
  change ‖exp (A+B) - exp A - expFirstOrder A B 1‖ ≤ _
  calc
    _ ≤ C^2*C*‖B‖^2/2 := by simpa only [one_smul, one_pow, mul_one] using hr
    _ = _ := by ring

/-- 任意有限维实 Banach 代数中的真实 Fréchet 导数。 -/
theorem hasFDerivAt_exp_integral (A : 𝔄) :
    HasFDerivAt (exp : 𝔄 → 𝔄) (expDerivative A) A := by
  obtain ⟨C, hC, hb⟩ := exists_quadratic_remainder_bound A
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  have hn : ∀ᶠ B : 𝔄 in 𝓝 0, ‖B‖ < min 1 (ε/C) := by
    exact (Metric.eventually_nhds_iff.mpr ⟨min 1 (ε/C), by positivity,
      fun B hB => by simpa [dist_zero_right] using hB⟩)
  filter_upwards [hn] with B hB
  have h1 : ‖B‖ < 1 := lt_of_lt_of_le hB (min_le_left _ _)
  have hεB : C * ‖B‖ ≤ ε := by
    have := lt_of_lt_of_le hB (min_le_right _ _)
    have := (lt_div_iff₀ hC).mp this
    nlinarith
  exact (hb B h1).trans (by nlinarith [norm_nonneg B])

theorem fderiv_exp_apply (A B : 𝔄) :
    fderiv ℝ (exp : 𝔄 → 𝔄) A B =
      ∫ s in (0 : ℝ)..1, exp ((1-s) • A) * B * exp (s • A) := by
  rw [(hasFDerivAt_exp_integral A).fderiv]
  rfl

/-- 解析性同时将上述具体导数升级为严格导数。 -/
theorem hasStrictFDerivAt_exp_integral (A : 𝔄) :
    HasStrictFDerivAt (exp : 𝔄 → 𝔄) (expDerivative A) A := by
  simpa only [(hasFDerivAt_exp_integral A).fderiv] using
    (exp_analytic (𝕂 := ℝ) A).hasStrictFDerivAt

section MatrixSubmersion
open Matrix
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- 方向 exp(-M) 使矩阵指数的一阶变化恰为单位矩阵。 -/
theorem expDerivative_exp_neg (M : Matrix n n ℝ) :
    expDerivative M (exp (-M)) = 1 := by
  rw [expDerivative_apply]
  have hkernel : (fun s : ℝ => exp ((1-s) • M) * exp (-M) * exp (s • M)) =
      (fun _ : ℝ => (1 : Matrix n n ℝ)) := by
    funext s
    rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl M).smul_left (1-s)).neg_right)]
    have hm : (1-s) • M + -M = (-s) • M := by module
    rw [hm, ← Matrix.exp_add_of_commute _ _ (((Commute.refl M).smul_left (-s)).smul_right s)]
    rw [show (-s) • M + s • M = 0 by module, exp_zero]
  change intervalIntegral (fun s : ℝ => exp ((1-s) • M) * exp (-M) * exp (s • M))
    0 1 MeasureTheory.volume = 1
  rw [hkernel]
  simp

def matrixEntryCLM (i j : n) : Matrix n n ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun M => M i j
    map_add' := by intros; rfl
    map_smul' := by intros; rfl
  }

/-- 真实标量函数 (exp M)ᵢᵢ 的指定方向导数为 1。 -/
theorem fderiv_exp_diagonal_exp_neg (M : Matrix n n ℝ) (i : n) :
    fderiv ℝ (fun Q : Matrix n n ℝ => exp Q i i) M (exp (-M)) = 1 := by
  have h := (matrixEntryCLM i i).hasFDerivAt.comp M (hasFDerivAt_exp_integral M)
  change fderiv ℝ (⇑(matrixEntryCLM i i) ∘ exp) M (exp (-M)) = 1
  rw [h.fderiv]
  change expDerivative M (exp (-M)) i i = 1
  rw [expDerivative_exp_neg]
  simp
end MatrixSubmersion

section Canonical
open CanonicalBloch GKSLAlgebra

abbrev Parameters := BlochVec × Matrix (Fin 3) (Fin 3) ℂ

/-- 实际规范参数到真实增广 Bloch 生成元的实线性映射。 -/
def canonicalGeneratorCLM : Parameters →L[ℝ] AugmentedMatrix :=
  LinearMap.toContinuousLinearMap {
    toFun := fun p => augmentedGenerator p.1 p.2
    map_add' := by
      intro p q
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [augmentedGenerator, blochMatrix, crossMatrix, drift, Matrix.trace,
          Fin.sum_univ_three, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] <;> ring
    map_smul' := by
      intro r p
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [augmentedGenerator, blochMatrix, crossMatrix, drift, Matrix.trace,
          Fin.sum_univ_three, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] <;> ring
  }

@[simp] theorem canonicalGeneratorCLM_apply (p : Parameters) :
    canonicalGeneratorCLM p = augmentedGenerator p.1 p.2 := rfl

/-- 加权测量矩阵元，权重分别对应 x 与 z。 -/
def measurementCLM (α β : ℝ) : AugmentedMatrix →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun Q => α * Q 3 3 + β * Q 3 0
    map_add' := by intro Q R; simp; ring
    map_smul' := by intro r Q; simp [Matrix.smul_apply, smul_eq_mul]; ring
  }

def canonicalScalar (α β : ℝ) (p : Parameters) : ℝ :=
  let ab := canonicalOutput p.1 p.2 1
  α * (ab.1 + ab.2 - 1) + β * (ab.1 - ab.2)

theorem canonicalScalar_eq (α β : ℝ) (p : Parameters) :
    canonicalScalar α β p = measurementCLM α β (exp (canonicalGeneratorCLM p)) := by
  simp only [canonicalScalar, canonicalOutput, canonicalEvolution, one_smul,
    measurementCLM, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, canonicalGeneratorCLM_apply]
  ring

/-- 对实际输出 αx+βz 的具体 Fréchet 导数。 -/
def canonicalScalarDerivative (α β : ℝ) (p : Parameters) : Parameters →L[ℝ] ℝ :=
  (measurementCLM α β).comp ((expDerivative (canonicalGeneratorCLM p)).comp
    canonicalGeneratorCLM)

theorem hasStrictFDerivAt_canonicalScalar (α β : ℝ) (p : Parameters) :
    HasStrictFDerivAt (canonicalScalar α β) (canonicalScalarDerivative α β p) p := by
  have h := (measurementCLM α β).hasStrictFDerivAt.comp p
    ((hasStrictFDerivAt_exp_integral (canonicalGeneratorCLM p)).comp p
      canonicalGeneratorCLM.hasStrictFDerivAt)
  rw [show canonicalScalar α β = (fun q => measurementCLM α β
    (exp (canonicalGeneratorCLM q))) from funext (canonicalScalar_eq α β)]
  exact h

theorem canonicalScalarDerivative_apply (α β : ℝ) (p v : Parameters) :
    canonicalScalarDerivative α β p v =
      measurementCLM α β
        (∫ s in (0 : ℝ)..1,
          exp ((1-s) • augmentedGenerator p.1 p.2) *
            augmentedGenerator v.1 v.2 * exp (s • augmentedGenerator p.1 p.2)) := rfl

theorem hasStrictFDerivAt_canonical_a (p : Parameters) :
    HasStrictFDerivAt (fun p : Parameters => (canonicalOutput p.1 p.2 1).1)
      (canonicalScalarDerivative (1/2) (1/2) p) p := by
  have h := (hasStrictFDerivAt_canonicalScalar (1/2) (1/2) p).add_const (1/2)
  have heq : (fun q : Parameters => (canonicalOutput q.1 q.2 1).1) =
      (fun q => canonicalScalar (1/2) (1/2) q + 1/2) := by
    funext q
    simp only [canonicalScalar]
    ring
  rw [heq]
  exact h

theorem hasStrictFDerivAt_canonical_b (p : Parameters) :
    HasStrictFDerivAt (fun p : Parameters => (canonicalOutput p.1 p.2 1).2)
      (canonicalScalarDerivative (1/2) (-1/2) p) p := by
  have h := (hasStrictFDerivAt_canonicalScalar (1/2) (-1/2) p).add_const (1/2)
  have heq : (fun q : Parameters => (canonicalOutput q.1 q.2 1).2) =
      (fun q => canonicalScalar (1/2) (-1/2) q + 1/2) := by
    funext q
    simp only [canonicalScalar]
    ring
  rw [heq]
  exact h

end Canonical

#print axioms hasFDerivAt_exp_integral
#print axioms fderiv_exp_apply
#print axioms hasStrictFDerivAt_canonicalScalar
#print axioms hasStrictFDerivAt_canonical_a
#print axioms hasStrictFDerivAt_canonical_b
#print axioms fderiv_exp_diagonal_exp_neg
end TwoStateQuantumEmbedding.ExponentialGradient
