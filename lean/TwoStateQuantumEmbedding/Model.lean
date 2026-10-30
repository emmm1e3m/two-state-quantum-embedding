import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic

/-! 原始问题模型：固定同一基、任意有限跳跃数、有限非负演化时间及概率闭包。 -/

noncomputable section
open Matrix Complex
open scoped BigOperators

namespace TwoStateQuantumEmbedding

abbrev QubitMatrix := Matrix (Fin 2) (Fin 2) ℂ
abbrev LiouvilleIndex := Fin 2 × Fin 2
abbrev LiouvilleMatrix := Matrix LiouvilleIndex LiouvilleIndex ℂ

def dissipator (A ρ : QubitMatrix) : QubitMatrix :=
  A * ρ * A.conjTranspose - (1 / 2 : ℂ) •
    (A.conjTranspose * A * ρ + ρ * A.conjTranspose * A)

def gkslAction {n : ℕ} (H : QubitMatrix) (A : Fin n → QubitMatrix)
    (ρ : QubitMatrix) : QubitMatrix :=
  (-Complex.I) • (H * ρ - ρ * H) + ∑ μ, dissipator (A μ) ρ

/-- 用矩阵单位表示超算子；行、列的第一分量分别为密度矩阵行索引。 -/
def actionMatrix (f : QubitMatrix → QubitMatrix) : LiouvilleMatrix :=
  fun ij kl => f (Matrix.single kl.1 kl.2 1) ij.1 ij.2

def gkslMatrix {n : ℕ} (H : QubitMatrix) (A : Fin n → QubitMatrix) :
    LiouvilleMatrix := actionMatrix (gkslAction H A)

def finiteEvolution {n : ℕ} (H : QubitMatrix) (A : Fin n → QubitMatrix)
    (t : ℝ) : LiouvilleMatrix := NormedSpace.exp (t • gkslMatrix H A)

def finiteOutput {n : ℕ} (H : QubitMatrix) (A : Fin n → QubitMatrix)
    (t : ℝ) : ℝ × ℝ :=
  let E := finiteEvolution H A t
  ((E (0, 0) (0, 0)).re, (E (1, 1) (1, 1)).re)

def finiteOutputs : Set (ℝ × ℝ) :=
  {p | ∃ (n : ℕ) (H : QubitMatrix) (A : Fin n → QubitMatrix) (t : ℝ),
    H.IsHermitian ∧ 0 ≤ t ∧ finiteOutput H A t = p}

def Q2 : Set (ℝ × ℝ) := closure finiteOutputs

def unitTimeOutputs : Set (ℝ × ℝ) :=
  {p | ∃ (n : ℕ) (H : QubitMatrix) (A : Fin n → QubitMatrix),
    H.IsHermitian ∧ finiteOutput H A 1 = p}

theorem Q2_isClosed : IsClosed Q2 := isClosed_closure

theorem finiteOutput_mem_Q2 {n : ℕ} (H : QubitMatrix)
    (A : Fin n → QubitMatrix) (t : ℝ) (hH : H.IsHermitian) (ht : 0 ≤ t) :
    finiteOutput H A t ∈ Q2 :=
  subset_closure ⟨n, H, A, t, hH, ht, rfl⟩

theorem finiteOutput_zero {n : ℕ} (H : QubitMatrix)
    (A : Fin n → QubitMatrix) : finiteOutput H A 0 = (1, 1) := by
  simp [finiteOutput, finiteEvolution, NormedSpace.exp_zero]

theorem unitTimeOutputs_subset_finiteOutputs : unitTimeOutputs ⊆ finiteOutputs := by
  rintro p ⟨n, H, A, hH, hp⟩
  exact ⟨n, H, A, 1, hH, by norm_num, hp⟩

theorem dissipator_real_smul (A ρ : QubitMatrix) (s : ℝ) :
    dissipator (s • A) ρ = (s * s) • dissipator A ρ := by
  simp only [dissipator, Matrix.conjTranspose_smul, star_trivial,
    Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_add, smul_smul]
  module

theorem gkslAction_time_scaling {n : ℕ} (H : QubitMatrix)
    (A : Fin n → QubitMatrix) (ρ : QubitMatrix) (t : ℝ) (ht : 0 ≤ t) :
    gkslAction (t • H) (fun μ => Real.sqrt t • A μ) ρ =
      t • gkslAction H A ρ := by
  simp only [gkslAction, dissipator_real_smul, Real.mul_self_sqrt ht,
    Matrix.smul_mul, Matrix.mul_smul, ← Finset.smul_sum, smul_sub, smul_add]
  module

theorem gkslMatrix_time_scaling {n : ℕ} (H : QubitMatrix)
    (A : Fin n → QubitMatrix) (t : ℝ) (ht : 0 ≤ t) :
    gkslMatrix (t • H) (fun μ => Real.sqrt t • A μ) = t • gkslMatrix H A := by
  ext ij kl
  simp only [gkslMatrix, actionMatrix, gkslAction_time_scaling H A _ t ht]
  rfl

theorem finiteOutput_time_normalization {n : ℕ} (H : QubitMatrix)
    (A : Fin n → QubitMatrix) (t : ℝ) (ht : 0 ≤ t) :
    finiteOutput (t • H) (fun μ => Real.sqrt t • A μ) 1 = finiteOutput H A t := by
  simp only [finiteOutput, finiteEvolution, gkslMatrix_time_scaling H A t ht, one_smul]

theorem finiteOutputs_subset_unitTimeOutputs : finiteOutputs ⊆ unitTimeOutputs := by
  rintro p ⟨n, H, A, t, hH, ht, hp⟩
  refine ⟨n, t • H, (fun μ => Real.sqrt t • A μ), ?_, ?_⟩
  · simp only [Matrix.IsHermitian, Matrix.conjTranspose_smul, star_trivial, hH.eq]
  · exact (finiteOutput_time_normalization H A t ht).trans hp

theorem finiteOutputs_eq_unitTimeOutputs : finiteOutputs = unitTimeOutputs :=
  Set.Subset.antisymm finiteOutputs_subset_unitTimeOutputs unitTimeOutputs_subset_finiteOutputs

/-- 包括零时间在内，时间归一化精确保留原始概率闭包。 -/
theorem Q2_eq_closure_unitTimeOutputs : Q2 = closure unitTimeOutputs := by
  rw [Q2, finiteOutputs_eq_unitTimeOutputs]

/-- 概率闭包等价于原问题的任意精度、无统一参数界的逼近量词。 -/
theorem mem_Q2_iff_approx (p : ℝ × ℝ) : p ∈ Q2 ↔
    ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (H : QubitMatrix)
      (A : Fin n → QubitMatrix) (t : ℝ), H.IsHermitian ∧ 0 ≤ t ∧
      |(finiteOutput H A t).1 - p.1| < ε ∧
      |(finiteOutput H A t).2 - p.2| < ε := by
  rw [Q2, Metric.mem_closure_iff]
  constructor
  · intro h ε hε
    obtain ⟨q, ⟨n, H, A, t, hH, ht, hp⟩, hd⟩ := h ε hε
    refine ⟨n, H, A, t, hH, ht, ?_⟩
    rw [hp]
    rw [dist_comm] at hd
    simpa only [Prod.dist_eq, Real.dist_eq, max_lt_iff] using hd
  · intro h ε hε
    obtain ⟨n, H, A, t, hH, ht, ha, hb⟩ := h ε hε
    refine ⟨finiteOutput H A t, ⟨n, H, A, t, hH, ht, rfl⟩, ?_⟩
    rw [dist_comm]
    simpa only [Prod.dist_eq, Real.dist_eq, max_lt_iff] using And.intro ha hb

theorem gkslAction_add {n : ℕ} (H : QubitMatrix) (A : Fin n → QubitMatrix)
    (ρ σ : QubitMatrix) : gkslAction H A (ρ + σ) =
      gkslAction H A ρ + gkslAction H A σ := by
  simp only [gkslAction, dissipator, Matrix.mul_add, Matrix.add_mul, smul_add]
  simp only [add_add_add_comm, add_sub_add_comm, Finset.sum_add_distrib]
  simp only [smul_add]

theorem gkslAction_complex_smul {n : ℕ} (H : QubitMatrix)
    (A : Fin n → QubitMatrix) (ρ : QubitMatrix) (c : ℂ) :
    gkslAction H A (c • ρ) = c • gkslAction H A ρ := by
  simp only [gkslAction, dissipator, Matrix.smul_mul, Matrix.mul_smul,
    ← smul_add, ← smul_sub, smul_comm (1 / 2 : ℂ) c, ← Finset.smul_sum]
  module

def gkslLinearMap {n : ℕ} (H : QubitMatrix) (A : Fin n → QubitMatrix) :
    QubitMatrix →ₗ[ℂ] QubitMatrix where
  toFun := gkslAction H A
  map_add' := gkslAction_add H A
  map_smul' := fun c ρ => gkslAction_complex_smul H A ρ c

theorem qubit_matrix_units_decomposition (ρ : QubitMatrix) :
    (∑ kl : LiouvilleIndex, ρ kl.1 kl.2 • Matrix.single kl.1 kl.2 (1 : ℂ)) = ρ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.single_apply,
      Matrix.sum_apply]

/-- 超算子矩阵确实表示原始线性作用，而非仅给出了形式上的系数数组。 -/
theorem actionMatrix_mulVec (f : QubitMatrix →ₗ[ℂ] QubitMatrix) (ρ : QubitMatrix) :
    actionMatrix f *ᵥ (fun ij => ρ ij.1 ij.2) = fun ij => f ρ ij.1 ij.2 := by
  funext ij
  have h := congrArg (fun τ : QubitMatrix => f τ ij.1 ij.2)
    (qubit_matrix_units_decomposition ρ)
  simpa only [actionMatrix, Matrix.mulVec, dotProduct, map_sum, map_smul,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_comm] using h

theorem gkslMatrix_mulVec {n : ℕ} (H : QubitMatrix)
    (A : Fin n → QubitMatrix) (ρ : QubitMatrix) :
    gkslMatrix H A *ᵥ (fun ij => ρ ij.1 ij.2) =
      fun ij => gkslAction H A ρ ij.1 ij.2 :=
  actionMatrix_mulVec (gkslLinearMap H A) ρ

theorem finiteEvolution_zero {n : ℕ} (H : QubitMatrix)
    (A : Fin n → QubitMatrix) : finiteEvolution H A 0 = 1 := by
  simp [finiteEvolution, NormedSpace.exp_zero]

/-- 同一个时间不变生成元的指数满足真正的半群恒等式。 -/
theorem finiteEvolution_add {n : ℕ} (H : QubitMatrix)
    (A : Fin n → QubitMatrix) (s t : ℝ) :
    finiteEvolution H A (s + t) = finiteEvolution H A s * finiteEvolution H A t := by
  unfold finiteEvolution
  rw [add_smul]
  apply Matrix.exp_add_of_commute
  change (s • gkslMatrix H A) * (t • gkslMatrix H A) =
    (t • gkslMatrix H A) * (s • gkslMatrix H A)
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm]

theorem finiteEvolution_nat_mul {n : ℕ} (H : QubitMatrix)
    (A : Fin n → QubitMatrix) (t : ℝ) (m : ℕ) :
    finiteEvolution H A ((m : ℝ) * t) = (finiteEvolution H A t) ^ m := by
  induction m with
  | zero => simp [finiteEvolution_zero]
  | succ m ih =>
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul,
        finiteEvolution_add, ih, pow_succ]

/-- 任一有限阶根来自同一个生成元的相同短时段，不引入分段控制。 -/
theorem finiteEvolution_identical_root {n : ℕ} (H : QubitMatrix)
    (A : Fin n → QubitMatrix) (t : ℝ) (m : ℕ) (hm : m ≠ 0) :
    (finiteEvolution H A (t / m)) ^ m = finiteEvolution H A t := by
  rw [← finiteEvolution_nat_mul]
  congr 1
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  field_simp

section Continuity
open scoped Matrix.Norms.Operator

@[fun_prop]
theorem continuous_gkslMatrix (n : ℕ) :
    Continuous (fun p : QubitMatrix × (Fin n → QubitMatrix) => gkslMatrix p.1 p.2) := by
  unfold gkslMatrix actionMatrix gkslAction dissipator
  fun_prop

theorem continuous_finiteOutput (n : ℕ) :
    Continuous (fun p : QubitMatrix × (Fin n → QubitMatrix) × ℝ =>
      finiteOutput p.1 p.2.1 p.2.2) := by
  unfold finiteOutput finiteEvolution
  fun_prop

end Continuity

#print axioms finiteOutput_zero
#print axioms finiteOutput_mem_Q2
#print axioms Q2_eq_closure_unitTimeOutputs
#print axioms gkslMatrix_mulVec
#print axioms continuous_finiteOutput
#print axioms finiteEvolution_add
#print axioms mem_Q2_iff_approx
#print axioms finiteEvolution_identical_root

end TwoStateQuantumEmbedding
