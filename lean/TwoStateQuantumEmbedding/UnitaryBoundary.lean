import TwoStateQuantumEmbedding.Model
import TwoStateQuantumEmbedding.CPTP
import TwoStateQuantumEmbedding.CanonicalBloch
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! 实际酉旋转的指数解，以及真实概率切片的最小值接口。 -/

noncomputable section
open Matrix NormedSpace
open scoped Matrix.Norms.Operator ComplexOrder

namespace TwoStateQuantumEmbedding

section LinearODE
variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄]

/-- 常系数左乘方程的实际指数解；用积分因子证明，不假设解唯一性。 -/
theorem eq_exp_of_hasDerivAt_left (A : 𝔄) (F : ℝ → 𝔄)
    (h0 : F 0 = 1) (hF : ∀ t, HasDerivAt F (A * F t) t) (t : ℝ) :
    F t = exp (t • A) := by
  let : NormedAlgebra ℚ 𝔄 := NormedAlgebra.restrictScalars ℚ ℝ 𝔄
  let G : ℝ → 𝔄 := fun s => exp ((-s) • A) * F s
  have hG (s : ℝ) : HasDerivAt G 0 s := by
    have he : HasDerivAt (fun r : ℝ => exp ((-r) • A))
        (-(exp ((-s) • A) * A)) s := by
      simpa [Function.comp_def] using
        (hasDerivAt_exp_smul_const A (-s)).scomp s (hasDerivAt_id s).neg
    convert he.mul (hF s) using 1
    noncomm_ring
  have hc := is_const_of_deriv_eq_zero (fun s => (hG s).differentiableAt)
    (fun s => (hG s).deriv) t 0
  have hi : exp ((-t) • A) * F t = 1 := by
    simpa [G, h0, exp_zero] using hc
  have h := congrArg (fun x => exp (t • A) * x) hi
  have he : exp (t • A) * exp (-(t • A)) = 1 := by
    rw [← NormedSpace.exp_add_of_commute (Commute.refl (t • A)).neg_right,
      add_neg_cancel, exp_zero]
  simpa only [neg_smul, ← mul_assoc, he, one_mul, mul_one] using h
end LinearODE

def rotationGenerator4 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, -1; 0, 0, 1, 0]

def rotation4 (t : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0; 0, 1, 0, 0;
    0, 0, Real.cos t, -Real.sin t; 0, 0, Real.sin t, Real.cos t]

theorem rotation4_zero : rotation4 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [rotation4]

theorem rotation4_hasDerivAt (t : ℝ) :
    HasDerivAt rotation4 (rotationGenerator4 * rotation4 t) t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;>
    simp [rotation4, rotationGenerator4, Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals first | exact hasDerivAt_const t _ | exact Real.hasDerivAt_cos t |
    exact Real.hasDerivAt_sin t | exact (Real.hasDerivAt_sin t).neg

theorem exp_rotationGenerator4 (t : ℝ) :
    exp (t • rotationGenerator4) = rotation4 t :=
  (eq_exp_of_hasDerivAt_left rotationGenerator4 rotation4
    rotation4_zero rotation4_hasDerivAt t).symm

open GKSLAlgebra CanonicalBloch

theorem augmentedGenerator_x_zero (θ : ℝ) :
    augmentedGenerator ![θ, 0, 0] 0 = θ • rotationGenerator4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [augmentedGenerator, blochMatrix, crossMatrix, drift,
      rotationGenerator4, Matrix.trace, Matrix.diag]

theorem canonicalOutput_x_zero (θ t : ℝ) :
    canonicalOutput ![θ, 0, 0] 0 t =
      ((1 + Real.cos (t * θ)) / 2, (1 + Real.cos (t * θ)) / 2) := by
  simp [canonicalOutput, canonicalEvolution, augmentedGenerator_x_zero,
    smul_smul, exp_rotationGenerator4, rotation4]

/-- 每个酉直线点都由实际有限 Hamiltonian 实现，包含两端点。 -/
theorem diagonal_mem_canonicalOutputs {b : ℝ} (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    (b, b) ∈ canonicalOutputs := by
  refine ⟨![Real.arccos (2 * b - 1), 0, 0], 0, Matrix.PosSemidef.zero, ?_⟩
  rw [canonicalOutput_x_zero]
  have h1 : -1 ≤ 2 * b - 1 := by linarith [hb.1]
  have h2 : 2 * b - 1 ≤ 1 := by linarith [hb.2]
  simp only [one_mul, Real.cos_arccos h1 h2]
  congr 1 <;> ring

theorem diagonal_mem_Q2 {b : ℝ} (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    (b, b) ∈ Q2 := by
  rw [Q2_eq_closure_canonicalOutputs]
  exact subset_closure (diagonal_mem_canonicalOutputs hb)

/-- 下边界从真实可达闭包的切片定义，不使用候选解析分支。 -/
def lowerSlice (b : ℝ) : Set ℝ := {a | (a, b) ∈ Q2}

def lowerBoundary (b : ℝ) : ℝ := sInf (lowerSlice b)

theorem lowerSlice_isCompact (b : ℝ) : IsCompact (lowerSlice b) := by
  apply isCompact_Icc.of_isClosed_subset
    (Q2_isClosed.preimage (continuous_id.prodMk continuous_const))
  intro a ha
  exact (Q2_subset_unitSquare ha).1

theorem lowerSlice_nonempty {b : ℝ} (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    (lowerSlice b).Nonempty := ⟨b, diagonal_mem_Q2 hb⟩

theorem lowerBoundary_isLeast {b : ℝ} (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    IsLeast (lowerSlice b) (lowerBoundary b) :=
  (lowerSlice_isCompact b).isLeast_sInf (lowerSlice_nonempty hb)

theorem lowerBoundary_mem_Q2 {b : ℝ} (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    (lowerBoundary b, b) ∈ Q2 := (lowerBoundary_isLeast hb).1

theorem lowerBoundary_le_of_mem {a b : ℝ} (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hp : (a, b) ∈ Q2) : lowerBoundary b ≤ a :=
  (lowerBoundary_isLeast hb).2 hp

theorem lowerBoundary_bounds {b : ℝ} (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ lowerBoundary b ∧ lowerBoundary b ≤ b :=
  ⟨(Q2_subset_unitSquare (lowerBoundary_mem_Q2 hb)).1.1,
    lowerBoundary_le_of_mem hb (diagonal_mem_Q2 hb)⟩

theorem lowerBoundary_zero : lowerBoundary 0 = 0 := by
  have h := lowerBoundary_bounds (b := 0) (by constructor <;> norm_num)
  exact le_antisymm h.2 h.1

/-- 真实边界点保留原问题的任意精度、无参数统一上界的逼近量词。 -/
theorem lowerBoundary_approx {b : ℝ} (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (H : TwoStateQuantumEmbedding.QubitMatrix)
      (A : Fin n → TwoStateQuantumEmbedding.QubitMatrix) (t : ℝ),
      H.IsHermitian ∧ 0 ≤ t ∧
      |(finiteOutput H A t).1 - lowerBoundary b| < ε ∧
      |(finiteOutput H A t).2 - b| < ε :=
  (mem_Q2_iff_approx _).mp (lowerBoundary_mem_Q2 hb) ε hε

#print axioms eq_exp_of_hasDerivAt_left
#print axioms exp_rotationGenerator4
#print axioms diagonal_mem_Q2
#print axioms lowerBoundary_isLeast
#print axioms lowerBoundary_mem_Q2
#print axioms lowerBoundary_approx

end TwoStateQuantumEmbedding
