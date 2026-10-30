import TwoStateQuantumEmbedding.CPTP

/-! 原始四项测量概率的任意精度闭包定义。 -/

noncomputable section
open Matrix Complex
open scoped ComplexOrder MatrixOrder

namespace TwoStateQuantumEmbedding.OriginalProblem
open TwoStateQuantumEmbedding

/-- 原定义的行是测量输出，列是制备输入。 -/
def probability {n : ℕ} (H : QubitMatrix) (A : Fin n → QubitMatrix)
    (t : ℝ) (i j : Fin 2) : ℝ :=
  (gkslSuperoperatorEvolution H A t (Matrix.single j j 1) i i).re

def table (p : ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![p.1, 1 - p.2; 1 - p.1, p.2]

/-- 取实部没有丢弃信息：合法演化的概率对角元确为实数。 -/
theorem probability_is_real {n : ℕ} (H : QubitMatrix) (A : Fin n → QubitMatrix)
    (t : ℝ) (hH : H.IsHermitian) (ht : 0 ≤ t) (i j : Fin 2) :
    gkslSuperoperatorEvolution H A t (Matrix.single j j 1) i i =
      (probability H A t i j : ℂ) := by
  have hpos := gkslSuperoperatorEvolution_posSemidef H A t hH ht (basisProjector_posSemidef j)
  apply Complex.ext
  · rfl
  · exact (RCLike.nonneg_iff.mp (hpos.diag_nonneg (i := i))).2

/-- 由真实保迹性恢复另外两条概率，不额外假定列随机性。 -/
theorem all_four_probabilities {n : ℕ} (H : QubitMatrix) (A : Fin n → QubitMatrix)
    (t : ℝ) (hH : H.IsHermitian) (ht : 0 ≤ t) (i j : Fin 2) :
    probability H A t i j = table (finiteOutput H A t) i j := by
  have h0 : probability H A t 0 0 + probability H A t 1 0 = 1 := by
    have hx := gkslSuperoperatorEvolution_trace H A t hH ht (Matrix.single 0 0 1)
    rw [basisProjector_trace] at hx
    simpa [probability, Matrix.trace, Fin.sum_univ_two] using congrArg Complex.re hx
  have h1 : probability H A t 0 1 + probability H A t 1 1 = 1 := by
    have hx := gkslSuperoperatorEvolution_trace H A t hH ht (Matrix.single 1 1 1)
    rw [basisProjector_trace] at hx
    simpa [probability, Matrix.trace, Fin.sum_univ_two] using congrArg Complex.re hx
  rw [finiteOutput_eq_superoperator_probabilities]
  change probability H A t i j =
    table (probability H A t 0 0, probability H A t 1 1) i j
  fin_cases i <;> fin_cases j <;> simp [table] <;> linarith

theorem table_error_le {p q : ℝ × ℝ} {δ : ℝ}
    (ha : |p.1 - q.1| ≤ δ) (hb : |p.2 - q.2| ≤ δ) (i j : Fin 2) :
    |table p i j - table q i j| ≤ δ := by
  fin_cases i <;> fin_cases j
  · exact ha
  · change |(1 - p.2) - (1 - q.2)| ≤ δ
    simpa only [sub_sub_sub_cancel_left, abs_sub_comm] using hb
  · change |(1 - p.1) - (1 - q.1)| ≤ δ
    simpa only [sub_sub_sub_cancel_left, abs_sub_comm] using ha
  · exact hb

/-- 精确核对原文任意精度、四个概率、非严格误差及原始所有有限 GKSL 的量词。 -/
theorem original_Q2_four_entry_iff (p : ℝ × ℝ) : p ∈ Q2 ↔
    ∀ δ : ℝ, 0 < δ → ∃ (n : ℕ) (H : QubitMatrix)
      (A : Fin n → QubitMatrix) (t : ℝ), H.IsHermitian ∧ 0 ≤ t ∧
      ∀ i j : Fin 2, |table p i j - probability H A t i j| ≤ δ := by
  rw [mem_Q2_iff_approx]
  constructor
  · intro h δ hδ
    obtain ⟨n, H, A, t, hH, ht, ha, hb⟩ := h δ hδ
    refine ⟨n, H, A, t, hH, ht, ?_⟩
    intro i j
    rw [all_four_probabilities H A t hH ht, abs_sub_comm]
    exact table_error_le ha.le hb.le i j
  · intro h ε hε
    obtain ⟨n, H, A, t, hH, ht, herr⟩ := h (ε / 2) (half_pos hε)
    refine ⟨n, H, A, t, hH, ht, ?_, ?_⟩
    · have hz := herr 0 0
      rw [all_four_probabilities H A t hH ht] at hz
      have hz' : |(finiteOutput H A t).1 - p.1| ≤ ε / 2 := by
        simpa [table, abs_sub_comm] using hz
      exact lt_of_le_of_lt hz' (half_lt_self hε)
    · have ho := herr 1 1
      rw [all_four_probabilities H A t hH ht] at ho
      have ho' : |(finiteOutput H A t).2 - p.2| ≤ ε / 2 := by
        simpa [table, abs_sub_comm] using ho
      exact lt_of_le_of_lt ho' (half_lt_self hε)

#print axioms probability_is_real
#print axioms all_four_probabilities
#print axioms original_Q2_four_entry_iff

end TwoStateQuantumEmbedding.OriginalProblem
