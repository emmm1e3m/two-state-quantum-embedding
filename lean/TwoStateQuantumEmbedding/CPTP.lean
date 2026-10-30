import TwoStateQuantumEmbedding.ExponentialRepresentation
import QICLean.Channel.Semigroup.LindbladForm.GKSLTheorem
import QICLean.Channel.CompletelyPositiveBridge
import Mathlib.Topology.Order.Compact

/-! 原模型的 GKSL 指数是 CPTP；原始概率闭包位于紧单位正方形中。 -/

noncomputable section
open Matrix Complex
open scoped BigOperators MatrixOrder ComplexOrder

namespace TwoStateQuantumEmbedding

/-- 保留原 Hamiltonian 和每个跳跃算符的 Lindblad 数据。 -/
def modelLindbladForm {n : ℕ} (H : QubitMatrix) (A : Fin n → QubitMatrix)
    (hH : H.IsHermitian) : LindbladForm 2 :=
  ⟨n, H, A, hH⟩

theorem model_dissipator_eq (A ρ : QubitMatrix) :
    dissipator A ρ = _root_.dissipator A ρ := by
  simp only [dissipator, _root_.dissipator, smul_add, Matrix.mul_assoc]
  abel

/-- 两种记法的 Hamiltonian 符号与反对易项系数严格一致。 -/
theorem gkslLinearMap_eq_lindbladForm {n : ℕ} (H : QubitMatrix)
    (A : Fin n → QubitMatrix) (hH : H.IsHermitian) :
    gkslLinearMap H A = (modelLindbladForm H A hH).toLinearMap := by
  ext1 ρ
  change gkslAction H A ρ =
    Complex.I • (ρ * H - H * ρ) + ∑ j : Fin n, _root_.dissipator (A j) ρ
  simp only [gkslAction, model_dissipator_eq, neg_smul, smul_sub]
  abel

theorem gkslSuperoperatorEvolution_toLinearMap_eq_expSemigroup {n : ℕ}
    (H : QubitMatrix) (A : Fin n → QubitMatrix) (t : ℝ) :
    (gkslSuperoperatorEvolution H A t).toLinearMap = expSemigroup (gkslLinearMap H A) t := by
  apply endEquiv.injective
  rw [expSemigroup_toCLM]
  rfl

/-- 任意有限跳跃数、Hermitian Hamiltonian 及非负时间的真实演化是 CPTP。 -/
theorem gkslSuperoperatorEvolution_isChannel {n : ℕ} (H : QubitMatrix)
    (A : Fin n → QubitMatrix) (t : ℝ) (hH : H.IsHermitian) (ht : 0 ≤ t) :
    IsChannel (gkslSuperoperatorEvolution H A t).toLinearMap := by
  rw [gkslSuperoperatorEvolution_toLinearMap_eq_expSemigroup]
  exact ((gksl_iff_lindbladForm (gkslLinearMap H A)).2
    ⟨modelLindbladForm H A hH, gkslLinearMap_eq_lindbladForm H A hH⟩) t ht

theorem gkslSuperoperatorEvolution_posSemidef {n : ℕ} (H : QubitMatrix)
    (A : Fin n → QubitMatrix) (t : ℝ) (hH : H.IsHermitian) (ht : 0 ≤ t)
    {ρ : QubitMatrix} (hρ : ρ.PosSemidef) :
    (gkslSuperoperatorEvolution H A t ρ).PosSemidef :=
  (gkslSuperoperatorEvolution_isChannel H A t hH ht).pos ρ hρ

theorem gkslSuperoperatorEvolution_trace {n : ℕ} (H : QubitMatrix)
    (A : Fin n → QubitMatrix) (t : ℝ) (hH : H.IsHermitian) (ht : 0 ≤ t)
    (ρ : QubitMatrix) :
    (gkslSuperoperatorEvolution H A t ρ).trace = ρ.trace :=
  (gkslSuperoperatorEvolution_isChannel H A t hH ht).tp ρ

/-- 与 mathlib 的所有辅助维度完全正性定义相接，而不只断言单系统正性。 -/
def gkslSuperoperatorEvolution_completelyPositiveMap {n : ℕ} (H : QubitMatrix)
    (A : Fin n → QubitMatrix) (t : ℝ) (hH : H.IsHermitian) (ht : 0 ≤ t) :
    CompletelyPositiveMap (CStarMatrix (Fin 2) (Fin 2) ℂ)
      (CStarMatrix (Fin 2) (Fin 2) ℂ) :=
  (gkslSuperoperatorEvolution_isChannel H A t hH ht).cp.toCompletelyPositiveMap

@[simp] theorem gkslSuperoperatorEvolution_completelyPositiveMap_apply {n : ℕ}
    (H : QubitMatrix) (A : Fin n → QubitMatrix) (t : ℝ)
    (hH : H.IsHermitian) (ht : 0 ≤ t) (ρ : QubitMatrix) :
    gkslSuperoperatorEvolution_completelyPositiveMap H A t hH ht ρ =
      gkslSuperoperatorEvolution H A t ρ := rfl

theorem basisProjector_posSemidef (i : Fin 2) :
    (Matrix.single i i (1 : ℂ) : QubitMatrix).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (Matrix.single i i (1 : ℂ) : QubitMatrix)
  simpa [Matrix.conjTranspose_single, Matrix.single_mul_single_same] using h

theorem basisProjector_trace (i : Fin 2) :
    (Matrix.single i i (1 : ℂ) : QubitMatrix).trace = 1 := by
  simp [Matrix.trace, Matrix.diag, Matrix.single_apply]

theorem density_diagonal_mem_Icc {ρ : QubitMatrix} (hρ : ρ.PosSemidef)
    (htrace : ρ.trace = 1) (i : Fin 2) : (ρ i i).re ∈ Set.Icc (0 : ℝ) 1 := by
  have hdiag : ∀ j, 0 ≤ (ρ j j).re := fun j =>
    (RCLike.nonneg_iff.mp (hρ.diag_nonneg (i := j))).1
  refine ⟨hdiag i, ?_⟩
  have hsum : ∑ j : Fin 2, (ρ j j).re = 1 := by
    simpa [Matrix.trace, Matrix.diag] using congrArg Complex.re htrace
  rw [← hsum]
  exact Finset.single_le_sum (fun j _ => hdiag j) (Finset.mem_univ i)

theorem gksl_basis_probability_mem_Icc {n : ℕ} (H : QubitMatrix)
    (A : Fin n → QubitMatrix) (t : ℝ) (hH : H.IsHermitian) (ht : 0 ≤ t)
    (i j : Fin 2) :
    (gkslSuperoperatorEvolution H A t (Matrix.single i i 1) j j).re ∈ Set.Icc (0 : ℝ) 1 := by
  apply density_diagonal_mem_Icc
  · exact gkslSuperoperatorEvolution_posSemidef H A t hH ht (basisProjector_posSemidef i)
  · rw [gkslSuperoperatorEvolution_trace H A t hH ht, basisProjector_trace]

theorem finiteOutput_mem_unitSquare {n : ℕ} (H : QubitMatrix)
    (A : Fin n → QubitMatrix) (t : ℝ) (hH : H.IsHermitian) (ht : 0 ≤ t) :
    finiteOutput H A t ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
  rw [finiteOutput_eq_superoperator_probabilities]
  exact ⟨gksl_basis_probability_mem_Icc H A t hH ht 0 0,
    gksl_basis_probability_mem_Icc H A t hH ht 1 1⟩

theorem finiteOutputs_subset_unitSquare :
    finiteOutputs ⊆ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
  rintro p ⟨n, H, A, t, hH, ht, rfl⟩
  exact finiteOutput_mem_unitSquare H A t hH ht

theorem Q2_subset_unitSquare :
    Q2 ⊆ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 :=
  closure_minimal finiteOutputs_subset_unitSquare (isClosed_Icc.prod isClosed_Icc)

theorem Q2_isCompact : IsCompact Q2 :=
  (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset Q2_isClosed Q2_subset_unitSquare

#print axioms gkslLinearMap_eq_lindbladForm
#print axioms model_dissipator_eq
#print axioms gkslSuperoperatorEvolution_toLinearMap_eq_expSemigroup
#print axioms gkslSuperoperatorEvolution_isChannel
#print axioms gkslSuperoperatorEvolution_posSemidef
#print axioms gkslSuperoperatorEvolution_trace
#print axioms gkslSuperoperatorEvolution_completelyPositiveMap
#print axioms gkslSuperoperatorEvolution_completelyPositiveMap_apply
#print axioms basisProjector_posSemidef
#print axioms basisProjector_trace
#print axioms density_diagonal_mem_Icc
#print axioms gksl_basis_probability_mem_Icc
#print axioms finiteOutput_mem_unitSquare
#print axioms finiteOutputs_subset_unitSquare
#print axioms Q2_subset_unitSquare
#print axioms Q2_isCompact

end TwoStateQuantumEmbedding
