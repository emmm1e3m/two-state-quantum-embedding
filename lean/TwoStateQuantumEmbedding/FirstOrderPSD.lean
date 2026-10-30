import TwoStateQuantumEmbedding.FirstOrderBridge

noncomputable section
open Matrix Complex NormedSpace MeasureTheory
open scoped Interval ComplexOrder Matrix.Norms.L2Operator
namespace TwoStateQuantumEmbedding.SwapComparison
open GKSLAlgebra CanonicalBloch GKSLBounds
set_option maxHeartbeats 1000000

/-- 耗散算符对真实 Hermitian 参数的线性性。 -/
theorem dissipativeCLM_add (K L : Matrix (Fin 3) (Fin 3) ℂ) :
    dissipativeCLM (K+L)=dissipativeCLM K+dissipativeCLM L := by
  apply augmentedMatrixEquiv.injective
  rw [map_add, ← canonicalCLM_zero, ← canonicalCLM_zero, ← canonicalCLM_zero]
  simp only [canonicalCLM, AlgEquiv.apply_symm_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [augmentedGenerator, blochMatrix, crossMatrix, drift, Matrix.trace,
      Fin.sum_univ_succ, Matrix.smul_apply, smul_eq_mul] <;> ring

theorem expFirstOrder_add {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] (Q B C : A) (t : ℝ) :
    expFirstOrder Q (B+C) t=expFirstOrder Q B t+expFirstOrder Q C t := by
  unfold expFirstOrder
  simp only [mul_add, add_mul]
  exact intervalIntegral.integral_add
    ((continuous_duhamel_kernel Q Q B t).intervalIntegrable 0 t)
    ((continuous_duhamel_kernel Q Q C t).intervalIntegrable 0 t)

theorem firstOrderReturn_add (h : BlochVec)
    (K L : Matrix (Fin 3) (Fin 3) ℂ) (t s : ℝ) :
    firstOrderReturn h (K+L) t s=firstOrderReturn h K t s+firstOrderReturn h L t s := by
  simp [firstOrderReturn, dissipativeCLM_add, expFirstOrder_add]
  ring

theorem firstOrderReturn_sum {ι : Type*} (h : BlochVec)
    (S : Finset ι) (K : ι → Matrix (Fin 3) (Fin 3) ℂ) (t s : ℝ) :
    firstOrderReturn h (∑ i ∈ S, K i) t s=∑ i ∈ S, firstOrderReturn h (K i) t s := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [firstOrderReturn, expFirstOrder]
  | @insert i S hi ih =>
      simp only [Finset.sum_insert hi, firstOrderReturn_add, ih]

theorem kossakowski_eq_sum {n : ℕ} (v : Fin n → PauliVec) :
    GKSLAlgebra.kossakowski v = ∑ i, singleK (v i) := by
  ext i j
  simp [GKSLAlgebra.kossakowski, singleK, Matrix.sum_apply]

theorem kossakowski_eq_swap {n : ℕ} (v : Fin n → PauliVec) :
    GKSLAlgebra.kossakowski v = Swap.kossakowski v := by
  ext i j
  simp [GKSLAlgebra.kossakowski, Swap.kossakowski, Matrix.sum_apply, Matrix.vecMulVec]

/-- 任意有限跳跃族的实际参考首阶项，已接矩阵迹二次型。 -/
theorem firstOrderReturn_kossakowski_a (j : ℕ) {n : ℕ} (v : Fin n → PauliVec) :
    firstOrderReturn ![Swap.frequency j,0,0] (GKSLAlgebra.kossakowski v) 1 1 =
      (Swap.matrixQa j * GKSLAlgebra.kossakowski v).trace.re := by
  rw [kossakowski_eq_sum, firstOrderReturn_sum]
  simp only [firstOrderReturn_single_a]
  rw [← kossakowski_eq_sum, kossakowski_eq_swap, Swap.trace_Qa_kossakowski]
  simp

theorem firstOrderReturn_kossakowski_b (j : ℕ) {n : ℕ} (v : Fin n → PauliVec) :
    firstOrderReturn ![Swap.frequency j,0,0] (GKSLAlgebra.kossakowski v) 1 (-1) =
      (Swap.matrixQb j * GKSLAlgebra.kossakowski v).trace.re := by
  rw [kossakowski_eq_sum, firstOrderReturn_sum]
  simp only [firstOrderReturn_single_b]
  rw [← kossakowski_eq_sum, kossakowski_eq_swap, Swap.trace_Qb_kossakowski]
  simp

/-- 所有 PSD K，不限制耗散秩或跳跃数。 -/
theorem firstOrderReturn_psd_a (j : ℕ) (K : Matrix (Fin 3) (Fin 3) ℂ)
    (hK : K.PosSemidef) :
    firstOrderReturn ![Swap.frequency j,0,0] K 1 1 = (Swap.matrixQa j*K).trace.re := by
  obtain ⟨v,rfl⟩ := exists_kossakowski_factor K hK
  exact firstOrderReturn_kossakowski_a j v

theorem firstOrderReturn_psd_b (j : ℕ) (K : Matrix (Fin 3) (Fin 3) ℂ)
    (hK : K.PosSemidef) :
    firstOrderReturn ![Swap.frequency j,0,0] K 1 (-1) = (Swap.matrixQb j*K).trace.re := by
  obtain ⟨v,rfl⟩ := exists_kossakowski_factor K hK
  exact firstOrderReturn_kossakowski_b j v

#print axioms firstOrderReturn_psd_a
#print axioms firstOrderReturn_psd_b
end TwoStateQuantumEmbedding.SwapComparison

