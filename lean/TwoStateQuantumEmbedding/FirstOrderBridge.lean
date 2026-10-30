import TwoStateQuantumEmbedding.SwapComparison
import TwoStateQuantumEmbedding.GKSLNormBounds
import TwoStateQuantumEmbedding.UnitaryBoundary

noncomputable section
open Matrix Complex NormedSpace MeasureTheory
open scoped Interval ComplexOrder Matrix.Norms.L2Operator
namespace TwoStateQuantumEmbedding.SwapComparison
open GKSLAlgebra CanonicalBloch GKSLBounds

set_option maxRecDepth 2048
set_option maxHeartbeats 1600000

def encoded (x : AugmentedSpace) : QubitMatrix := realGeneralizedState (augmentedCoords x)

theorem hamiltonianCLM_zero : hamiltonianCLM 0=0 := by
  have hz : crossMatrix (0:BlochVec) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [crossMatrix]
  apply ContinuousLinearMap.ext
  intro x
  simp [hamiltonianCLM, augmentedCLM_apply, hz]

theorem canonicalCLM_zero (K : Matrix (Fin 3) (Fin 3) ℂ) :
    canonicalCLM 0 K = dissipativeCLM K := by
  rw [canonicalCLM_eq_add, hamiltonianCLM_zero, zero_add]

theorem hamiltonianCLM_eq_canonical (h : BlochVec) :
    hamiltonianCLM h = canonicalCLM h 0 := by
  rw [canonicalCLM_eq_add, dissipativeCLM_zero, add_zero]

theorem encoded_basis_plus : encoded (basisInitial 1) = Matrix.single 0 0 1 := by
  simp [encoded, basisInitial, augmentedCoords, realGeneralizedState,
    generalizedState, pauli, euclid, Matrix.smul_apply, smul_eq_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

theorem encoded_basis_minus : encoded (basisInitial (-1)) = Matrix.single 1 1 1 := by
  simp [encoded, basisInitial, augmentedCoords, realGeneralizedState,
    generalizedState, pauli, euclid, Matrix.smul_apply, smul_eq_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

theorem readout_encoded_plus (x : AugmentedSpace) :
    diagonalReadout 1 x = diagonalReal (encoded x) 0 := by
  simp [diagonalReadout_apply, diagonalReal, encoded, realGeneralizedState,
    generalizedState, augmentedCoords, pauli, Matrix.smul_apply, smul_eq_mul,
    Complex.mul_re]
  ring

theorem readout_encoded_minus (x : AugmentedSpace) :
    diagonalReadout (-1) x = diagonalReal (encoded x) 1 := by
  simp [diagonalReadout_apply, diagonalReal, encoded, realGeneralizedState,
    generalizedState, augmentedCoords, pauli, Matrix.smul_apply, smul_eq_mul,
    Complex.mul_re]
  ring

/-- 同一个实际耗散 CLM 与 Pauli dissipator 的完整输入桥。 -/
theorem encoded_dissipative_single (v : PauliVec) (x : AugmentedSpace) :
    encoded (dissipativeCLM (singleK v) x) =
      GKSLAlgebra.dissipator (pauli v) (encoded x) := by
  have hc : augmentedCoords (dissipativeCLM (singleK v) x) =
      augmentedGenerator 0 (singleK v) *ᵥ augmentedCoords x := by
    rw [← canonicalCLM_zero]
    have he := augmentedMatrixEquiv_mulVec (canonicalCLM 0 (singleK v)) x
    simpa only [canonicalCLM, AlgEquiv.apply_symm_apply] using he.symm
  unfold encoded
  rw [hc]
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [realGeneralizedState, generalizedState, augmentedCoords, augmentedGenerator,
      blochMatrix, crossMatrix, drift, singleK, GKSLAlgebra.dissipator, pauli,
      Matrix.mul_apply, Matrix.mulVec, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Matrix.trace,
      Matrix.one_apply, Matrix.conjTranspose_apply,
      Matrix.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im] <;> ring

/-- 纯 X 旋转对所有实迹输入的真实 Pauli 编码作用。 -/
theorem xRotation_encoded (a : ℝ) (x : AugmentedSpace) :
    xRotation a*encoded x*(xRotation a).conjTranspose =
      realGeneralizedState (rotation4 (2*a) *ᵥ augmentedCoords x) := by
  have ht := Real.sin_sq_add_cos_sq a
  have hu := congrArg (fun y => x.1*y) ht
  have hx := congrArg (fun y => (x.2 0)*y) ht
  have hy := congrArg (fun y => (x.2 1)*y) ht
  have hz := congrArg (fun y => (x.2 2)*y) ht
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [xRotation, encoded, realGeneralizedState, generalizedState, augmentedCoords,
      rotation4, pauli, Matrix.mul_apply, Matrix.mulVec, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      Matrix.one_apply, Matrix.conjTranspose_apply, pow_two, Matrix.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im,
      Real.sin_two_mul, Real.cos_two_mul, Complex.sin_ofReal_re, Complex.cos_ofReal_re] <;>
      nlinarith only [hu, hx, hy, hz]

theorem encoded_exp_hamiltonian_x (w t : ℝ) (x : AugmentedSpace) :
    encoded ((NormedSpace.exp (t • hamiltonianCLM ![w,0,0])) x) =
      xRotation (w*t/2)*encoded x*(xRotation (w*t/2)).conjTranspose := by
  unfold encoded
  rw [hamiltonianCLM_eq_canonical, augmentedCoords_exp_canonical]
  rw [canonicalEvolution, augmentedGenerator_x_zero, smul_smul, exp_rotationGenerator4]
  change realGeneralizedState (rotation4 (t*w) *ᵥ augmentedCoords x) =
    xRotation (w*t/2)*encoded x*(xRotation (w*t/2)).conjTranspose
  rw [xRotation_encoded]
  congr 2
  ring

/-- 参考首阶项已接到078的同一个增广CLM积分。 -/
theorem firstOrderReturn_single_a (j : ℕ) (v : PauliVec) :
    firstOrderReturn ![Swap.frequency j,0,0] (singleK v) 1 1 = Swap.qa j v := by
  rw [firstOrderReturn_eq_integral, ← referenceFirstOrder_a]
  unfold referenceFirstOrder
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [readout_encoded_plus, encoded_exp_hamiltonian_x, encoded_dissipative_single,
    encoded_exp_hamiltonian_x, encoded_basis_plus]
  rw [show Swap.frequency j*(1-t)/2=Swap.frequency j/2*(1-t) by ring,
    show Swap.frequency j*t/2=Swap.frequency j/2*t by ring]

theorem firstOrderReturn_single_b (j : ℕ) (v : PauliVec) :
    firstOrderReturn ![Swap.frequency j,0,0] (singleK v) 1 (-1) = Swap.qb j v := by
  rw [firstOrderReturn_eq_integral, ← referenceFirstOrder_b]
  unfold referenceFirstOrder
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [readout_encoded_minus, encoded_exp_hamiltonian_x, encoded_dissipative_single,
    encoded_exp_hamiltonian_x, encoded_basis_minus]
  rw [show Swap.frequency j*(1-t)/2=Swap.frequency j/2*(1-t) by ring,
    show Swap.frequency j*t/2=Swap.frequency j/2*t by ring]

#print axioms firstOrderReturn_single_a
#print axioms firstOrderReturn_single_b
#print axioms encoded_dissipative_single
#print axioms encoded_exp_hamiltonian_x
end TwoStateQuantumEmbedding.SwapComparison
