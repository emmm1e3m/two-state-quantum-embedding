import TwoStateQuantumEmbedding.ResetStationaryBudget
import TwoStateQuantumEmbedding.ResetEndpoint

noncomputable section
open Matrix Complex Set
open scoped BigOperators Matrix.Norms.Operator ComplexOrder
namespace TwoStateQuantumEmbedding.ResetActual
open ResetEndpoint

/-- 原始对角稳态的精确误差恒等式，不预先排序其两个特征值。 -/
theorem diagonal_output_identity {n : ℕ} (H : QubitMatrix) (J : Fin n → QubitMatrix)
    (t ν : ℝ) (hH : H.IsHermitian) (ht : 0 ≤ t)
    (hs : gkslAction H J (diagonalState ν) = 0) :
    1-(finiteOutput H J t).2 =
      ν * (1-((finiteOutput H J t).1+(finiteOutput H J t).2-1)) := by
  have hdiag : diagonalState ν =
      (ν : ℂ) • (Matrix.single 0 0 1 : QubitMatrix) +
      (1-(ν : ℂ)) • (Matrix.single 1 1 1 : QubitMatrix) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [diagonalState, Matrix.single_apply]
  have hfix := gksl_evolution_fixed_of_stationary H J (diagonalState ν) hs t
  rw [hdiag, map_add, map_smul, map_smul] at hfix
  have hpop := congrArg (fun X : QubitMatrix => (X 0 0).re) hfix
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    mul_zero, sub_zero, zero_mul, Matrix.single_apply, if_pos rfl,
    Fin.zero_eta, Fin.isValue] at hpop
  rw [gksl_disturbance_eq_one_sub_output H J t hH ht] at hpop
  have ha : (gkslSuperoperatorEvolution H J t (Matrix.single 0 0 1) 0 0).re =
      (finiteOutput H J t).1 := by rw [finiteOutput_eq_superoperator_probabilities]
  rw [ha] at hpop
  norm_num at hpop
  nlinarith

theorem diagonal_nu_le_error {n : ℕ} (H : QubitMatrix) (J : Fin n → QubitMatrix)
    (t ν : ℝ) (hH : H.IsHermitian) (ht : 0 ≤ t) (hν0 : 0 ≤ ν)
    (hs : gkslAction H J (diagonalState ν) = 0)
    (hq : (finiteOutput H J t).1+(finiteOutput H J t).2-1 ≤ 0) :
    ν ≤ 1-(finiteOutput H J t).2 := by
  have hid := diagonal_output_identity H J t ν hH ht hs
  have hm := mul_nonneg hν0 (neg_nonneg.mpr hq)
  nlinarith


#print axioms diagonal_output_identity
#print axioms diagonal_nu_le_error
end TwoStateQuantumEmbedding.ResetActual
