import TwoStateQuantumEmbedding.Model
import TwoStateQuantumEmbedding.GKSLAlgebra
import TwoStateQuantumEmbedding.ResetFamily
import Mathlib.Tactic

/-! 从原始纯态稳态条件推出共同暗态规范。 -/
noncomputable section
open Matrix Complex
open scoped BigOperators Matrix.Norms.Operator

namespace TwoStateQuantumEmbedding.PureStationary

def pureProjector (g : Fin 2 → ℂ) : QubitMatrix := Matrix.vecMulVec g (star g)
def pureBasis (g : Fin 2 → ℂ) : QubitMatrix :=
  !![-star (g 1), g 0; star (g 0), g 1]
def ground : QubitMatrix := Matrix.single 1 1 1
def conjugate (U X : QubitMatrix) : QubitMatrix := U * X * U.conjTranspose

/-- 对真实生成元定义纯稳态，不限制跳跃数、秩或方向。 -/
def HasPureStationary {n : ℕ} (H : QubitMatrix) (J : Fin n → QubitMatrix) : Prop :=
  ∃ g : Fin 2 → ℂ, normSq (g 0) + normSq (g 1) = 1 ∧
    gkslAction H J (pureProjector g) = 0

theorem pureBasis_unitary (g : Fin 2 → ℂ) (hg : normSq (g 0) + normSq (g 1) = 1) :
    (pureBasis g).conjTranspose * pureBasis g = 1 ∧
      pureBasis g * (pureBasis g).conjTranspose = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [pureBasis, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      normSq_apply, Complex.mul_re, Complex.mul_im] at * <;> nlinarith

theorem pureProjector_basis (g : Fin 2 → ℂ) :
    pureProjector g = conjugate (pureBasis g) ground := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pureProjector, conjugate, pureBasis, ground, Matrix.vecMulVec,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Matrix.single_apply]

theorem gksl_conjugate {n : ℕ} (U H X : QubitMatrix) (J : Fin n → QubitMatrix)
    (hU : U.conjTranspose * U = 1) :
    gkslAction (conjugate U H) (fun μ => conjugate U (J μ)) (conjugate U X) =
      conjugate U (gkslAction H J X) := by
  have hd (μ : Fin n) : dissipator (conjugate U (J μ)) (conjugate U X) =
      conjugate U (dissipator (J μ) X) :=
    ResetFamily.dissipator_conjugate U (J μ) X hU
  simp only [gkslAction]
  simp_rw [hd]
  simp only [conjugate, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sub, Matrix.sub_mul]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc U.conjTranspose U, hU, Matrix.one_mul]

theorem stationary_ground_offdiagonal {n : ℕ} (H : QubitMatrix) (J : Fin n → QubitMatrix)
    (hs : gkslAction H J ground = 0) : ∀ μ, J μ 0 1 = 0 := by
  have hd : (gkslAction H J ground 0 0).re = ∑ μ, normSq (J μ 0 1) := by
    simp [gkslAction, dissipator, ground, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.single_apply, Matrix.conjTranspose_apply,
      Matrix.sum_apply, Complex.mul_re, normSq_apply]
  rw [hs] at hd
  have hz : ∑ μ, normSq (J μ 0 1) = 0 := hd.symm
  have h_each := (Finset.sum_eq_zero_iff_of_nonneg (fun μ _ => normSq_nonneg (J μ 0 1))).mp hz
  intro μ
  exact normSq_eq_zero.mp (h_each μ (Finset.mem_univ μ))

def shiftedJumps {n : ℕ} (J : Fin n → QubitMatrix) : Fin n → QubitMatrix :=
  fun μ => J μ - J μ 1 1 • (1 : QubitMatrix)
def shiftedHamiltonian {n : ℕ} (H : QubitMatrix) (J : Fin n → QubitMatrix) : QubitMatrix :=
  H + ∑ μ, GKSLAlgebra.gaugeHamiltonian (J μ 1 1) (shiftedJumps J μ)
def darkJump (x y : ℂ) : QubitMatrix := !![x, 0; y, 0]
def darkJumps {n : ℕ} (x y : Fin n → ℂ) : Fin n → QubitMatrix :=
  fun μ => darkJump (x μ) (y μ)
def diagonalHamiltonian (ω : ℝ) : QubitMatrix := !![(ω / 2 : ℂ), 0; 0, -(ω / 2)]

theorem shifted_action {n : ℕ} (H X : QubitMatrix) (J : Fin n → QubitMatrix) :
    gkslAction H J X = gkslAction (shiftedHamiltonian H J) (shiftedJumps J) X := by
  have hd (μ : Fin n) : dissipator (J μ) X = dissipator (shiftedJumps J μ) X +
      (-Complex.I) • (GKSLAlgebra.gaugeHamiltonian (J μ 1 1) (shiftedJumps J μ) * X -
        X * GKSLAlgebra.gaugeHamiltonian (J μ 1 1) (shiftedJumps J μ)) := by
    have h := GKSLAlgebra.dissipator_scalar_shift (J μ 1 1) (shiftedJumps J μ) X
    change dissipator _ X = dissipator _ X + _ at h
    simpa only [shiftedJumps, add_sub_cancel] using h
  have hsum : (∑ μ, (-Complex.I) •
      (GKSLAlgebra.gaugeHamiltonian (J μ 1 1) (shiftedJumps J μ) * X -
        X * GKSLAlgebra.gaugeHamiltonian (J μ 1 1) (shiftedJumps J μ))) =
      (-Complex.I) • ((∑ μ, GKSLAlgebra.gaugeHamiltonian (J μ 1 1) (shiftedJumps J μ)) * X -
        X * (∑ μ, GKSLAlgebra.gaugeHamiltonian (J μ 1 1) (shiftedJumps J μ))) := by
    simp only [Matrix.sum_mul, Matrix.mul_sum, smul_sub, Finset.sum_sub_distrib, Finset.smul_sum]
  simp only [gkslAction, shiftedHamiltonian, hd, Finset.sum_add_distrib, hsum,
    Matrix.add_mul, Matrix.mul_add]
  module

theorem shifted_hermitian {n : ℕ} (H : QubitMatrix) (hH : H.IsHermitian)
    (J : Fin n → QubitMatrix) : (shiftedHamiltonian H J).IsHermitian := by
  apply hH.add
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro μ _
  exact (GKSLAlgebra.gaugeHamiltonian_hermitian _ _).eq

theorem shifted_dark_form {n : ℕ} (J : Fin n → QubitMatrix) (hJ : ∀ μ, J μ 0 1 = 0) :
    shiftedJumps J = darkJumps (fun μ => J μ 0 0 - J μ 1 1) (fun μ => J μ 1 0) := by
  funext μ
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [shiftedJumps, darkJumps, darkJump, hJ]

theorem dark_dissipator_ground (x y : ℂ) : dissipator (darkJump x y) ground = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [dissipator, darkJump, ground, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_two, Matrix.single_apply, Matrix.conjTranspose_apply]

theorem dark_stationary_hamiltonian_offdiagonal {n : ℕ} (H : QubitMatrix)
    (x y : Fin n → ℂ) (hs : gkslAction H (darkJumps x y) ground = 0) : H 0 1 = 0 := by
  have h := congrArg (fun X : QubitMatrix => X 0 1) hs
  simp only [gkslAction, darkJumps, dark_dissipator_ground, Finset.sum_const_zero, add_zero] at h
  simp [ground, Matrix.mul_apply, Matrix.single_apply] at h
  exact h

theorem diagonal_hamiltonian_decomposition (H : QubitMatrix) (hH : H.IsHermitian)
    (h01 : H 0 1 = 0) :
    (((H 0 0).re + (H 1 1).re) / 2 : ℂ) • (1 : QubitMatrix) +
      diagonalHamiltonian ((H 0 0).re - (H 1 1).re) = H := by
  have h00 := congrArg Complex.im (hH.apply 0 0)
  have h11 := congrArg Complex.im (hH.apply 1 1)
  have h10 := hH.apply 1 0
  simp only [Complex.star_def, Complex.conj_im] at h00 h11
  have hi00 : (H 0 0).im = 0 := by linarith
  have hi11 : (H 1 1).im = 0 := by linarith
  have hz10 : H 1 0 = 0 := by simpa [h01] using h10.symm
  ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [diagonalHamiltonian, Matrix.smul_apply, smul_eq_mul, hi00, hi11, h01, hz10] <;> ring

/-- 给定基中的纯稳态迫使全部跳跃共同暗，并使调整后的 Hamiltonian 对角。 -/
theorem ground_normal_form {n : ℕ} (H : QubitMatrix) (hH : H.IsHermitian)
    (J : Fin n → QubitMatrix) (hs : gkslAction H J ground = 0) :
    ∃ (ω : ℝ) (x y : Fin n → ℂ), ∀ X : QubitMatrix,
      gkslAction H J X = gkslAction (diagonalHamiltonian ω) (darkJumps x y) X := by
  have hJ := stationary_ground_offdiagonal H J hs
  have hform := shifted_dark_form J hJ
  have hH' := shifted_hermitian H hH J
  have hs' : gkslAction (shiftedHamiltonian H J)
      (darkJumps (fun μ => J μ 0 0 - J μ 1 1) (fun μ => J μ 1 0)) ground = 0 := by
    rw [← hform, ← shifted_action]
    exact hs
  have h01 := dark_stationary_hamiltonian_offdiagonal _ _ _ hs'
  refine ⟨((shiftedHamiltonian H J) 0 0).re - ((shiftedHamiltonian H J) 1 1).re,
    (fun μ => J μ 0 0 - J μ 1 1), (fun μ => J μ 1 0), ?_⟩
  intro X
  rw [shifted_action, hform]
  conv_lhs => rw [← diagonal_hamiltonian_decomposition _ hH' h01]
  exact GKSLAlgebra.scalar_hamiltonian_irrelevant _ _ _ _

theorem conjugate_inverse (U X : QubitMatrix) (hU : U.conjTranspose * U = 1) :
    conjugate U.conjTranspose (conjugate U X) = X := by
  simp only [conjugate, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
    ← Matrix.mul_assoc U.conjTranspose U, hU, Matrix.one_mul, Matrix.mul_one]

theorem conjugate_hermitian (U H : QubitMatrix) (hH : H.IsHermitian) :
    (conjugate U H).IsHermitian := by
  unfold Matrix.IsHermitian conjugate
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hH.eq]
  simp only [Matrix.mul_assoc]

theorem rotated_stationary_ground {n : ℕ} (H : QubitMatrix) (J : Fin n → QubitMatrix)
    (g : Fin 2 → ℂ) (hg : normSq (g 0) + normSq (g 1) = 1)
    (hs : gkslAction H J (pureProjector g) = 0) :
    gkslAction (conjugate (pureBasis g).conjTranspose H)
      (fun μ => conjugate (pureBasis g).conjTranspose (J μ)) ground = 0 := by
  obtain ⟨hU, hU'⟩ := pureBasis_unitary g hg
  have h := gksl_conjugate (pureBasis g).conjTranspose H (pureProjector g) J
    (by simpa only [Matrix.conjTranspose_conjTranspose] using hU')
  rw [pureProjector_basis g, conjugate_inverse _ _ hU] at h
  rw [← pureProjector_basis g, hs] at h
  simpa [conjugate] using h

/-- 每个原始跳跃都以给定纯稳态向量为本征向量。 -/
theorem stationary_common_eigenvector {n : ℕ} (H : QubitMatrix) (J : Fin n → QubitMatrix)
    (g : Fin 2 → ℂ) (hg : normSq (g 0) + normSq (g 1) = 1)
    (hs : gkslAction H J (pureProjector g) = 0) :
    ∀ μ, J μ *ᵥ g = (conjugate (pureBasis g).conjTranspose (J μ) 1 1) • g := by
  obtain ⟨hU, hU'⟩ := pureBasis_unitary g hg
  have hJ := stationary_ground_offdiagonal _ _ (rotated_stationary_ground H J g hg hs)
  intro μ
  have hmul : J μ * pureBasis g =
      pureBasis g * conjugate (pureBasis g).conjTranspose (J μ) := by
    simp only [conjugate, Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc, hU',
      Matrix.one_mul]
  ext i
  have hi := congrArg (fun X : QubitMatrix => X i 1) hmul
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hJ μ, mul_zero, zero_add] at hi
  fin_cases i <;> simpa [pureBasis, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    smul_eq_mul, mul_comm] using hi

/-- 任意纯稳态生成元的完整暗态规范，结论是对所有矩阵输入的同一线性作用。 -/
theorem pure_stationary_normal_form {n : ℕ} (H : QubitMatrix) (hH : H.IsHermitian)
    (J : Fin n → QubitMatrix) (g : Fin 2 → ℂ)
    (hg : normSq (g 0) + normSq (g 1) = 1)
    (hs : gkslAction H J (pureProjector g) = 0) :
    ∃ (U : QubitMatrix) (ω : ℝ) (x y : Fin n → ℂ),
      U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1 ∧
      pureProjector g = conjugate U ground ∧
      ∀ X : QubitMatrix, gkslAction H J (conjugate U X) =
        conjugate U (gkslAction (diagonalHamiltonian ω) (darkJumps x y) X) := by
  obtain ⟨hU, hU'⟩ := pureBasis_unitary g hg
  have hs' := rotated_stationary_ground H J g hg hs
  obtain ⟨ω, x, y, hn⟩ := ground_normal_form _ (conjugate_hermitian _ _ hH) _ hs'
  refine ⟨pureBasis g, ω, x, y, hU, hU', pureProjector_basis g, ?_⟩
  intro X
  rw [← hn]
  have h := gksl_conjugate (pureBasis g) (conjugate (pureBasis g).conjTranspose H) X
    (fun μ => conjugate (pureBasis g).conjTranspose (J μ)) hU
  have hback (Y : QubitMatrix) :
      conjugate (pureBasis g) (conjugate (pureBasis g).conjTranspose Y) = Y := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      conjugate_inverse (pureBasis g).conjTranspose Y
        (by simpa only [Matrix.conjTranspose_conjTranspose] using hU')
  simpa only [hback] using h

end TwoStateQuantumEmbedding.PureStationary

#print axioms TwoStateQuantumEmbedding.PureStationary.stationary_ground_offdiagonal
#print axioms TwoStateQuantumEmbedding.PureStationary.stationary_common_eigenvector
#print axioms TwoStateQuantumEmbedding.PureStationary.pure_stationary_normal_form
