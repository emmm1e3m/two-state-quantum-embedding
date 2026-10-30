import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-! 原始 GKSL 作用与 Pauli/Bloch 对应的实际矩阵代数。 -/

noncomputable section
open Matrix Complex
open scoped BigOperators ComplexOrder

namespace TwoStateQuantumEmbedding.GKSLAlgebra

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

abbrev QubitMatrix := Matrix (Fin 2) (Fin 2) ℂ
abbrev PauliVec := Fin 3 → ℂ
abbrev BlochVec := Fin 3 → ℝ

def dissipator (A ρ : QubitMatrix) : QubitMatrix :=
  A * ρ * A.conjTranspose - (1 / 2 : ℂ) •
    (A.conjTranspose * A * ρ + ρ * A.conjTranspose * A)

def gkslAction {n : ℕ} (H : QubitMatrix) (A : Fin n → QubitMatrix)
    (ρ : QubitMatrix) : QubitMatrix :=
  (-Complex.I) • (H * ρ - ρ * H) + ∑ μ, dissipator (A μ) ρ

/-- 顺序固定为 X、Y、Z；此式直接定义实际 2×2 矩阵。 -/
def pauli (l : PauliVec) : QubitMatrix :=
  !![l 2, l 0 - Complex.I * l 1; l 0 + Complex.I * l 1, -l 2]

def realPauli (r : BlochVec) : QubitMatrix := pauli (fun j => (r j : ℂ))

def blochState (r : BlochVec) : QubitMatrix :=
  (1 / 2 : ℂ) • (1 + realPauli r)

def scalarPart (A : QubitMatrix) : ℂ := (A 0 0 + A 1 1) / 2

def pauliCoeffs (A : QubitMatrix) : PauliVec :=
  ![(A 0 1 + A 1 0) / 2,
    Complex.I * (A 0 1 - A 1 0) / 2,
    (A 0 0 - A 1 1) / 2]

def kossakowski {n : ℕ} (l : Fin n → PauliVec) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => ∑ μ, l μ i * star (l μ j)

def drift (K : Matrix (Fin 3) (Fin 3) ℂ) : BlochVec :=
  ![-4 * (K 1 2).im, -4 * (K 2 0).im, -4 * (K 0 1).im]

theorem pauli_trace (l : PauliVec) : Matrix.trace (pauli l) = 0 := by
  simp [pauli, Matrix.trace, Fin.sum_univ_two]

theorem pauli_decomposition (A : QubitMatrix) :
    scalarPart A • (1 : QubitMatrix) + pauli (pauliCoeffs A) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scalarPart, pauli, pauliCoeffs, Matrix.smul_apply, smul_eq_mul]
  all_goals ring_nf
  all_goals simp [Complex.I_sq]
  all_goals ring

def singleK (l : PauliVec) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => l i * star (l j)

def crossMatrix (h : BlochVec) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -h 2, h 1; h 2, 0, -h 0; -h 1, h 0, 0]

def dissipativeVelocity (K : Matrix (Fin 3) (Fin 3) ℂ) (r : BlochVec) : BlochVec :=
  (2 : ℝ) • ((K.map Complex.re) *ᵥ r - Matrix.trace (K.map Complex.re) • r) + drift K

def blochDerivative (v : BlochVec) : QubitMatrix := (1 / 2 : ℂ) • realPauli v

def hamiltonian (h : BlochVec) : QubitMatrix := (1 / 2 : ℂ) • realPauli h

def gaugeHamiltonian (q : ℂ) (L : QubitMatrix) : QubitMatrix :=
  (Complex.I / 2) • (star q • L - q • L.conjTranspose)

theorem dissipator_adjoint (A ρ : QubitMatrix) :
    (dissipator A ρ).conjTranspose = dissipator A ρ.conjTranspose := by
  simp [dissipator, Matrix.conjTranspose_mul, mul_assoc, add_comm]

theorem dissipator_trace (A ρ : QubitMatrix) : Matrix.trace (dissipator A ρ) = 0 := by
  simp only [dissipator, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_add, smul_eq_mul]
  rw [Matrix.trace_mul_cycle A ρ A.conjTranspose]
  rw [Matrix.trace_mul_cycle ρ A.conjTranspose A]
  rw [Matrix.trace_mul_cycle A ρ A.conjTranspose]
  ring

/-- 标量跳跃部分确实等于一个 Hamiltonian 规范修正。 -/
theorem dissipator_scalar_shift (q : ℂ) (L ρ : QubitMatrix) :
    dissipator (q • (1 : QubitMatrix) + L) ρ =
      dissipator L ρ + (-Complex.I) •
        (gaugeHamiltonian q L * ρ - ρ * gaugeHamiltonian q L) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [dissipator, gaugeHamiltonian, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul,
      Complex.mul_re, Complex.mul_im] <;> ring

theorem gaugeHamiltonian_hermitian (q : ℂ) (L : QubitMatrix) :
    (gaugeHamiltonian q L).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  apply Complex.ext <;>
    simp [gaugeHamiltonian, Matrix.conjTranspose_apply, Matrix.smul_apply,
      smul_eq_mul, Complex.mul_re, Complex.mul_im] <;> ring

theorem hamiltonian_hermitian (h : BlochVec) : (hamiltonian h).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [hamiltonian, realPauli, pauli, Matrix.smul_apply, smul_eq_mul,
      sub_eq_add_neg]

/-- 单个无迹复跳跃的耗散作用；未假定 Bloch 向量位于单位球。 -/
theorem dissipator_bloch (l : PauliVec) (r : BlochVec) :
    dissipator (pauli l) (blochState r) =
      blochDerivative (dissipativeVelocity (singleK l) r) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [dissipator, blochState, blochDerivative, realPauli, pauli,
      dissipativeVelocity, singleK, drift, Matrix.trace, Matrix.map_apply,
      Matrix.mulVec, Matrix.vecMul, dotProduct, Fin.sum_univ_three, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.smul_apply,
      smul_eq_mul, Complex.mul_re, Complex.mul_im] <;> ring

theorem hamiltonian_bloch (h r : BlochVec) :
    (-Complex.I) • (hamiltonian h * blochState r - blochState r * hamiltonian h) =
      blochDerivative ((crossMatrix h) *ᵥ r) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [hamiltonian, blochState, blochDerivative, realPauli, pauli,
      crossMatrix, Matrix.mulVec, Matrix.vecMul, dotProduct, Fin.sum_univ_three,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul,
      Complex.mul_re, Complex.mul_im] <;> ring

theorem kossakowski_posSemidef {n : ℕ} (l : Fin n → PauliVec) :
    (kossakowski l).PosSemidef := by
  let B : Matrix (Fin 3) (Fin n) ℂ := fun i μ => l μ i
  have heq : kossakowski l = B * B.conjTranspose := by
    ext i j
    rfl
  rw [heq]
  exact Matrix.posSemidef_self_mul_conjTranspose _

theorem blochDerivative_add (u v : BlochVec) :
    blochDerivative (u + v) = blochDerivative u + blochDerivative v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blochDerivative, realPauli, pauli, Matrix.smul_apply, smul_eq_mul] <;> ring

@[simp] theorem blochDerivative_zero : blochDerivative 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blochDerivative, realPauli, pauli, Matrix.smul_apply, smul_eq_mul]

theorem blochDerivative_sum {ι : Type*} (s : Finset ι) (f : ι → BlochVec) :
    blochDerivative (∑ i ∈ s, f i) = ∑ i ∈ s, blochDerivative (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih, blochDerivative_add]

theorem dissipativeVelocity_add (K L : Matrix (Fin 3) (Fin 3) ℂ) (r : BlochVec) :
    dissipativeVelocity (K + L) r = dissipativeVelocity K r + dissipativeVelocity L r := by
  funext i
  fin_cases i <;>
    simp [dissipativeVelocity, drift, Matrix.map_apply,
      Matrix.trace, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.vecHead, Matrix.vecTail, smul_eq_mul] <;> ring

@[simp] theorem dissipativeVelocity_zero (r : BlochVec) : dissipativeVelocity 0 r = 0 := by
  funext i
  fin_cases i <;>
    simp [dissipativeVelocity, drift, Matrix.trace]

theorem dissipativeVelocity_sum {ι : Type*} (s : Finset ι)
    (K : ι → Matrix (Fin 3) (Fin 3) ℂ) (r : BlochVec) :
    dissipativeVelocity (∑ i ∈ s, K i) r = ∑ i ∈ s, dissipativeVelocity (K i) r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih, dissipativeVelocity_add]

theorem dissipativeVelocity_kossakowski {n : ℕ} (l : Fin n → PauliVec) (r : BlochVec) :
    dissipativeVelocity (kossakowski l) r =
      ∑ μ, dissipativeVelocity (singleK (l μ)) r := by
  have heq : kossakowski l = ∑ μ, singleK (l μ) := by
    ext i j
    simp [kossakowski, singleK, Matrix.sum_apply]
  rw [heq, dissipativeVelocity_sum]

def blochMatrix (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  crossMatrix h + (2 : ℝ) •
    (K.map Complex.re - Matrix.trace (K.map Complex.re) • (1 : Matrix (Fin 3) (Fin 3) ℝ))

theorem blochMatrix_velocity (h r : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ) :
    blochMatrix h K *ᵥ r + drift K = crossMatrix h *ᵥ r + dissipativeVelocity K r := by
  funext i
  fin_cases i <;>
    simp [blochMatrix, dissipativeVelocity, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Matrix.smul_apply, smul_eq_mul] <;> ring

/-- 任意有限无迹跳跃的实际生成元作用等于论文中的 M r+c。 -/
theorem canonical_gksl_bloch {n : ℕ} (h r : BlochVec) (l : Fin n → PauliVec) :
    gkslAction (hamiltonian h) (fun μ => pauli (l μ)) (blochState r) =
      blochDerivative (blochMatrix h (kossakowski l) *ᵥ r + drift (kossakowski l)) := by
  simp only [gkslAction, hamiltonian_bloch, dissipator_bloch,
    blochMatrix_velocity, dissipativeVelocity_kossakowski, blochDerivative_add,
    blochDerivative_sum]

def hamiltonianVector (H : QubitMatrix) : BlochVec :=
  ![2 * (H 0 1).re, -2 * (H 0 1).im, (H 0 0).re - (H 1 1).re]

def hamiltonianScalar (H : QubitMatrix) : ℝ := ((H 0 0).re + (H 1 1).re) / 2

theorem hermitian_decomposition (H : QubitMatrix) (hH : H.IsHermitian) :
    ((hamiltonianScalar H : ℝ) : ℂ) • (1 : QubitMatrix) +
      hamiltonian (hamiltonianVector H) = H := by
  have h00 := congrArg Complex.im (hH.apply 0 0)
  have h11 := congrArg Complex.im (hH.apply 1 1)
  have hr := congrArg Complex.re (hH.apply 0 1)
  have hi := congrArg Complex.im (hH.apply 0 1)
  simp only [Complex.star_def, Complex.conj_re, Complex.conj_im] at h00 h11 hr hi
  have z00 : (H 0 0).im = 0 := by linarith
  have z11 : (H 1 1).im = 0 := by linarith
  have i10 : (H 1 0).im = -(H 0 1).im := by linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [hamiltonian, hamiltonianVector, hamiltonianScalar, realPauli, pauli,
      Matrix.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im,
      z00, z11, hr, i10] <;> ring

theorem scalar_hamiltonian_irrelevant {n : ℕ} (q : ℂ) (H ρ : QubitMatrix)
    (A : Fin n → QubitMatrix) :
    gkslAction (q • (1 : QubitMatrix) + H) A ρ = gkslAction H A ρ := by
  simp [gkslAction, Matrix.add_mul, Matrix.mul_add]

theorem hermitian_gksl_bloch {n : ℕ} (H : QubitMatrix) (hH : H.IsHermitian)
    (l : Fin n → PauliVec) (r : BlochVec) :
    gkslAction H (fun μ => pauli (l μ)) (blochState r) =
      blochDerivative (blochMatrix (hamiltonianVector H) (kossakowski l) *ᵥ r +
        drift (kossakowski l)) := by
  calc
    _ = gkslAction
        (((hamiltonianScalar H : ℝ) : ℂ) • (1 : QubitMatrix) +
          hamiltonian (hamiltonianVector H)) (fun μ => pauli (l μ)) (blochState r) := by
      rw [hermitian_decomposition H hH]
    _ = _ := by rw [scalar_hamiltonian_irrelevant, canonical_gksl_bloch]

def canonicalHamiltonian {n : ℕ} (H : QubitMatrix) (A : Fin n → QubitMatrix) : QubitMatrix :=
  H + ∑ μ, gaugeHamiltonian (scalarPart (A μ)) (pauli (pauliCoeffs (A μ)))

theorem canonicalHamiltonian_hermitian {n : ℕ} (H : QubitMatrix)
    (hH : H.IsHermitian) (A : Fin n → QubitMatrix) :
    (canonicalHamiltonian H A).IsHermitian := by
  apply hH.add
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro μ _
  exact (gaugeHamiltonian_hermitian _ _).eq

theorem gkslAction_gauge {n : ℕ} (H ρ : QubitMatrix) (A : Fin n → QubitMatrix) :
    gkslAction H A ρ =
      gkslAction (canonicalHamiltonian H A) (fun μ => pauli (pauliCoeffs (A μ))) ρ := by
  have hd (μ : Fin n) : dissipator (A μ) ρ =
      dissipator (pauli (pauliCoeffs (A μ))) ρ + (-Complex.I) •
      (gaugeHamiltonian (scalarPart (A μ)) (pauli (pauliCoeffs (A μ))) * ρ -
        ρ * gaugeHamiltonian (scalarPart (A μ)) (pauli (pauliCoeffs (A μ)))) := by
    calc
      _ = dissipator (scalarPart (A μ) • (1 : QubitMatrix) + pauli (pauliCoeffs (A μ))) ρ := by
        rw [pauli_decomposition]
      _ = _ := dissipator_scalar_shift _ _ _
  have hsum :
      (∑ μ, (-Complex.I) •
        (gaugeHamiltonian (scalarPart (A μ)) (pauli (pauliCoeffs (A μ))) * ρ -
        ρ * gaugeHamiltonian (scalarPart (A μ)) (pauli (pauliCoeffs (A μ))))) =
      (-Complex.I) •
        ((∑ μ, gaugeHamiltonian (scalarPart (A μ)) (pauli (pauliCoeffs (A μ)))) * ρ -
        ρ * (∑ μ, gaugeHamiltonian (scalarPart (A μ)) (pauli (pauliCoeffs (A μ))))) := by
    simp only [Matrix.sum_mul, Matrix.mul_sum, smul_sub,
      Finset.sum_sub_distrib, Finset.smul_sum]
  simp only [gkslAction, canonicalHamiltonian, hd, Finset.sum_add_distrib, hsum,
    Matrix.add_mul, Matrix.mul_add]
  module

/-- 原始任意有限跳跃、任意 Hermitian Hamiltonian 到实 Bloch 生成元的完整代数桥。 -/
theorem arbitrary_gksl_bloch {n : ℕ} (H : QubitMatrix) (hH : H.IsHermitian)
    (A : Fin n → QubitMatrix) (r : BlochVec) :
    gkslAction H A (blochState r) =
      blochDerivative
        (blochMatrix (hamiltonianVector (canonicalHamiltonian H A))
          (kossakowski (fun μ => pauliCoeffs (A μ))) *ᵥ r +
          drift (kossakowski (fun μ => pauliCoeffs (A μ)))) := by
  rw [gkslAction_gauge]
  exact hermitian_gksl_bloch _ (canonicalHamiltonian_hermitian H hH A) _ _

theorem gkslAction_trace {n : ℕ} (H ρ : QubitMatrix) (A : Fin n → QubitMatrix) :
    Matrix.trace (gkslAction H A ρ) = 0 := by
  simp only [gkslAction, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sub,
    Matrix.trace_sum, dissipator_trace, Finset.sum_const_zero, smul_eq_mul]
  rw [Matrix.trace_mul_comm H ρ]
  simp

theorem gkslAction_adjoint {n : ℕ} (H ρ : QubitMatrix) (hH : H.IsHermitian)
    (A : Fin n → QubitMatrix) :
    (gkslAction H A ρ).conjTranspose = gkslAction H A ρ.conjTranspose := by
  simp only [gkslAction, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_sum,
    dissipator_adjoint, hH.eq]
  simp only [map_neg, Complex.star_def, Complex.conj_I, neg_neg]
  module

/-- 复 Hermitian 系数的虚部由漂移完全恢复，符号对应计算基 z=+1。 -/
theorem hermitian_drift_reconstruction (K : Matrix (Fin 3) (Fin 3) ℂ)
    (hK : K.IsHermitian) :
    K = (fun i j => ((K i j).re : ℂ)) +
      (Complex.I / 4) • (fun i j => ((crossMatrix (drift K)) i j : ℂ)) := by
  have him (i j : Fin 3) : -(K j i).im = (K i j).im := by
    simpa only [Complex.star_def, Complex.conj_im] using
      congrArg Complex.im (hK.apply i j)
  have h00 := him 0 0
  have h11 := him 1 1
  have h22 := him 2 2
  have h01 := him 0 1
  have h02 := him 0 2
  have h12 := him 1 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [crossMatrix, drift, smul_eq_mul,
      Complex.mul_re, Complex.mul_im] <;> linarith

theorem kossakowski_real_posSemidef {n : ℕ} (l : Fin n → PauliVec) :
    ((kossakowski l).map Complex.re).PosSemidef := by
  let R : Matrix (Fin 3) (Fin n) ℝ := fun i μ => (l μ i).re
  let T : Matrix (Fin 3) (Fin n) ℝ := fun i μ => (l μ i).im
  have heq : (kossakowski l).map Complex.re = R * R.conjTranspose + T * T.conjTranspose := by
    ext i j
    change (∑ μ, l μ i * star (l μ j)).re =
      (∑ μ, (l μ i).re * (l μ j).re) + (∑ μ, (l μ i).im * (l μ j).im)
    simp [Complex.mul_re, Finset.sum_add_distrib]
  rw [heq]
  exact (Matrix.posSemidef_self_mul_conjTranspose R).add
    (Matrix.posSemidef_self_mul_conjTranspose T)

open scoped MatrixOrder Matrix.Norms.L2Operator in
/-- 任意 PSD 的 3×3 系数矩阵确有至多三个真实无迹跳跃的 Gram 分解。 -/
theorem exists_kossakowski_factor (K : Matrix (Fin 3) (Fin 3) ℂ)
    (hK : K.PosSemidef) : ∃ l : Fin 3 → PauliVec, kossakowski l = K := by
  let B : Matrix (Fin 3) (Fin 3) ℂ := CFC.sqrt K
  have hB : B.IsHermitian := by
    exact (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg K)).isHermitian
  have hBB : B * B.conjTranspose = K := by
    rw [hB.eq]
    exact CFC.sqrt_mul_sqrt_self K hK.nonneg
  refine ⟨fun μ i => B i μ, ?_⟩
  calc
    kossakowski (fun μ i => B i μ) = B * B.conjTranspose := by
      ext i j
      rfl
    _ = K := hBB

theorem hamiltonianVector_blochState (r : BlochVec) :
    hamiltonianVector (blochState r) = r := by
  funext i
  fin_cases i <;>
    simp [hamiltonianVector, blochState, realPauli, pauli,
      Matrix.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im]
  all_goals ring

theorem hamiltonianVector_blochDerivative (v : BlochVec) :
    hamiltonianVector (blochDerivative v) = v := by
  funext i
  fin_cases i <;>
    simp [hamiltonianVector, blochDerivative, realPauli, pauli,
      Matrix.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im]
  all_goals ring

theorem blochState_trace (r : BlochVec) : Matrix.trace (blochState r) = 1 := by
  simp [blochState, Matrix.trace_smul, Matrix.trace_add, realPauli, pauli_trace]

theorem blochState_hermitian (r : BlochVec) : (blochState r).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [blochState, realPauli, pauli, Matrix.smul_apply, smul_eq_mul, sub_eq_add_neg]

theorem hermitian_trace_one_blochState (ρ : QubitMatrix) (hρ : ρ.IsHermitian)
    (htr : Matrix.trace ρ = 1) : blochState (hamiltonianVector ρ) = ρ := by
  have hr := congrArg Complex.re htr
  simp only [Matrix.trace, Fin.sum_univ_two, Complex.add_re, Complex.one_re] at hr
  change (ρ 0 0).re + (ρ 1 1).re = 1 at hr
  have hs : hamiltonianScalar ρ = 1 / 2 := by
    unfold hamiltonianScalar
    rw [hr]
  calc
    blochState (hamiltonianVector ρ) =
        ((hamiltonianScalar ρ : ℝ) : ℂ) • (1 : QubitMatrix) +
          hamiltonian (hamiltonianVector ρ) := by
      rw [hs]
      simp [blochState, hamiltonian, smul_add]
    _ = ρ := hermitian_decomposition ρ hρ

theorem blochState_basis_zero : blochState ![0, 0, 1] = Matrix.single 0 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [blochState, realPauli, pauli, Matrix.single_apply, Matrix.smul_apply, smul_eq_mul]

theorem blochState_basis_one : blochState ![0, 0, -1] = Matrix.single 1 1 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [blochState, realPauli, pauli, Matrix.single_apply, Matrix.smul_apply, smul_eq_mul]

/-- 每个 PSD 的规范参数都由合法有限跳跃真正实现。 -/
theorem exists_gksl_for_canonical (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ)
    (hK : K.PosSemidef) :
    ∃ A : Fin 3 → QubitMatrix, ∀ r : BlochVec,
      gkslAction (hamiltonian h) A (blochState r) =
        blochDerivative (blochMatrix h K *ᵥ r + drift K) := by
  obtain ⟨l, hl⟩ := exists_kossakowski_factor K hK
  refine ⟨fun μ => pauli (l μ), ?_⟩
  intro r
  simpa only [hl] using canonical_gksl_bloch h r l

#print axioms pauli_decomposition
#print axioms dissipator_scalar_shift
#print axioms dissipator_bloch
#print axioms hamiltonian_bloch
#print axioms canonical_gksl_bloch
#print axioms hermitian_gksl_bloch
#print axioms kossakowski_posSemidef
#print axioms gkslAction_gauge
#print axioms arbitrary_gksl_bloch
#print axioms gkslAction_trace
#print axioms gkslAction_adjoint
#print axioms hermitian_drift_reconstruction
#print axioms kossakowski_real_posSemidef
#print axioms exists_kossakowski_factor
#print axioms exists_gksl_for_canonical
#print axioms hermitian_trace_one_blochState

end TwoStateQuantumEmbedding.GKSLAlgebra
