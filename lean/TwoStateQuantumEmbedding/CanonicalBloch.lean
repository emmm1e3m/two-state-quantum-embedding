import TwoStateQuantumEmbedding.GKSLAlgebra
import TwoStateQuantumEmbedding.ExponentialRepresentation

/-! 原始矩阵指数与增广 Bloch 矩阵指数的真实对应。 -/

noncomputable section
open Matrix Complex
open scoped BigOperators Matrix.Norms.Operator ComplexOrder

namespace TwoStateQuantumEmbedding.CanonicalBloch
open GKSLAlgebra

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

abbrev BlochIndex := Fin 4
abbrev AugmentedMatrix := Matrix BlochIndex BlochIndex ℝ
abbrev AugmentedVector := BlochIndex → ℝ

/-- 第 0 坐标为迹，后面三个坐标依次为 X、Y、Z。 -/
def augmentedGenerator (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ) : AugmentedMatrix :=
  let M := blochMatrix h K
  let c := drift K
  !![0, 0, 0, 0;
     c 0, M 0 0, M 0 1, M 0 2;
     c 1, M 1 0, M 1 1, M 1 2;
     c 2, M 2 0, M 2 1, M 2 2]

def canonicalEvolution (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ) (t : ℝ) :
    AugmentedMatrix := NormedSpace.exp (t • augmentedGenerator h K)

def canonicalOutput (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ) (t : ℝ) : ℝ × ℝ :=
  let E := canonicalEvolution h K t
  ((1 + E 3 3 + E 3 0) / 2, (1 + E 3 3 - E 3 0) / 2)

def canonicalOutputs : Set (ℝ × ℝ) :=
  {p | ∃ (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ),
    K.PosSemidef ∧ canonicalOutput h K 1 = p}

theorem canonicalOutput_sum_sub_one (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ)
    (t : ℝ) :
    (canonicalOutput h K t).1 + (canonicalOutput h K t).2 - 1 =
      canonicalEvolution h K t 3 3 := by
  simp only [canonicalOutput]
  ring

theorem canonicalOutput_sub (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ) (t : ℝ) :
    (canonicalOutput h K t).1 - (canonicalOutput h K t).2 =
      canonicalEvolution h K t 3 0 := by
  simp only [canonicalOutput]
  ring

/-- 不要求迹为 1，也不要求 Hermitian 的完整复线性 Pauli 编码。 -/
def generalizedState : (BlochIndex → ℂ) ≃ₗ[ℂ] QubitMatrix where
  toFun v := (1 / 2 : ℂ) • (v 0 • (1 : QubitMatrix) + pauli ![v 1, v 2, v 3])
  invFun ρ := ![ρ 0 0 + ρ 1 1, ρ 0 1 + ρ 1 0,
    Complex.I * (ρ 0 1 - ρ 1 0), ρ 0 0 - ρ 1 1]
  left_inv v := by
    funext i
    fin_cases i <;>
      simp [pauli, Matrix.smul_apply, smul_eq_mul]
    all_goals ring_nf
    all_goals simp [Complex.I_sq]
  right_inv ρ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauli, Matrix.smul_apply, smul_eq_mul]
    all_goals ring_nf
    all_goals simp [Complex.I_sq]
    all_goals ring
  map_add' v w := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauli, Matrix.smul_apply, smul_eq_mul] <;> ring
  map_smul' z v := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauli, Matrix.smul_apply, smul_eq_mul] <;> ring

def realGeneralizedState (v : AugmentedVector) : QubitMatrix :=
  generalizedState (fun i => (v i : ℂ))

def spatialPart (v : AugmentedVector) : BlochVec := ![v 1, v 2, v 3]

theorem realGeneralizedState_affine (v : AugmentedVector) :
    realGeneralizedState v = ((v 0 - 1 : ℝ) : ℂ) • blochState 0 +
      blochState (spatialPart v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [realGeneralizedState, generalizedState, spatialPart, blochState, realPauli,
      pauli, Matrix.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im] <;> ring

theorem realGeneralizedState_zero_head (v : AugmentedVector) (h : v 0 = 0) :
    realGeneralizedState v = blochDerivative (spatialPart v) := by
  simp [realGeneralizedState, generalizedState, blochDerivative, realPauli, spatialPart, h]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem augmentedGenerator_mulVec_head (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ)
    (v : AugmentedVector) : (augmentedGenerator h K *ᵥ v) 0 = 0 := by
  simp [augmentedGenerator, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem augmentedGenerator_mulVec_spatial (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ)
    (v : AugmentedVector) :
    spatialPart (augmentedGenerator h K *ᵥ v) =
      blochMatrix h K *ᵥ spatialPart v + v 0 • drift K := by
  funext i
  fin_cases i <;>
    simp [spatialPart, augmentedGenerator, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, smul_eq_mul] <;> ring

theorem blochDerivative_complex_ofReal_smul (s : ℝ) (v : BlochVec) :
    blochDerivative (s • v) = (s : ℂ) • blochDerivative v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blochDerivative, realPauli, pauli, Matrix.smul_apply, smul_eq_mul] <;> ring

/-- 任意实迹和任意实 Bloch 坐标的生成元对应。 -/
theorem gkslAction_realGeneralizedState {n : ℕ} (H : QubitMatrix) (hH : H.IsHermitian)
    (A : Fin n → QubitMatrix) (v : AugmentedVector) :
    TwoStateQuantumEmbedding.gkslAction H A (realGeneralizedState v) =
      realGeneralizedState
        (augmentedGenerator (hamiltonianVector (canonicalHamiltonian H A))
          (kossakowski (fun μ => pauliCoeffs (A μ))) *ᵥ v) := by
  rw [realGeneralizedState_affine, gkslAction_add, gkslAction_complex_smul]
  change ((v 0 - 1 : ℝ) : ℂ) • GKSLAlgebra.gkslAction H A (blochState 0) +
    GKSLAlgebra.gkslAction H A (blochState (spatialPart v)) = _
  rw [arbitrary_gksl_bloch H hH, arbitrary_gksl_bloch H hH,
    realGeneralizedState_zero_head _ (augmentedGenerator_mulVec_head _ _ _),
    augmentedGenerator_mulVec_spatial]
  simp only [Matrix.mulVec_zero, zero_add]
  rw [← blochDerivative_complex_ofReal_smul, ← blochDerivative_add]
  congr 1
  module

/-- 以完整 Pauli 坐标表示任意复线性超算子。 -/
def blochEndAlgEquiv : Module.End ℂ QubitMatrix ≃ₐ[ℂ]
    Matrix BlochIndex BlochIndex ℂ :=
  (generalizedState.symm.conjAlgEquiv ℂ).trans LinearMap.toMatrixAlgEquiv'

theorem blochEndAlgEquiv_apply (f : Module.End ℂ QubitMatrix) (i j : BlochIndex) :
    blochEndAlgEquiv f i j =
      generalizedState.symm (f (generalizedState (Pi.single j 1))) i := rfl

theorem complex_single_eq_real_single (j : BlochIndex) :
    (Pi.single j 1 : BlochIndex → ℂ) =
      fun i => ((Pi.single j 1 : AugmentedVector) i : ℂ) := by
  funext i
  by_cases hij : i = j <;> simp [hij]

/-- 已证明的实生成元作用确定复线性表示的全部四列。 -/
theorem blochEndAlgEquiv_gksl {n : ℕ} (H : QubitMatrix) (hH : H.IsHermitian)
    (A : Fin n → QubitMatrix) :
    blochEndAlgEquiv (gkslLinearMap H A) =
      (augmentedGenerator (hamiltonianVector (canonicalHamiltonian H A))
        (kossakowski (fun μ => pauliCoeffs (A μ)))).map Complex.ofReal := by
  ext i j
  rw [blochEndAlgEquiv_apply, complex_single_eq_real_single]
  change generalizedState.symm
    (TwoStateQuantumEmbedding.gkslAction H A (realGeneralizedState (Pi.single j 1))) i = _
  rw [gkslAction_realGeneralizedState H hH]
  simp only [realGeneralizedState, LinearEquiv.symm_apply_apply]
  simp [Matrix.mulVec_single]

/-- 原 Liouville 数组和完整 Pauli 数组之间的实际矩阵代数同构。 -/
def liouvilleBlochAlgEquiv : LiouvilleMatrix ≃ₐ[ℂ] Matrix BlochIndex BlochIndex ℂ :=
  (matrixEndAlgEquiv (Fin 2)).symm.trans blochEndAlgEquiv

theorem liouvilleBlochAlgEquiv_gksl {n : ℕ} (H : QubitMatrix) (hH : H.IsHermitian)
    (A : Fin n → QubitMatrix) :
    liouvilleBlochAlgEquiv (gkslMatrix H A) =
      (augmentedGenerator (hamiltonianVector (canonicalHamiltonian H A))
        (kossakowski (fun μ => pauliCoeffs (A μ)))).map Complex.ofReal := by
  have hm : gkslMatrix H A = matrixEndAlgEquiv (Fin 2) (gkslLinearMap H A) := by
    ext ij kl
    simp [matrixEndAlgEquiv_apply, gkslMatrix, actionMatrix, gkslLinearMap]
  rw [hm]
  change blochEndAlgEquiv ((matrixEndAlgEquiv (Fin 2)).symm
    ((matrixEndAlgEquiv (Fin 2)) (gkslLinearMap H A))) = _
  rw [AlgEquiv.symm_apply_apply]
  exact blochEndAlgEquiv_gksl H hH A

theorem liouvilleBlochAlgEquiv_exp (L : LiouvilleMatrix) :
    liouvilleBlochAlgEquiv (NormedSpace.exp L) =
      NormedSpace.exp (liouvilleBlochAlgEquiv L) :=
  NormedSpace.map_exp liouvilleBlochAlgEquiv
    liouvilleBlochAlgEquiv.toLinearMap.continuous_of_finiteDimensional L

theorem real_matrix_exp_complex (Q : AugmentedMatrix) :
    (NormedSpace.exp Q).map Complex.ofReal =
      NormedSpace.exp (Q.map Complex.ofReal) := by
  let f : AugmentedMatrix →+* Matrix BlochIndex BlochIndex ℂ :=
    Complex.ofRealHom.mapMatrix
  apply NormedSpace.map_exp f _ Q
  change Continuous (fun Q : AugmentedMatrix => fun i j => (Q i j : ℂ))
  fun_prop

/-- 真实矩阵指数的坐标变换，对全部实时间成立。 -/
theorem finiteEvolution_bloch_representation {n : ℕ} (H : QubitMatrix) (hH : H.IsHermitian)
    (A : Fin n → QubitMatrix) (t : ℝ) :
    liouvilleBlochAlgEquiv (finiteEvolution H A t) =
      (canonicalEvolution (hamiltonianVector (canonicalHamiltonian H A))
        (kossakowski (fun μ => pauliCoeffs (A μ))) t).map Complex.ofReal := by
  unfold finiteEvolution canonicalEvolution
  rw [liouvilleBlochAlgEquiv_exp, real_matrix_exp_complex]
  congr 1
  change liouvilleBlochAlgEquiv ((t : ℂ) • gkslMatrix H A) = _
  rw [map_smul, liouvilleBlochAlgEquiv_gksl H hH]
  ext i j
  simp

theorem blochEndAlgEquiv_mulVec (f : Module.End ℂ QubitMatrix) (v : BlochIndex → ℂ) :
    blochEndAlgEquiv f *ᵥ v = generalizedState.symm (f (generalizedState v)) := by
  change Matrix.toLinAlgEquiv' (LinearMap.toMatrixAlgEquiv'
    (generalizedState.symm.conjAlgEquiv ℂ f)) v = _
  rw [Matrix.toLinAlgEquiv'_toMatrixAlgEquiv']
  rfl

theorem liouvilleBlochAlgEquiv_superoperator (f : QubitMatrix →L[ℂ] QubitMatrix) :
    liouvilleBlochAlgEquiv (matrixCLMAlgEquiv (Fin 2) f) =
      blochEndAlgEquiv f.toLinearMap := by
  change blochEndAlgEquiv ((matrixEndAlgEquiv (Fin 2)).symm
    ((matrixEndAlgEquiv (Fin 2)) f.toLinearMap)) = _
  rw [AlgEquiv.symm_apply_apply]

/-- 对任意复 Pauli 输入，原超算子指数与真实 Bloch 指数作用相同。 -/
theorem generalizedState_evolution {n : ℕ} (H : QubitMatrix) (hH : H.IsHermitian)
    (A : Fin n → QubitMatrix) (t : ℝ) (v : BlochIndex → ℂ) :
    generalizedState
      ((canonicalEvolution (hamiltonianVector (canonicalHamiltonian H A))
        (kossakowski (fun μ => pauliCoeffs (A μ))) t).map Complex.ofReal *ᵥ v) =
      gkslSuperoperatorEvolution H A t (generalizedState v) := by
  have he := finiteEvolution_bloch_representation H hH A t
  rw [finiteEvolution_eq_superoperator_representation,
    liouvilleBlochAlgEquiv_superoperator] at he
  rw [← he, blochEndAlgEquiv_mulVec, LinearEquiv.apply_symm_apply]
  rfl

theorem real_matrix_mulVec_complex (Q : AugmentedMatrix) (v : AugmentedVector) :
    Q.map Complex.ofReal *ᵥ (fun i => (v i : ℂ)) =
      fun i => ((Q *ᵥ v) i : ℂ) := by
  funext i
  simp [Matrix.mulVec, dotProduct]

/-- 任意实迹、任意实时间的真实演化桥。 -/
theorem realGeneralizedState_evolution {n : ℕ} (H : QubitMatrix) (hH : H.IsHermitian)
    (A : Fin n → QubitMatrix) (t : ℝ) (v : AugmentedVector) :
    realGeneralizedState
      (canonicalEvolution (hamiltonianVector (canonicalHamiltonian H A))
        (kossakowski (fun μ => pauliCoeffs (A μ))) t *ᵥ v) =
      gkslSuperoperatorEvolution H A t (realGeneralizedState v) := by
  have he := generalizedState_evolution H hH A t (fun i => (v i : ℂ))
  rw [real_matrix_mulVec_complex] at he
  exact he

theorem matrix_exp_zero_row (Q : AugmentedMatrix) (hQ : ∀ j, Q 0 j = 0) (j : BlochIndex) :
    NormedSpace.exp Q 0 j = (1 : AugmentedMatrix) 0 j := by
  let P : AugmentedMatrix := Matrix.single 0 0 1
  have hc : SemiconjBy P Q 0 := by
    change P * Q = 0 * P
    ext i k
    fin_cases i <;>
      simp [P, Matrix.mul_apply, Matrix.single_apply, hQ]
  have he := hc.exp_right
  change P * NormedSpace.exp Q = NormedSpace.exp (0 : AugmentedMatrix) * P at he
  have hj := congrArg (fun B : AugmentedMatrix => B 0 j) he
  simpa [P, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.single_apply,
    Matrix.one_apply, NormedSpace.exp_zero] using hj

theorem canonicalEvolution_head (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ)
    (t : ℝ) (j : BlochIndex) :
    canonicalEvolution h K t 0 j = (1 : AugmentedMatrix) 0 j := by
  apply matrix_exp_zero_row
  intro k
  fin_cases k <;> simp [augmentedGenerator]

theorem realGeneralizedState_basis_zero :
    realGeneralizedState ![1, 0, 0, 1] = Matrix.single 0 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realGeneralizedState, generalizedState, pauli, Matrix.single_apply,
      Matrix.smul_apply, smul_eq_mul]

theorem realGeneralizedState_basis_one :
    realGeneralizedState ![1, 0, 0, -1] = Matrix.single 1 1 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realGeneralizedState, generalizedState, pauli, Matrix.single_apply,
      Matrix.smul_apply, smul_eq_mul]

/-- 原始概率读出恰好是同一个增广指数的两个坐标组合。 -/
theorem finiteOutput_eq_canonicalOutput {n : ℕ} (H : QubitMatrix) (hH : H.IsHermitian)
    (A : Fin n → QubitMatrix) (t : ℝ) :
    finiteOutput H A t =
      canonicalOutput (hamiltonianVector (canonicalHamiltonian H A))
        (kossakowski (fun μ => pauliCoeffs (A μ))) t := by
  have hz := realGeneralizedState_evolution H hH A t ![1, 0, 0, 1]
  have ho := realGeneralizedState_evolution H hH A t ![1, 0, 0, -1]
  rw [realGeneralizedState_basis_zero] at hz
  rw [realGeneralizedState_basis_one] at ho
  rw [finiteOutput_eq_superoperator_probabilities, ← hz, ← ho]
  simp [canonicalOutput, realGeneralizedState, generalizedState, pauli,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ, canonicalEvolution_head,
    Matrix.smul_apply, smul_eq_mul, Complex.mul_re]
  constructor <;> ring

theorem pauliCoeffs_pauli (l : PauliVec) : pauliCoeffs (pauli l) = l := by
  funext i
  fin_cases i <;> simp [pauliCoeffs, pauli]
  all_goals ring_nf
  all_goals simp [Complex.I_sq]

theorem scalarPart_pauli (l : PauliVec) : scalarPart (pauli l) = 0 := by
  simp [scalarPart, pauli]

theorem canonicalHamiltonian_pauli {n : ℕ} (H : QubitMatrix) (l : Fin n → PauliVec) :
    canonicalHamiltonian H (fun μ => pauli (l μ)) = H := by
  simp [canonicalHamiltonian, scalarPart_pauli, gaugeHamiltonian]

theorem hamiltonianVector_hamiltonian (h : BlochVec) :
    hamiltonianVector (hamiltonian h) = h :=
  hamiltonianVector_blochDerivative h

theorem finiteOutput_canonical_pauli {n : ℕ} (h : BlochVec) (l : Fin n → PauliVec) (t : ℝ) :
    finiteOutput (hamiltonian h) (fun μ => pauli (l μ)) t =
      canonicalOutput h (kossakowski l) t := by
  rw [finiteOutput_eq_canonicalOutput _ (hamiltonian_hermitian h),
    canonicalHamiltonian_pauli, hamiltonianVector_hamiltonian]
  simp only [pauliCoeffs_pauli]

/-- 任意规范 PSD 参数的整条真实演化由同一组三个有限跳跃实现。 -/
theorem exists_evolution_for_canonical (h : BlochVec)
    (K : Matrix (Fin 3) (Fin 3) ℂ) (hK : K.PosSemidef) :
    ∃ A : Fin 3 → QubitMatrix, ∀ (t : ℝ) (v : AugmentedVector),
      realGeneralizedState (canonicalEvolution h K t *ᵥ v) =
        gkslSuperoperatorEvolution (hamiltonian h) A t (realGeneralizedState v) := by
  obtain ⟨l, hl⟩ := exists_kossakowski_factor K hK
  refine ⟨fun μ => pauli (l μ), ?_⟩
  intro t v
  have he := realGeneralizedState_evolution (hamiltonian h) (hamiltonian_hermitian h)
    (fun μ => pauli (l μ)) t v
  simpa only [canonicalHamiltonian_pauli, hamiltonianVector_hamiltonian,
    pauliCoeffs_pauli, hl] using he

/-- 每个合法规范参数都有同一组三个有限跳跃，匹配所有实时间的输出。 -/
theorem exists_finiteOutput_for_canonical (h : BlochVec)
    (K : Matrix (Fin 3) (Fin 3) ℂ) (hK : K.PosSemidef) :
    ∃ A : Fin 3 → QubitMatrix, ∀ t : ℝ,
      finiteOutput (hamiltonian h) A t = canonicalOutput h K t := by
  obtain ⟨l, hl⟩ := exists_kossakowski_factor K hK
  refine ⟨fun μ => pauli (l μ), ?_⟩
  intro t
  simpa only [hl] using finiteOutput_canonical_pauli h l t

theorem unitTimeOutputs_eq_canonicalOutputs : unitTimeOutputs = canonicalOutputs := by
  ext p
  constructor
  · rintro ⟨n, H, A, hH, hp⟩
    refine ⟨hamiltonianVector (canonicalHamiltonian H A),
      kossakowski (fun μ => pauliCoeffs (A μ)), kossakowski_posSemidef _, ?_⟩
    rw [← finiteOutput_eq_canonicalOutput H hH A]
    exact hp
  · rintro ⟨h, K, hK, hp⟩
    obtain ⟨A, hA⟩ := exists_finiteOutput_for_canonical h K hK
    exact ⟨3, hamiltonian h, A, hamiltonian_hermitian h, (hA 1).trans hp⟩

theorem Q2_eq_closure_canonicalOutputs : Q2 = closure canonicalOutputs := by
  rw [Q2_eq_closure_unitTimeOutputs, unitTimeOutputs_eq_canonicalOutputs]

theorem finiteOutputs_eq_canonicalOutputs : finiteOutputs = canonicalOutputs := by
  rw [finiteOutputs_eq_unitTimeOutputs, unitTimeOutputs_eq_canonicalOutputs]

theorem canonicalOutput_mem_Q2 (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ)
    (hK : K.PosSemidef) (t : ℝ) (ht : 0 ≤ t) : canonicalOutput h K t ∈ Q2 := by
  obtain ⟨A, hA⟩ := exists_finiteOutput_for_canonical h K hK
  rw [← hA t]
  exact finiteOutput_mem_Q2 _ _ _ (hamiltonian_hermitian h) ht

#print axioms generalizedState
#print axioms gkslAction_realGeneralizedState
#print axioms finiteEvolution_bloch_representation
#print axioms generalizedState_evolution
#print axioms realGeneralizedState_evolution
#print axioms canonicalEvolution_head
#print axioms finiteOutput_eq_canonicalOutput
#print axioms exists_evolution_for_canonical
#print axioms exists_finiteOutput_for_canonical
#print axioms unitTimeOutputs_eq_canonicalOutputs
#print axioms Q2_eq_closure_canonicalOutputs

end TwoStateQuantumEmbedding.CanonicalBloch
