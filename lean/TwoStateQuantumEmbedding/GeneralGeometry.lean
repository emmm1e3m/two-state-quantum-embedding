import TwoStateQuantumEmbedding.Geometry
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Analysis.Matrix.Order

set_option maxRecDepth 3000
set_option maxHeartbeats 1600000

open Matrix
open scoped ComplexOrder MatrixOrder

namespace TwoState.GeneralGeometry

abbrev V3 := Fin 3 → ℝ
abbrev M3 := Matrix (Fin 3) (Fin 3) ℝ
abbrev C3 := Matrix (Fin 3) (Fin 3) ℂ

def crossMat (d : V3) : M3 :=
  !![0, -d 2, d 1; d 2, 0, -d 0; -d 1, d 0, 0]

def complexify (S : M3) : C3 := S.map Complex.ofReal

def canonical (S : M3) (d : V3) : C3 :=
  complexify S + Complex.I • complexify (crossMat d)

def Orthogonal (R : M3) : Prop := R.transpose * R = 1 ∧ R * R.transpose = 1

theorem canonical_diagonal (s d : V3) :
    canonical (Matrix.diagonal s) d =
      TwoState.Geometry.driftMatrix (s 0) (s 1) (s 2) (d 0) (d 1) (d 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [canonical, complexify, crossMat, TwoState.Geometry.driftMatrix,
      Matrix.diagonal]

/- 对任意矩阵的余子式协变，保留反射的行列式符号。 -/
theorem crossMat_congruence (R : M3) (d : V3) :
    R * crossMat d * R.transpose = crossMat (R.transpose.adjugate *ᵥ d) := by
  rw [Matrix.adjugate_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [crossMat, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.transpose_apply] <;> ring

theorem orthogonal_adjugate (R : M3) (hR : Orthogonal R) :
    R.adjugate = R.det • R.transpose := by
  calc
    R.adjugate = R.adjugate * (R * R.transpose) := by rw [hR.2, Matrix.mul_one]
    _ = (R.adjugate * R) * R.transpose := by rw [Matrix.mul_assoc]
    _ = R.det • R.transpose := by rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]

theorem orthogonal_transpose (R : M3) (hR : Orthogonal R) : Orthogonal R.transpose := by
  simpa [Orthogonal] using And.intro hR.2 hR.1

theorem orthogonal_det_sq (R : M3) (hR : Orthogonal R) : R.det * R.det = 1 := by
  have h := congrArg Matrix.det hR.2
  simpa [Matrix.det_mul, Matrix.det_transpose] using h

theorem orthogonal_crossMat (R : M3) (hR : Orthogonal R) (d : V3) :
    R * crossMat d * R.transpose = crossMat (R.det • (R *ᵥ d)) := by
  rw [crossMat_congruence, orthogonal_adjugate R.transpose (orthogonal_transpose R hR)]
  simp [Matrix.det_transpose, Matrix.smul_mulVec]

theorem orthogonal_adjugate_congruence (R S : M3) (hR : Orthogonal R) :
    (R*S*R.transpose).adjugate = R*S.adjugate*R.transpose := by
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib,
    orthogonal_adjugate R.transpose (orthogonal_transpose R hR), orthogonal_adjugate R hR]
  simp only [Matrix.det_transpose, Matrix.transpose_transpose,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, orthogonal_det_sq R hR, one_smul]
  rw [Matrix.mul_assoc]

/- 使用 mathlib 的实际 Hermitian 谱定理选取正交特征基。 -/
theorem exists_orthogonal_diagonalization (S : M3) (hS : S.PosSemidef) :
    ∃ (R : M3) (s : V3), Orthogonal R ∧ (∀ i, 0 ≤ s i) ∧
      S = R * Matrix.diagonal s * R.transpose := by
  let U := hS.isHermitian.eigenvectorUnitary
  refine ⟨U, hS.isHermitian.eigenvalues, ?_, hS.eigenvalues_nonneg, ?_⟩
  · constructor
    · simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
        Unitary.coe_star_mul_self U
    · simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial] using
        Unitary.coe_mul_star_self U
  · simpa [U, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      hS.isHermitian.spectral_theorem

@[simp] theorem complexify_mul (A B : M3) :
    complexify (A*B) = complexify A * complexify B := by
  exact Matrix.map_mul (f := Complex.ofRealHom)

@[simp] theorem complexify_transpose (A : M3) :
    complexify A.transpose = (complexify A).conjTranspose := by
  ext i j
  simp [complexify, Matrix.conjTranspose_apply]

@[simp] theorem complexify_one : complexify (1 : M3) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [complexify, Matrix.one_apply, h]

theorem canonical_congruence (R S : M3) (hR : Orthogonal R) (d : V3) :
    complexify R * canonical S d * (complexify R).conjTranspose =
      canonical (R*S*R.transpose) (R.det • (R *ᵥ d)) := by
  unfold canonical
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [← complexify_transpose, ← complexify_mul, ← complexify_mul,
    ← complexify_mul, ← complexify_mul, orthogonal_crossMat R hR]

theorem posSemidef_congruence_iff (A U : C3) (hU : U.conjTranspose*U = 1) :
    (U*A*U.conjTranspose).PosSemidef ↔ A.PosSemidef := by
  constructor
  · intro h
    have hh := h.conjTranspose_mul_mul_same U
    have he : U.conjTranspose*(U*A*U.conjTranspose)*U =
        (U.conjTranspose*U)*A*(U.conjTranspose*U) := by simp only [Matrix.mul_assoc]
    rw [he, hU, Matrix.one_mul, Matrix.mul_one] at hh
    exact hh
  · intro h
    exact h.mul_mul_conjTranspose_same U

theorem canonical_posSemidef_congruence_iff (R S : M3)
    (hR : Orthogonal R) (d : V3) :
    (canonical (R*S*R.transpose) (R.det • (R*ᵥd))).PosSemidef ↔
      (canonical S d).PosSemidef := by
  rw [← canonical_congruence R S hR d]
  apply posSemidef_congruence_iff
  rw [← complexify_transpose, ← complexify_mul, hR.1, complexify_one]

theorem orthogonal_mulVec_inverse (R : M3) (hR : Orthogonal R) (d : V3) :
    R*ᵥ(R.transpose*ᵥd) = d := by
  rw [Matrix.mulVec_mulVec, hR.2, Matrix.one_mulVec]

theorem orthogonal_signed_inverse (R : M3) (hR : Orthogonal R) (d : V3) :
    R.det • (R*ᵥ(R.det • (R.transpose*ᵥd))) = d := by
  rw [Matrix.mulVec_smul, smul_smul, orthogonal_det_sq R hR, one_smul,
    orthogonal_mulVec_inverse R hR]

theorem canonical_posSemidef_in_basis (R S : M3) (hR : Orthogonal R) (d : V3) :
    (canonical (R*S*R.transpose) d).PosSemidef ↔
      (canonical S (R.det • (R.transpose*ᵥd))).PosSemidef := by
  have h := canonical_posSemidef_congruence_iff R S hR (R.det • (R.transpose*ᵥd))
  simpa only [orthogonal_signed_inverse R hR] using h

/- 欧氏点积在两种取向的正交基变换下保持。 -/
theorem orthogonal_dot (R : M3) (hR : Orthogonal R) (u v : V3) :
    (R*ᵥu) ⬝ᵥ (R*ᵥv) = u ⬝ᵥ v := by
  rw [← Matrix.dotProduct_transpose_mulVec R v (R*ᵥu),
    Matrix.mulVec_mulVec, hR.1, Matrix.one_mulVec, dotProduct_comm]

theorem orthogonal_signed_dot (R : M3) (hR : Orthogonal R) (u v : V3) :
    (R.det • (R*ᵥu)) ⬝ᵥ (R.det • (R*ᵥv)) = u ⬝ᵥ v := by
  rw [smul_dotProduct, dotProduct_smul, smul_smul, orthogonal_det_sq R hR,
    one_smul, orthogonal_dot R hR]

def pairProducts (s : V3) : V3 := ![s 1*s 2, s 0*s 2, s 0*s 1]

theorem adjugate_diagonal_three (s : V3) :
    (Matrix.diagonal s).adjugate = Matrix.diagonal (pairProducts s) := by
  rw [Matrix.adjugate_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, pairProducts]

theorem pairProducts_nonneg (s : V3) (hs : ∀ i, 0 ≤ s i) :
    ∀ i, 0 ≤ pairProducts s i := by
  intro i
  fin_cases i
  · exact mul_nonneg (hs 1) (hs 2)
  · exact mul_nonneg (hs 0) (hs 2)
  · exact mul_nonneg (hs 0) (hs 1)

theorem adjugate_posSemidef (S : M3) (hS : S.PosSemidef) : S.adjugate.PosSemidef := by
  obtain ⟨R, s, hR, hs, he⟩ := exists_orthogonal_diagonalization S hS
  rw [he, orthogonal_adjugate_congruence R _ hR, adjugate_diagonal_three]
  have hd := Matrix.PosSemidef.diagonal
    (show (0 : V3) ≤ pairProducts s from pairProducts_nonneg s hs)
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hd.mul_mul_conjTranspose_same R

noncomputable def diagonalRoot (s : V3) : M3 :=
  Matrix.diagonal (fun i => Real.sqrt (pairProducts s i))

theorem diagonalRoot_posSemidef (s : V3) : (diagonalRoot s).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  exact Real.sqrt_nonneg _

theorem diagonalRoot_square (s : V3) (hs : ∀ i, 0 ≤ s i) :
    diagonalRoot s * diagonalRoot s = Matrix.diagonal (pairProducts s) := by
  rw [diagonalRoot, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact Real.mul_self_sqrt (pairProducts_nonneg s hs i)

theorem conjugatedRoot_square (R : M3) (hR : Orthogonal R) (s : V3)
    (hs : ∀ i, 0 ≤ s i) :
    (R*diagonalRoot s*R.transpose)*(R*diagonalRoot s*R.transpose) =
      (R*Matrix.diagonal s*R.transpose).adjugate := by
  rw [orthogonal_adjugate_congruence R _ hR, adjugate_diagonal_three]
  calc
    _ = R*diagonalRoot s*(R.transpose*R)*diagonalRoot s*R.transpose := by
      simp only [Matrix.mul_assoc]
    _ = R*(diagonalRoot s*diagonalRoot s)*R.transpose := by
      rw [hR.1, Matrix.mul_one, Matrix.mul_assoc R]
    _ = _ := by rw [diagonalRoot_square s hs]

open scoped MatrixOrder in
theorem sqrt_adjugate_in_basis (R : M3) (hR : Orthogonal R) (s : V3)
    (hs : ∀ i, 0 ≤ s i) :
    CFC.sqrt ((R*Matrix.diagonal s*R.transpose).adjugate) =
      R*diagonalRoot s*R.transpose := by
  have hp : (R*diagonalRoot s*R.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (diagonalRoot_posSemidef s).mul_mul_conjTranspose_same R
  exact CFC.sqrt_unique (conjugatedRoot_square R hR s hs) hp.nonneg

theorem canonical_diagonal_iff_ball (s d : V3) (hs : ∀ i, 0 ≤ s i) :
    (canonical (Matrix.diagonal s) d).PosSemidef ↔
      ∃ u : V3, u ⬝ᵥ u ≤ 1 ∧ d = diagonalRoot s *ᵥ u := by
  rw [canonical_diagonal, TwoState.Geometry.driftMatrix_posSemidef_iff_ball
    _ _ _ _ _ _ (hs 0) (hs 1) (hs 2)]
  constructor
  · rintro ⟨u₁, u₂, u₃, hu, hd₁, hd₂, hd₃⟩
    refine ⟨![u₁,u₂,u₃], ?_, ?_⟩
    · simpa [dotProduct, Fin.sum_univ_succ, pow_two, add_assoc] using hu
    · funext i
      fin_cases i
      · simpa [diagonalRoot, Matrix.mulVec_diagonal, pairProducts] using hd₁
      · simpa [diagonalRoot, Matrix.mulVec_diagonal, pairProducts] using hd₂
      · simpa [diagonalRoot, Matrix.mulVec_diagonal, pairProducts] using hd₃
  · rintro ⟨u, hu, hd⟩
    refine ⟨u 0, u 1, u 2, ?_, ?_, ?_, ?_⟩
    · simpa [dotProduct, Fin.sum_univ_succ, pow_two, add_assoc] using hu
    · simpa [diagonalRoot, Matrix.mulVec_diagonal, pairProducts] using congrFun hd 0
    · simpa [diagonalRoot, Matrix.mulVec_diagonal, pairProducts] using congrFun hd 1
    · simpa [diagonalRoot, Matrix.mulVec_diagonal, pairProducts] using congrFun hd 2

theorem conjugated_signed_mulVec (R A : M3) (hR : Orthogonal R) (u : V3) :
    (R*A*R.transpose)*ᵥ(R.det • (R*ᵥu)) = R.det • (R*ᵥ(A*ᵥu)) := by
  rw [Matrix.mulVec_smul]
  simp only [← Matrix.mulVec_mulVec]
  rw [Matrix.mulVec_mulVec u R.transpose R, hR.1, Matrix.one_mulVec]

theorem canonical_ball_in_basis (R : M3) (hR : Orthogonal R) (s d : V3)
    (hs : ∀ i, 0 ≤ s i) :
    (canonical (R*Matrix.diagonal s*R.transpose) d).PosSemidef ↔
      ∃ u : V3, u ⬝ᵥ u ≤ 1 ∧ d = (R*diagonalRoot s*R.transpose)*ᵥu := by
  rw [canonical_posSemidef_in_basis R _ hR, canonical_diagonal_iff_ball _ _ hs]
  constructor
  · rintro ⟨u, hu, hd⟩
    refine ⟨R.det • (R*ᵥu), ?_, ?_⟩
    · rw [orthogonal_signed_dot R hR]
      exact hu
    · rw [conjugated_signed_mulVec R _ hR, ← hd, orthogonal_signed_inverse R hR]
  · rintro ⟨u, hu, hd⟩
    refine ⟨R.det • (R.transpose*ᵥu), ?_, ?_⟩
    · have hn : (R.det • (R.transpose*ᵥu)) ⬝ᵥ (R.det • (R.transpose*ᵥu)) = u ⬝ᵥ u := by
        simpa only [Matrix.det_transpose] using
          orthogonal_signed_dot R.transpose (orthogonal_transpose R hR) u u
      rw [hn]
      exact hu
    · rw [hd]
      simp only [← Matrix.mulVec_mulVec]
      rw [Matrix.mulVec_mulVec (diagonalRoot s *ᵥ (R.transpose*ᵥu)) R.transpose R,
        hR.1, Matrix.one_mulVec,
        Matrix.mulVec_smul]

/- 一般PSD实部的坐标无关椭球，包含全部退化情况。 -/
theorem canonical_posSemidef_iff_sqrt_ball (S : M3) (hS : S.PosSemidef) (d : V3) :
    (canonical S d).PosSemidef ↔
      ∃ u : V3, u ⬝ᵥ u ≤ 1 ∧ d = (CFC.sqrt S.adjugate)*ᵥu := by
  obtain ⟨R, s, hR, hs, he⟩ := exists_orthogonal_diagonalization S hS
  rw [he, sqrt_adjugate_in_basis R hR s hs, canonical_ball_in_basis R hR s d hs]

theorem unitBall_linear_image (w : V3) (z : ℝ) :
    (∃ u : V3, u ⬝ᵥ u ≤ 1 ∧ z = w ⬝ᵥ u) ↔ |z| ≤ Real.sqrt (w ⬝ᵥ w) := by
  have hw : w ⬝ᵥ w = (w 0)^2+(w 1)^2+(w 2)^2 := by
    simp [dotProduct, Fin.sum_univ_succ, pow_two, add_assoc]
  rw [hw, ← TwoState.Geometry.ball3_linear_image]
  constructor
  · rintro ⟨u, hu, hz⟩
    refine ⟨u 0, u 1, u 2, ?_, ?_⟩
    · simpa [dotProduct, Fin.sum_univ_succ, pow_two, add_assoc] using hu
    · simpa [dotProduct, Fin.sum_univ_succ, add_assoc] using hz
  · rintro ⟨u₁, u₂, u₃, hu, hz⟩
    refine ⟨![u₁,u₂,u₃], ?_, ?_⟩
    · simpa [dotProduct, Fin.sum_univ_succ, pow_two, add_assoc] using hu
    · simpa [dotProduct, Fin.sum_univ_succ, add_assoc] using hz

theorem matrix_ball_linear_image (A : M3) (l : V3) (z : ℝ) :
    (∃ u : V3, u ⬝ᵥ u ≤ 1 ∧ z = l ⬝ᵥ (A*ᵥu)) ↔
      |z| ≤ Real.sqrt ((A.transpose*ᵥl) ⬝ᵥ (A.transpose*ᵥl)) := by
  have he (u : V3) : l ⬝ᵥ (A*ᵥu) = (A.transpose*ᵥl) ⬝ᵥ u := by
    rw [← Matrix.dotProduct_transpose_mulVec A u l, dotProduct_comm]
  simp_rw [he]
  exact unitBall_linear_image _ _

theorem sqrt_adjugate_dot (S : M3) (hS : S.PosSemidef) (l : V3) :
    ((CFC.sqrt S.adjugate).transpose*ᵥl) ⬝ᵥ
        ((CFC.sqrt S.adjugate).transpose*ᵥl) = l ⬝ᵥ (S.adjugate*ᵥl) := by
  have hp : (CFC.sqrt S.adjugate).PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  have ht : (CFC.sqrt S.adjugate).transpose = CFC.sqrt S.adjugate := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hp.isHermitian.eq
  have hsq := CFC.sqrt_mul_sqrt_self S.adjugate (adjugate_posSemidef S hS).nonneg
  rw [Matrix.dotProduct_transpose_mulVec (CFC.sqrt S.adjugate)
    ((CFC.sqrt S.adjugate).transpose*ᵥl) l, Matrix.mulVec_mulVec, ht, hsq]

/- 一般实部下的完整支撑区间，端点和中间值均已包含。 -/
theorem canonical_linear_image (S : M3) (hS : S.PosSemidef) (l : V3) (z : ℝ) :
    (∃ d : V3, (canonical S d).PosSemidef ∧ z = l ⬝ᵥ d) ↔
      |z| ≤ Real.sqrt (l ⬝ᵥ (S.adjugate*ᵥl)) := by
  have he : (∃ d : V3, (canonical S d).PosSemidef ∧ z = l ⬝ᵥ d) ↔
      (∃ u : V3, u ⬝ᵥ u ≤ 1 ∧ z = l ⬝ᵥ ((CFC.sqrt S.adjugate)*ᵥu)) := by
    constructor
    · rintro ⟨d, hd, hz⟩
      obtain ⟨u, hu, he⟩ := (canonical_posSemidef_iff_sqrt_ball S hS d).mp hd
      exact ⟨u, hu, by rw [← he]; exact hz⟩
    · rintro ⟨u, hu, hz⟩
      exact ⟨(CFC.sqrt S.adjugate)*ᵥu,
        (canonical_posSemidef_iff_sqrt_ball S hS _).mpr ⟨u, hu, rfl⟩, hz⟩
  rw [he, matrix_ball_linear_image, sqrt_adjugate_dot S hS]

noncomputable def physicalCanonical (S : M3) (c : V3) : C3 := canonical S ((1/4 : ℝ) • c)

theorem crossMat_smul (r : ℝ) (d : V3) : crossMat (r • d) = r • crossMat d := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [crossMat]

theorem complexify_smul (r : ℝ) (S : M3) :
    complexify (r • S) = (r : ℂ) • complexify S := by
  ext i j
  simp [complexify, smul_eq_mul]

/- 此处的矩阵严格等于论文 K=S+i[c]×/4，而非改写过的PSD谓词。 -/
theorem physicalCanonical_eq (S : M3) (c : V3) :
    physicalCanonical S c = complexify S + (Complex.I/4) • complexify (crossMat c) := by
  unfold physicalCanonical canonical
  rw [crossMat_smul, complexify_smul, smul_smul]
  norm_num [div_eq_mul_inv]

theorem physicalCanonical_posSemidef_iff_ball (S : M3) (hS : S.PosSemidef) (c : V3) :
    (physicalCanonical S c).PosSemidef ↔
      ∃ u : V3, u ⬝ᵥ u ≤ 1 ∧ c = (4 : ℝ) • ((CFC.sqrt S.adjugate)*ᵥu) := by
  rw [physicalCanonical, canonical_posSemidef_iff_sqrt_ball S hS]
  constructor <;> rintro ⟨u, hu, he⟩ <;> refine ⟨u, hu, ?_⟩ <;>
    funext i <;> have hi := congrFun he i <;>
    simp only [Pi.smul_apply, smul_eq_mul] at hi ⊢ <;> linarith

theorem physicalCanonical_linear_image (S : M3) (hS : S.PosSemidef) (l : V3) (z : ℝ) :
    (∃ c : V3, (physicalCanonical S c).PosSemidef ∧ z = l ⬝ᵥ c) ↔
      |z| ≤ 4*Real.sqrt (l ⬝ᵥ (S.adjugate*ᵥl)) := by
  have he : (∃ c : V3, (physicalCanonical S c).PosSemidef ∧ z = l ⬝ᵥ c) ↔
      (∃ d : V3, (canonical S d).PosSemidef ∧ z/4 = l ⬝ᵥ d) := by
    constructor
    · rintro ⟨c, hc, hz⟩
      refine ⟨(1/4 : ℝ) • c, hc, ?_⟩
      rw [dotProduct_smul, ← hz]
      simp [smul_eq_mul]
      ring
    · rintro ⟨d, hd, hz⟩
      refine ⟨(4 : ℝ) • d, ?_, ?_⟩
      · simpa [physicalCanonical, smul_smul] using hd
      · rw [dotProduct_smul]
        simp only [smul_eq_mul]
        linarith
  rw [he, canonical_linear_image S hS, abs_div]
  norm_num
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
  ring_nf

theorem physicalCanonical_max_attained (S : M3) (hS : S.PosSemidef) (l : V3) :
    ∃ c : V3, (physicalCanonical S c).PosSemidef ∧
      l ⬝ᵥ c = 4*Real.sqrt (l ⬝ᵥ (S.adjugate*ᵥl)) := by
  obtain ⟨c, hc, he⟩ := (physicalCanonical_linear_image S hS l
    (4*Real.sqrt (l ⬝ᵥ (S.adjugate*ᵥl)))).mpr
    (by rw [abs_of_nonneg (by positivity)])
  exact ⟨c, hc, he.symm⟩

theorem adjugate_quadratic_nonneg (S : M3) (hS : S.PosSemidef) (l : V3) :
    0 ≤ l ⬝ᵥ (S.adjugate*ᵥl) := by
  simpa only [star_trivial] using (adjugate_posSemidef S hS).dotProduct_mulVec_nonneg l

theorem physicalCanonical_isGreatest (S : M3) (hS : S.PosSemidef) (l : V3) :
    IsGreatest {z : ℝ | ∃ c : V3, (physicalCanonical S c).PosSemidef ∧ z = l ⬝ᵥ c}
      (4*Real.sqrt (l ⬝ᵥ (S.adjugate*ᵥl))) := by
  constructor
  · exact (physicalCanonical_linear_image S hS l _).mpr
      (by rw [abs_of_nonneg (by positivity)])
  · intro z hz
    exact (le_abs_self z).trans ((physicalCanonical_linear_image S hS l z).mp hz)

#print axioms crossMat_congruence
#print axioms orthogonal_crossMat
#print axioms orthogonal_adjugate_congruence
#print axioms exists_orthogonal_diagonalization
#print axioms adjugate_posSemidef
#print axioms sqrt_adjugate_in_basis
#print axioms canonical_posSemidef_iff_sqrt_ball
#print axioms physicalCanonical_eq
#print axioms physicalCanonical_posSemidef_iff_ball
#print axioms physicalCanonical_linear_image
#print axioms physicalCanonical_max_attained
#print axioms adjugate_quadratic_nonneg
#print axioms physicalCanonical_isGreatest

end TwoState.GeneralGeometry
