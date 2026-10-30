import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

set_option maxRecDepth 2000
set_option maxHeartbeats 800000

/-! 对角实部的漂移矩阵；漂移变量 d 等于论文 c/4。 -/
open Matrix
open scoped ComplexOrder

namespace TwoState.Geometry

def driftMatrix (s₁ s₂ s₃ d₁ d₂ d₃ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(s₁ : ℂ), -Complex.I * d₃, Complex.I * d₂;
     Complex.I * d₃, (s₂ : ℂ), -Complex.I * d₁;
     -Complex.I * d₂, Complex.I * d₁, (s₃ : ℂ)]

theorem driftMatrix_hermitian (s₁ s₂ s₃ d₁ d₂ d₃ : ℝ) :
    (driftMatrix s₁ s₂ s₃ d₁ d₂ d₃).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [driftMatrix, Matrix.conjTranspose_apply]

theorem driftMatrix_det (s₁ s₂ s₃ d₁ d₂ d₃ : ℝ) :
    (driftMatrix s₁ s₂ s₃ d₁ d₂ d₃).det =
      ((s₁*s₂*s₃ - s₁*d₁^2-s₂*d₂^2-s₃*d₃^2 : ℝ) : ℂ) := by
  rw [Matrix.det_fin_three]
  simp [driftMatrix]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, pow_two] <;> ring

theorem driftMatrix_charpoly_re (s₁ s₂ s₃ d₁ d₂ d₃ t : ℝ) :
    ((driftMatrix s₁ s₂ s₃ d₁ d₂ d₃).charpoly.eval (t : ℂ)).re =
    t^3 - (s₁+s₂+s₃)*t^2 +
      (s₁*s₂-d₃^2 + (s₁*s₃-d₂^2) + (s₂*s₃-d₁^2))*t -
      (s₁*s₂*s₃-s₁*d₁^2-s₂*d₂^2-s₃*d₃^2) := by
  rw [Matrix.eval_charpoly, Matrix.det_fin_three]
  simp [driftMatrix, Matrix.scalar, Matrix.diagonal, Complex.mul_re,
    Complex.mul_im, pow_two]
  ring

/- 三阶 Hermitian 情形的充分方向用实际实谱证明，不假设主子式判据。 -/
theorem driftMatrix_posSemidef_of_conditions
    (s₁ s₂ s₃ d₁ d₂ d₃ : ℝ)
    (h₁ : 0 ≤ s₁) (h₂ : 0 ≤ s₂) (h₃ : 0 ≤ s₃)
    (h₁₂ : 0 ≤ s₁*s₂-d₃^2) (h₁₃ : 0 ≤ s₁*s₃-d₂^2)
    (h₂₃ : 0 ≤ s₂*s₃-d₁^2)
    (hdet : 0 ≤ s₁*s₂*s₃-s₁*d₁^2-s₂*d₂^2-s₃*d₃^2) :
    (driftMatrix s₁ s₂ s₃ d₁ d₂ d₃).PosSemidef := by
  let hH := driftMatrix_hermitian s₁ s₂ s₃ d₁ d₂ d₃
  apply hH.posSemidef_iff_eigenvalues_nonneg.mpr
  intro i
  let t : ℝ := hH.eigenvalues i
  change 0 ≤ t
  have he : (driftMatrix s₁ s₂ s₃ d₁ d₂ d₃).charpoly.eval (t : ℂ) = 0 := by
    rw [hH.charpoly_eq]
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [t]
  have hp := congrArg Complex.re he
  rw [driftMatrix_charpoly_re] at hp
  simp only [Complex.zero_re] at hp
  by_contra hn
  have ht : t < 0 := lt_of_not_ge hn
  have ht2 : 0 < t^2 := sq_pos_of_neg ht
  have ht3 : t^3 < 0 := by
    have := mul_neg_of_pos_of_neg ht2 ht
    nlinarith
  have htrace : 0 ≤ s₁+s₂+s₃ := by linarith
  have hpair : 0 ≤ s₁*s₂-d₃^2+(s₁*s₃-d₂^2)+(s₂*s₃-d₁^2) := by linarith
  have ha := mul_nonneg htrace (sq_nonneg t)
  have hb := mul_nonpos_of_nonneg_of_nonpos hpair ht.le
  linarith

theorem driftMatrix_posSemidef_iff (s₁ s₂ s₃ d₁ d₂ d₃ : ℝ) :
    (driftMatrix s₁ s₂ s₃ d₁ d₂ d₃).PosSemidef ↔
      0 ≤ s₁ ∧ 0 ≤ s₂ ∧ 0 ≤ s₃ ∧
      0 ≤ s₁*s₂-d₃^2 ∧ 0 ≤ s₁*s₃-d₂^2 ∧ 0 ≤ s₂*s₃-d₁^2 ∧
      0 ≤ s₁*s₂*s₃-s₁*d₁^2-s₂*d₂^2-s₃*d₃^2 := by
  constructor
  · intro h
    have h₁ := (Complex.nonneg_iff.mp (h.diag_nonneg (i := 0))).1
    have h₂ := (Complex.nonneg_iff.mp (h.diag_nonneg (i := 1))).1
    have h₃ := (Complex.nonneg_iff.mp (h.diag_nonneg (i := 2))).1
    have h₁₂ := (Complex.nonneg_iff.mp (h.submatrix ![(0 : Fin 3), 1]).det_nonneg).1
    have h₁₃ := (Complex.nonneg_iff.mp (h.submatrix ![(0 : Fin 3), 2]).det_nonneg).1
    have h₂₃ := (Complex.nonneg_iff.mp (h.submatrix ![(1 : Fin 3), 2]).det_nonneg).1
    rw [Matrix.det_fin_two] at h₁₂ h₁₃ h₂₃
    have hd := h.det_nonneg
    rw [driftMatrix_det, Complex.zero_le_real] at hd
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hd⟩
    · simpa [driftMatrix] using h₁
    · simpa [driftMatrix] using h₂
    · simpa [driftMatrix] using h₃
    · simpa [Matrix.det_fin_two, driftMatrix, Matrix.submatrix_apply,
        Complex.mul_re, Complex.mul_im, pow_two] using h₁₂
    · simpa [Matrix.det_fin_two, driftMatrix, Matrix.submatrix_apply,
        Complex.mul_re, Complex.mul_im, pow_two] using h₁₃
    · simpa [Matrix.det_fin_two, driftMatrix, Matrix.submatrix_apply,
        Complex.mul_re, Complex.mul_im, pow_two] using h₂₃
  · rintro ⟨h₁, h₂, h₃, h₁₂, h₁₃, h₂₃, hd⟩
    exact driftMatrix_posSemidef_of_conditions _ _ _ _ _ _ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hd

/- 一维闭球的缩放表述，包含零半径。 -/
theorem square_le_iff_scaled (d r : ℝ) (hr : 0 ≤ r) :
    d^2 ≤ r^2 ↔ ∃ u : ℝ, u^2 ≤ 1 ∧ d = r*u := by
  constructor
  · intro hd
    by_cases hz : r = 0
    · have hd0 : d = 0 := by nlinarith [sq_nonneg d]
      exact ⟨0, by norm_num, by simp [hz, hd0]⟩
    · have hp : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
      refine ⟨d/r, ?_, ?_⟩
      · rw [div_pow]
        exact (div_le_one (sq_pos_of_pos hp)).2 hd
      · field_simp
  · rintro ⟨u, hu, rfl⟩
    have := mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hu)
    nlinarith

/- 对角实部：完整球参数，所有退化情形均保留。 -/
theorem driftMatrix_posSemidef_iff_ball
    (s₁ s₂ s₃ d₁ d₂ d₃ : ℝ)
    (h₁ : 0 ≤ s₁) (h₂ : 0 ≤ s₂) (h₃ : 0 ≤ s₃) :
    (driftMatrix s₁ s₂ s₃ d₁ d₂ d₃).PosSemidef ↔
      ∃ u₁ u₂ u₃ : ℝ, u₁^2+u₂^2+u₃^2 ≤ 1 ∧
        d₁ = Real.sqrt (s₂*s₃)*u₁ ∧
        d₂ = Real.sqrt (s₁*s₃)*u₂ ∧
        d₃ = Real.sqrt (s₁*s₂)*u₃ := by
  rw [driftMatrix_posSemidef_iff]
  constructor
  · rintro ⟨_, _, _, h₁₂, h₁₃, h₂₃, hd⟩
    by_cases hz₁ : s₁ = 0
    · have hd₂ : d₂ = 0 := by simp [hz₁] at h₁₃; nlinarith [sq_nonneg d₂]
      have hd₃ : d₃ = 0 := by simp [hz₁] at h₁₂; nlinarith [sq_nonneg d₃]
      obtain ⟨u, hu, he⟩ := (square_le_iff_scaled d₁ (Real.sqrt (s₂*s₃))
        (Real.sqrt_nonneg _)).mp (by rw [Real.sq_sqrt (mul_nonneg h₂ h₃)]; linarith)
      exact ⟨u, 0, 0, by simpa using hu, he, by simp [hd₂], by simp [hd₃]⟩
    by_cases hz₂ : s₂ = 0
    · have hd₁ : d₁ = 0 := by simp [hz₂] at h₂₃; nlinarith [sq_nonneg d₁]
      have hd₃ : d₃ = 0 := by simp [hz₂] at h₁₂; nlinarith [sq_nonneg d₃]
      obtain ⟨u, hu, he⟩ := (square_le_iff_scaled d₂ (Real.sqrt (s₁*s₃))
        (Real.sqrt_nonneg _)).mp (by rw [Real.sq_sqrt (mul_nonneg h₁ h₃)]; linarith)
      exact ⟨0, u, 0, by simpa using hu, by simp [hd₁], he, by simp [hd₃]⟩
    by_cases hz₃ : s₃ = 0
    · have hd₁ : d₁ = 0 := by simp [hz₃] at h₂₃; nlinarith [sq_nonneg d₁]
      have hd₂ : d₂ = 0 := by simp [hz₃] at h₁₃; nlinarith [sq_nonneg d₂]
      obtain ⟨u, hu, he⟩ := (square_le_iff_scaled d₃ (Real.sqrt (s₁*s₂))
        (Real.sqrt_nonneg _)).mp (by rw [Real.sq_sqrt (mul_nonneg h₁ h₂)]; linarith)
      exact ⟨0, 0, u, by simpa using hu, by simp [hd₁], by simp [hd₂], he⟩
    have hp₁ : 0 < s₁ := lt_of_le_of_ne h₁ (Ne.symm hz₁)
    have hp₂ : 0 < s₂ := lt_of_le_of_ne h₂ (Ne.symm hz₂)
    have hp₃ : 0 < s₃ := lt_of_le_of_ne h₃ (Ne.symm hz₃)
    have hr₁ := Real.sqrt_pos.2 (mul_pos hp₂ hp₃)
    have hr₂ := Real.sqrt_pos.2 (mul_pos hp₁ hp₃)
    have hr₃ := Real.sqrt_pos.2 (mul_pos hp₁ hp₂)
    refine ⟨d₁/Real.sqrt (s₂*s₃), d₂/Real.sqrt (s₁*s₃),
      d₃/Real.sqrt (s₁*s₂), ?_, ?_, ?_, ?_⟩
    · have heq : (d₁/Real.sqrt (s₂*s₃))^2 + (d₂/Real.sqrt (s₁*s₃))^2 +
          (d₃/Real.sqrt (s₁*s₂))^2 =
          (s₁*d₁^2+s₂*d₂^2+s₃*d₃^2)/(s₁*s₂*s₃) := by
        rw [div_pow, div_pow, div_pow,
          Real.sq_sqrt (mul_nonneg h₂ h₃), Real.sq_sqrt (mul_nonneg h₁ h₃),
          Real.sq_sqrt (mul_nonneg h₁ h₂)]
        field_simp
      rw [heq]
      apply (div_le_one (mul_pos (mul_pos hp₁ hp₂) hp₃)).2
      linarith
    · field_simp
    · field_simp
    · field_simp
  · rintro ⟨u₁, u₂, u₃, hu, hd₁, hd₂, hd₃⟩
    have he₁ : d₁^2 = (s₂*s₃)*u₁^2 := by
      rw [hd₁, mul_pow, Real.sq_sqrt (mul_nonneg h₂ h₃)]
    have he₂ : d₂^2 = (s₁*s₃)*u₂^2 := by
      rw [hd₂, mul_pow, Real.sq_sqrt (mul_nonneg h₁ h₃)]
    have he₃ : d₃^2 = (s₁*s₂)*u₃^2 := by
      rw [hd₃, mul_pow, Real.sq_sqrt (mul_nonneg h₁ h₂)]
    have hu₁ : 0 ≤ 1-u₁^2 := by nlinarith [sq_nonneg u₂, sq_nonneg u₃]
    have hu₂ : 0 ≤ 1-u₂^2 := by nlinarith [sq_nonneg u₁, sq_nonneg u₃]
    have hu₃ : 0 ≤ 1-u₃^2 := by nlinarith [sq_nonneg u₁, sq_nonneg u₂]
    refine ⟨h₁, h₂, h₃, ?_, ?_, ?_, ?_⟩
    · rw [he₃]
      nlinarith [mul_nonneg (mul_nonneg h₁ h₂) hu₃]
    · rw [he₂]
      nlinarith [mul_nonneg (mul_nonneg h₁ h₃) hu₂]
    · rw [he₁]
      nlinarith [mul_nonneg (mul_nonneg h₂ h₃) hu₁]
    · rw [he₁, he₂, he₃]
      have hp := mul_nonneg (mul_nonneg (mul_nonneg h₁ h₂) h₃) (sub_nonneg.mpr hu)
      nlinarith

/- 共轭伙伴等于 Hermitian 矩阵的转置；这一步不要求实部对角化。 -/
theorem posSemidef_transpose_mix {n : Type*} [Fintype n]
    (K : Matrix n n ℂ) (hK : K.PosSemidef)
    (η : ℝ) (hηlo : -1 ≤ η) (hηhi : η ≤ 1) :
    (((1+η)/2 : ℝ) • K + ((1-η)/2 : ℝ) • K.transpose).PosSemidef := by
  exact (hK.smul (by linarith : 0 ≤ (1+η)/2)).add
    (hK.transpose.smul (by linarith : 0 ≤ (1-η)/2))

theorem driftMatrix_scale_identity (s₁ s₂ s₃ d₁ d₂ d₃ η : ℝ) :
    driftMatrix s₁ s₂ s₃ (η*d₁) (η*d₂) (η*d₃) =
      ((1+η)/2 : ℝ) • driftMatrix s₁ s₂ s₃ d₁ d₂ d₃ +
      ((1-η)/2 : ℝ) • (driftMatrix s₁ s₂ s₃ d₁ d₂ d₃).transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [driftMatrix, Matrix.transpose_apply, Complex.real_smul] <;> ring

theorem driftMatrix_scale_posSemidef (s₁ s₂ s₃ d₁ d₂ d₃ η : ℝ)
    (hK : (driftMatrix s₁ s₂ s₃ d₁ d₂ d₃).PosSemidef)
    (hηlo : -1 ≤ η) (hηhi : η ≤ 1) :
    (driftMatrix s₁ s₂ s₃ (η*d₁) (η*d₂) (η*d₃)).PosSemidef := by
  rw [driftMatrix_scale_identity]
  exact posSemidef_transpose_mix _ hK η hηlo hηhi

theorem transpose_mix_coordinates {n : Type*} (K : Matrix n n ℂ)
    (hK : K.IsHermitian) (η : ℝ) (i j : n) :
    ((((1+η)/2 : ℝ) • K + ((1-η)/2 : ℝ) • K.transpose) i j).re =
      (K i j).re ∧
    ((((1+η)/2 : ℝ) • K + ((1-η)/2 : ℝ) • K.transpose) i j).im =
      η*(K i j).im := by
  have hr := congrArg Complex.re (hK.apply i j)
  have hi := congrArg Complex.im (hK.apply i j)
  simp only [Complex.star_def, Complex.conj_re, Complex.conj_im] at hr hi
  have hi' : (K j i).im = -(K i j).im := by linarith
  constructor <;>
    simp [Matrix.transpose_apply, Complex.real_smul, hr, hi'] <;> ring

/- 三维球上线性泛函的全部像；必要方向显式使用平方和恒等式。 -/
theorem ball3_linear_image_sq (w₁ w₂ w₃ z : ℝ) :
    (∃ u₁ u₂ u₃ : ℝ, u₁^2+u₂^2+u₃^2 ≤ 1 ∧
      z = w₁*u₁+w₂*u₂+w₃*u₃) ↔ z^2 ≤ w₁^2+w₂^2+w₃^2 := by
  constructor
  · rintro ⟨u₁, u₂, u₃, hu, rfl⟩
    have hcs : (w₁*u₁+w₂*u₂+w₃*u₃)^2 ≤
        (w₁^2+w₂^2+w₃^2)*(u₁^2+u₂^2+u₃^2) := by
      nlinarith [sq_nonneg (w₁*u₂-w₂*u₁), sq_nonneg (w₁*u₃-w₃*u₁),
        sq_nonneg (w₂*u₃-w₃*u₂)]
    have hw : 0 ≤ w₁^2+w₂^2+w₃^2 := by positivity
    have hm := mul_nonneg hw (sub_nonneg.mpr hu)
    nlinarith
  · intro hz
    let R := w₁^2+w₂^2+w₃^2
    have hR : 0 ≤ R := by dsimp [R]; positivity
    by_cases hzero : R = 0
    · have hz0 : z = 0 := by change z^2 ≤ R at hz; rw [hzero] at hz; nlinarith [sq_nonneg z]
      exact ⟨0, 0, 0, by norm_num, by simp [hz0]⟩
    have hp : 0 < R := lt_of_le_of_ne hR (Ne.symm hzero)
    refine ⟨z*w₁/R, z*w₂/R, z*w₃/R, ?_, ?_⟩
    · have he : (z*w₁/R)^2+(z*w₂/R)^2+(z*w₃/R)^2 = z^2/R := by
        field_simp
        dsimp [R]
      rw [he]
      exact (div_le_one hp).2 hz
    · field_simp
      dsimp [R]

theorem ball3_linear_image (w₁ w₂ w₃ z : ℝ) :
    (∃ u₁ u₂ u₃ : ℝ, u₁^2+u₂^2+u₃^2 ≤ 1 ∧
      z = w₁*u₁+w₂*u₂+w₃*u₃) ↔
      |z| ≤ Real.sqrt (w₁^2+w₂^2+w₃^2) := by
  rw [ball3_linear_image_sq]
  have hn : 0 ≤ w₁^2+w₂^2+w₃^2 := by positivity
  have he := sq_le_sq₀ (abs_nonneg z) (Real.sqrt_nonneg (w₁^2+w₂^2+w₃^2))
  simpa only [sq_abs, Real.sq_sqrt hn] using he

/- 固定实部与线性泛函的整个支撑区间，不只证明上界。 -/
theorem driftMatrix_linear_image
    (s₁ s₂ s₃ l₁ l₂ l₃ z : ℝ)
    (h₁ : 0 ≤ s₁) (h₂ : 0 ≤ s₂) (h₃ : 0 ≤ s₃) :
    (∃ d₁ d₂ d₃ : ℝ, (driftMatrix s₁ s₂ s₃ d₁ d₂ d₃).PosSemidef ∧
      z = l₁*d₁+l₂*d₂+l₃*d₃) ↔
      |z| ≤ Real.sqrt (s₂*s₃*l₁^2+s₁*s₃*l₂^2+s₁*s₂*l₃^2) := by
  have hb : (∃ d₁ d₂ d₃ : ℝ,
      (driftMatrix s₁ s₂ s₃ d₁ d₂ d₃).PosSemidef ∧
      z = l₁*d₁+l₂*d₂+l₃*d₃) ↔
      (∃ u₁ u₂ u₃ : ℝ, u₁^2+u₂^2+u₃^2 ≤ 1 ∧
      z = (l₁*Real.sqrt (s₂*s₃))*u₁+(l₂*Real.sqrt (s₁*s₃))*u₂+
        (l₃*Real.sqrt (s₁*s₂))*u₃) := by
    constructor
    · rintro ⟨d₁, d₂, d₃, hd, hz⟩
      obtain ⟨u₁, u₂, u₃, hu, he₁, he₂, he₃⟩ :=
        (driftMatrix_posSemidef_iff_ball _ _ _ _ _ _ h₁ h₂ h₃).mp hd
      refine ⟨u₁, u₂, u₃, hu, ?_⟩
      rw [hz, he₁, he₂, he₃]
      ring
    · rintro ⟨u₁, u₂, u₃, hu, hz⟩
      refine ⟨Real.sqrt (s₂*s₃)*u₁, Real.sqrt (s₁*s₃)*u₂,
        Real.sqrt (s₁*s₂)*u₃, ?_, ?_⟩
      · exact (driftMatrix_posSemidef_iff_ball _ _ _ _ _ _ h₁ h₂ h₃).mpr
          ⟨u₁, u₂, u₃, hu, rfl, rfl, rfl⟩
      · rw [hz]
        ring
  rw [hb, ball3_linear_image]
  rw [mul_pow, mul_pow, mul_pow,
    Real.sq_sqrt (mul_nonneg h₂ h₃), Real.sq_sqrt (mul_nonneg h₁ h₃),
    Real.sq_sqrt (mul_nonneg h₁ h₂)]
  ring_nf

/- 换回论文的物理漂移 c=4d，保留准确的系数4。 -/
theorem physical_drift_linear_image
    (s₁ s₂ s₃ l₁ l₂ l₃ z : ℝ)
    (h₁ : 0 ≤ s₁) (h₂ : 0 ≤ s₂) (h₃ : 0 ≤ s₃) :
    (∃ d₁ d₂ d₃ : ℝ, (driftMatrix s₁ s₂ s₃ d₁ d₂ d₃).PosSemidef ∧
      z = 4*(l₁*d₁+l₂*d₂+l₃*d₃)) ↔
      |z| ≤ 4*Real.sqrt (s₂*s₃*l₁^2+s₁*s₃*l₂^2+s₁*s₂*l₃^2) := by
  have he : (∃ d₁ d₂ d₃ : ℝ,
      (driftMatrix s₁ s₂ s₃ d₁ d₂ d₃).PosSemidef ∧
      z = 4*(l₁*d₁+l₂*d₂+l₃*d₃)) ↔
      (∃ d₁ d₂ d₃ : ℝ,
      (driftMatrix s₁ s₂ s₃ d₁ d₂ d₃).PosSemidef ∧
      z/4 = l₁*d₁+l₂*d₂+l₃*d₃) := by
    constructor <;> rintro ⟨d₁, d₂, d₃, hd, hz⟩ <;>
      exact ⟨d₁, d₂, d₃, hd, by linarith⟩
  rw [he, driftMatrix_linear_image _ _ _ _ _ _ _ h₁ h₂ h₃, abs_div]
  norm_num
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
  ring_nf

/- 观测坐标变换及概率菱形。 -/
theorem observable_inverse (a b : ℝ) :
    (1+(a+b-1)+(a-b))/2 = a ∧ (1+(a+b-1)-(a-b))/2 = b := by
  constructor <;> ring

theorem stochastic_iff_diamond (a b : ℝ) :
    (0 ≤ a ∧ a ≤ 1 ∧ 0 ≤ b ∧ b ≤ 1) ↔ |a-b| ≤ 1-|a+b-1| := by
  rcases le_total 0 (a-b) with h₁ | h₁ <;>
    rcases le_total 0 (a+b-1) with h₂ | h₂
  · rw [abs_of_nonneg h₁, abs_of_nonneg h₂]
    constructor
    · rintro ⟨ha, hb, hc, hd⟩; linarith
    · intro h; exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rw [abs_of_nonneg h₁, abs_of_nonpos h₂]
    constructor
    · rintro ⟨ha, hb, hc, hd⟩; linarith
    · intro h; exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rw [abs_of_nonpos h₁, abs_of_nonneg h₂]
    constructor
    · rintro ⟨ha, hb, hc, hd⟩; linarith
    · intro h; exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rw [abs_of_nonpos h₁, abs_of_nonpos h₂]
    constructor
    · rintro ⟨ha, hb, hc, hd⟩; linarith
    · intro h; exact ⟨by linarith, by linarith, by linarith, by linarith⟩

#print axioms driftMatrix_posSemidef_iff
#print axioms driftMatrix_posSemidef_iff_ball
#print axioms posSemidef_transpose_mix
#print axioms driftMatrix_scale_posSemidef
#print axioms transpose_mix_coordinates
#print axioms ball3_linear_image
#print axioms driftMatrix_linear_image
#print axioms physical_drift_linear_image
#print axioms observable_inverse
#print axioms stochastic_iff_diamond

end TwoState.Geometry
