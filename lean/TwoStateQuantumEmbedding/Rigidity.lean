import TwoStateQuantumEmbedding.MatrixVolume
import TwoStateQuantumEmbedding.DissipativeFlow
import TwoStateQuantumEmbedding.GKSLAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! 同一半程压缩映射的二维面积与近交换耗散刚性。 -/
noncomputable section
open Matrix NormedSpace
open scoped RealInnerProductSpace Matrix Matrix.Norms.L2Operator ComplexOrder

namespace TwoStateQuantumEmbedding.Rigidity
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

/-- 半程标量几何。交叉内积的控制来自同一个压缩映射的两次作用。 -/
theorem half_geometry_scalar (s T Y m c : ℝ)
    (hs0 : 0 ≤ s) (hs : s ≤ 1 / 16)
    (hTlo : 7 / 8 ≤ T) (hT : T ≤ 1) (hY : Y ≤ T) (hYlo : 1 - 2 * s ≤ Y)
    (hminus : -(1 - Y) ≤ 2 * (m - c)) (hplus : 2 * (m - c) ≤ 1 - Y)
    (hr : (m + c) ^ 2 ≤ 2 * s) :
    3 / 4 ≤ T - m ^ 2 ∧
      (1 - 4 * s) * (T - m ^ 2) ≤ T * Y - c ^ 2 := by
  have hd0 : 0 ≤ 1 - Y := by linarith
  have hd1 : 1 - Y ≤ 1 := by linarith
  have hrlo : -(3 / 8 : ℝ) ≤ m + c := by nlinarith
  have hrhi : m + c ≤ (3 / 8 : ℝ) := by nlinarith
  have hmlo : -(1 / 4 : ℝ) ≤ m := by linarith
  have hmhi : m ≤ (1 / 4 : ℝ) := by linarith
  have hm2 : m ^ 2 ≤ 1 / 16 := by nlinarith
  have hq : 3 / 4 ≤ T - m ^ 2 := by linarith
  have hwabs : |m - c| ≤ (1 - Y) / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hmabs : |m| ≤ 1 / 4 := abs_le.mpr ⟨hmlo, hmhi⟩
  have hmw := mul_le_mul hmabs hwabs (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 4)
  rw [← abs_mul] at hmw
  have hprodlo := neg_le_abs (m * (m - c))
  have hw2 : (m - c) ^ 2 ≤ (1 - Y) / 4 := by
    have hp := mul_nonneg (sub_nonneg.mpr hplus) (sub_nonneg.mpr hminus)
    nlinarith [sq_nonneg (1 - Y)]
  have hTd := mul_le_mul_of_nonneg_right hT hd0
  have hqd := mul_le_mul_of_nonneg_right hq hd0
  have hsdelta := mul_le_mul_of_nonneg_right hYlo (by linarith : 0 ≤ T - m ^ 2)
  constructor
  · exact hq
  · nlinarith

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- 从压缩性推出半程所需标量条件；不假定任何 Gram 下界。 -/
theorem half_geometry_data (B : E →L[ℝ] E) (hB : ∀ v, ‖B v‖ ≤ ‖v‖)
    (z : E) (hz : ‖z‖ = 1) (s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 16)
    (hsread : ⟪z, B (B z)⟫ = s - 1) :
    3 / 4 ≤ ‖B z‖ ^ 2 - ⟪z, B z⟫ ^ 2 ∧
      (1 - 4 * s) * (‖B z‖ ^ 2 - ⟪z, B z⟫ ^ 2) ≤
        ‖B z‖ ^ 2 * ‖B (B z)‖ ^ 2 - ⟪B z, B (B z)⟫ ^ 2 := by
  have hx := hB z
  rw [hz] at hx
  have hy := hB (B z)
  have hy1 : ‖B (B z)‖ ≤ 1 := hy.trans hx
  have hin := abs_real_inner_le_norm z (B (B z))
  rw [hz, one_mul, hsread] at hin
  have hyn : 1 - s ≤ ‖B (B z)‖ := by
    have hh := neg_le_abs (s - 1)
    linarith
  have hYlo : 1 - 2 * s ≤ ‖B (B z)‖ ^ 2 := by
    nlinarith [norm_nonneg (B (B z)), sq_nonneg s]
  have hT : ‖B z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (B z)]
  have hY : ‖B (B z)‖ ^ 2 ≤ ‖B z‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hy
  have hTlo : 7 / 8 ≤ ‖B z‖ ^ 2 := by linarith
  have hp := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hB (z + B z))
  have hn := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hB (z - B z))
  rw [map_add, norm_add_sq_real, norm_add_sq_real, hz] at hp
  rw [map_sub, norm_sub_sq_real, norm_sub_sq_real, hz] at hn
  have hnorm : ‖B (B z) + z‖ ^ 2 ≤ 2 * s := by
    rw [norm_add_sq_real, real_inner_comm, hsread, hz]
    nlinarith [norm_nonneg (B (B z))]
  have hr := real_inner_mul_inner_self_le (B z) (B (B z) + z)
  simp only [real_inner_self_eq_norm_sq] at hr
  rw [inner_add_right, real_inner_comm z (B z)] at hr
  have hp2 := mul_le_mul hT hnorm (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  apply half_geometry_scalar s _ _ _ _ hs0 hs hTlo hT hY hYlo
  · nlinarith
  · nlinarith
  · nlinarith

/-- Gram 行列式在第二列减去第一列倍数并缩放时的精确变化。 -/
theorem area_smul_sub (a b : E) (m r : ℝ) :
    ‖a‖ ^ 2 * ‖r • (b - m • a)‖ ^ 2 - ⟪a, r • (b - m • a)⟫ ^ 2 =
      r ^ 2 * (‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫ ^ 2) := by
  simp only [← real_inner_self_eq_norm_sq, real_inner_smul_left, inner_smul_right,
    inner_sub_left, inner_sub_right, real_inner_comm b a]
  ring

/-- 明确构造第二个单位向量；量化分母正性排除了退化情况。 -/
theorem exists_orthonormal_pair_area (B : E →L[ℝ] E) (hB : ∀ v, ‖B v‖ ≤ ‖v‖)
    (z : E) (hz : ‖z‖ = 1) (s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 16)
    (hsread : ⟪z, B (B z)⟫ = s - 1) :
    ∃ e : E, ‖e‖ = 1 ∧ ⟪z, e⟫ = 0 ∧
      1 - 4 * s ≤ ‖B z‖ ^ 2 * ‖B e‖ ^ 2 - ⟪B z, B e⟫ ^ 2 := by
  obtain ⟨hq, ha⟩ := half_geometry_data B hB z hz s hs0 hs hsread
  let m := ⟪z, B z⟫
  let u := B z - m • z
  have hu : ‖u‖ ^ 2 = ‖B z‖ ^ 2 - m ^ 2 := by
    simp only [u, norm_sub_sq_real, inner_smul_right, norm_smul,
      Real.norm_eq_abs, sq_abs, hz, mul_one]
    dsimp [m]
    rw [real_inner_comm (B z) z]
    ring
  have hun : ‖u‖ ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hu
    dsimp [m] at hu
    linarith
  let e := ‖u‖⁻¹ • u
  have he : ‖e‖ = 1 := by simp [e, norm_smul, norm_inv, hun]
  have hze : ⟪z, e⟫ = 0 := by
    simp [e, u, inner_smul_right, inner_sub_right, hz, m]
  refine ⟨e, he, hze, ?_⟩
  have hb : B e = ‖u‖⁻¹ • (B (B z) - m • B z) := by simp [e, u]
  rw [hb, area_smul_sub]
  have hm := mul_le_mul_of_nonneg_left ha (sq_nonneg ‖u‖⁻¹)
  have heq : ‖u‖⁻¹ ^ 2 * ((1 - 4 * s) * (‖B z‖ ^ 2 - ⟪z, B z⟫ ^ 2)) =
      1 - 4 * s := by
    change ‖u‖⁻¹ ^ 2 * ((1 - 4 * s) * (‖B z‖ ^ 2 - m ^ 2)) = _
    rw [← hu]
    field_simp
  rwa [heq] at hm

end Hilbert

abbrev Euclid3 := EuclideanSpace ℝ (Fin 3)

/-- 两个真实欧氏向量作为 3×2 矩阵的列。 -/
def columns (u v : Euclid3) : Matrix (Fin 3) (Fin 2) ℝ := fun i j => ![u i, v i] j

theorem columns_gram (u v : Euclid3) :
    (columns u v)ᵀ * columns u v = !![‖u‖ ^ 2, ⟪u, v⟫; ⟪u, v⟫, ‖v‖ ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [columns, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply,
      EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply] <;> ring

theorem columns_mul (B : RealMatrix3) (u v : Euclid3) :
    B * columns u v = columns (Matrix.toEuclideanCLM (𝕜 := ℝ) B u)
      (Matrix.toEuclideanCLM (𝕜 := ℝ) B v) := by
  ext i j
  fin_cases j <;> rfl

/-- 同一半程实际矩阵近乎反转一个单位向量，必保留某二维单位面积。 -/
theorem exists_plane_gram_lower (B : RealMatrix3)
    (hB : ∀ v : Euclid3, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) B v‖ ≤ ‖v‖)
    (z : Euclid3) (hz : ‖z‖ = 1) (s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 16)
    (hsread : ⟪z, Matrix.toEuclideanCLM (𝕜 := ℝ) B
      (Matrix.toEuclideanCLM (𝕜 := ℝ) B z)⟫ = s - 1) :
    ∃ P : Matrix (Fin 3) (Fin 2) ℝ, Pᵀ * P = 1 ∧
      1 - 4 * s ≤ (Pᵀ * Bᵀ * B * P).det := by
  obtain ⟨e, he, hze, ha⟩ := exists_orthonormal_pair_area
    (Matrix.toEuclideanCLM (𝕜 := ℝ) B) hB z hz s hs0 hs hsread
  refine ⟨columns z e, ?_, ?_⟩
  · rw [columns_gram, hz, he, hze]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num
  · have heq : (columns z e)ᵀ * Bᵀ * B * columns z e =
        (B * columns z e)ᵀ * (B * columns z e) := by simp [Matrix.mul_assoc]
    rw [heq, columns_mul, columns_gram, Matrix.det_fin_two]
    simpa [pow_two] using ha

open DissipativeFlow

theorem canonical_trace (Ω S : RealMatrix3) (hΩ : Ωᵀ = -Ω) :
    (Ω - canonicalD S).trace = -4 * S.trace := by
  have h := congrArg Matrix.trace hΩ
  simp only [Matrix.trace_transpose, Matrix.trace_neg] at h
  have hzero : Ω.trace = 0 := by linarith
  simp only [canonicalD, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, smul_eq_mul, hzero]
  ring

theorem half_exp_square (M : RealMatrix3) :
    exp ((1 / 2 : ℝ) • M) * exp ((1 / 2 : ℝ) • M) = exp M := by
  let : NormedAlgebra ℚ RealMatrix3 := .restrictScalars ℚ ℝ _
  rw [← NormedSpace.exp_add_of_commute (Commute.refl ((1 / 2 : ℝ) • M)), ← add_smul]
  norm_num

/-- 073 的面积公式与 074 的最小伸长率在同一个半程指数处接合。 -/
theorem canonical_half_area_upper (Ω S : RealMatrix3) (hΩ : Ωᵀ = -Ω)
    (hS : S.PosSemidef) (P : Matrix (Fin 3) (Fin 2) ℝ) (hP : Pᵀ * P = 1) :
    (Pᵀ * (exp ((1 / 2 : ℝ) • (Ω - canonicalD S)))ᵀ *
      exp ((1 / 2 : ℝ) • (Ω - canonicalD S)) * P).det ≤ Real.exp (-2 * S.trace) := by
  let : NormedAlgebra ℚ RealMatrix3 := .restrictScalars ℚ ℝ _
  have hi : ‖(exp ((1 / 2 : ℝ) • (Ω - canonicalD S)))⁻¹‖ ≤ Real.exp S.trace := by
    rw [Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_exp]
    have h := matrix_inverse_norm Ω (canonicalD S) hΩ (2 * S.trace)
      (canonicalD_upper S hS) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    simpa only [neg_smul, show 2 * S.trace * (1 / 2) = S.trace by ring] using h
  have h := det_compressed_exp_gram_le ((1 / 2 : ℝ) • (Ω - canonicalD S)) P hP
  rw [Matrix.trace_smul, smul_eq_mul, canonical_trace Ω S hΩ] at h
  have hi2 := (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos S.trace).le).mpr hi
  have hup := mul_le_mul_of_nonneg_left hi2 (Real.exp_pos (2 * ((1 / 2) * (-4 * S.trace)))).le
  have heq : Real.exp (2 * ((1 / 2) * (-4 * S.trace))) * Real.exp S.trace ^ 2 =
      Real.exp (-2 * S.trace) := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  exact h.trans (by simpa only [heq] using hup)

/-- 正数 1−4s 的对数估计，保留论文的精确常数。 -/
theorem logarithmic_bound (d s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 16)
    (h : 1 - 4 * s ≤ Real.exp (-2 * d)) :
    d ≤ -Real.log (1 - 4 * s) / 2 ∧ -Real.log (1 - 4 * s) / 2 ≤ (8 / 3) * s := by
  have hx : 0 < 1 - 4 * s := by linarith
  have hl := Real.log_le_log hx h
  rw [Real.log_exp] at hl
  have hlog := Real.one_sub_inv_le_log_of_pos hx
  have heq : (1 - 4 * s)⁻¹ - 1 = 4 * s / (1 - 4 * s) := by field_simp; ring
  have hrat : 4 * s / (1 - 4 * s) ≤ (16 / 3) * s := by
    apply (div_le_iff₀ hx).mpr
    nlinarith [mul_nonneg hs0 (show 0 ≤ 1 / 16 - s by linarith)]
  constructor
  · linarith
  · linarith

/-- 实际规范 Bloch 线性生成元的近交换耗散刚性；半程平面由证明构造。 -/
theorem canonical_dissipative_rigidity (Ω S : RealMatrix3) (hΩ : Ωᵀ = -Ω)
    (hS : S.PosSemidef) (z : Euclid3) (hz : ‖z‖ = 1)
    (s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 16)
    (hread : ⟪z, Matrix.toEuclideanCLM (𝕜 := ℝ) (exp (Ω - canonicalD S)) z⟫ = s - 1) :
    S.trace ≤ -Real.log (1 - 4 * s) / 2 ∧
      -Real.log (1 - 4 * s) / 2 ≤ (8 / 3) * s := by
  let B := exp ((1 / 2 : ℝ) • (Ω - canonicalD S))
  have hB (v : Euclid3) : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) B v‖ ≤ ‖v‖ :=
    matrix_contraction Ω (canonicalD S) hΩ (canonicalD_posSemidef S hS) v (by norm_num)
  have hreadB : ⟪z, Matrix.toEuclideanCLM (𝕜 := ℝ) B
      (Matrix.toEuclideanCLM (𝕜 := ℝ) B z)⟫ = s - 1 := by
    rw [← mul_apply_eq_comp, ← map_mul]
    dsimp [B]
    rw [half_exp_square]
    exact hread
  obtain ⟨P, hP, hp⟩ := exists_plane_gram_lower B hB z hz s hs0 hs hreadB
  exact logarithmic_bound S.trace s hs0 hs (hp.trans (canonical_half_area_upper Ω S hΩ hS P hP))

open GKSLAlgebra

def zAxis : Euclid3 := WithLp.toLp 2 ![0, 0, 1]

theorem zAxis_norm : ‖zAxis‖ = 1 := by
  have h : ‖zAxis‖ ^ 2 = 1 := by simp [zAxis, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  nlinarith [norm_nonneg zAxis]

theorem zAxis_readout (A : RealMatrix3) :
    ⟪zAxis, Matrix.toEuclideanCLM (𝕜 := ℝ) A zAxis⟫ = A 2 2 := by
  rw [Matrix.inner_toEuclideanCLM]
  simp [zAxis, dotProduct, Matrix.mulVec, Fin.sum_univ_three]

theorem crossMatrix_skew (h : BlochVec) : (crossMatrix h)ᵀ = -crossMatrix h := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [crossMatrix]

theorem blochMatrix_eq_canonical (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ) :
    blochMatrix h K = crossMatrix h - canonicalD (K.map Complex.re) := by
  ext i j
  simp only [blochMatrix, canonicalD, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul]
  ring

/-- 复 PSD 的实部 PSD 由已证真实跳跃 Gram 分解推出。 -/
theorem realPart_posSemidef (K : Matrix (Fin 3) (Fin 3) ℂ) (hK : K.PosSemidef) :
    (K.map Complex.re).PosSemidef := by
  obtain ⟨l, hl⟩ := exists_kossakowski_factor K hK
  rw [← hl]
  exact kossakowski_real_posSemidef l

theorem trace_realPart (K : Matrix (Fin 3) (Fin 3) ℂ) :
    (K.map Complex.re).trace = K.trace.re := by
  simp [Matrix.trace, Fin.sum_univ_three]

/-- 真实 PSD 规范生成元的线性读出；s 非负性也由压缩性证明。 -/
theorem bloch_dissipative_rigidity (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ)
    (hK : K.PosSemidef) (s : ℝ)
    (hsread : s = 1 + (exp (blochMatrix h K)) 2 2) (hs : s ≤ 1 / 16) :
    K.trace.re ≤ -Real.log (1 - 4 * s) / 2 ∧
      -Real.log (1 - 4 * s) / 2 ≤ (8 / 3) * s := by
  have hS := realPart_posSemidef K hK
  have hΩ := crossMatrix_skew h
  have hn := matrix_contraction (crossMatrix h) (canonicalD (K.map Complex.re)) hΩ
    (canonicalD_posSemidef _ hS) zAxis (by norm_num : (0 : ℝ) ≤ 1)
  simp only [one_smul, ← blochMatrix_eq_canonical h K, zAxis_norm] at hn
  have hi := abs_real_inner_le_norm zAxis (Matrix.toEuclideanCLM (𝕜 := ℝ) (exp (blochMatrix h K)) zAxis)
  rw [zAxis_norm, one_mul, zAxis_readout] at hi
  have hs0 : 0 ≤ s := by
    have ha := neg_le_abs ((exp (blochMatrix h K)) 2 2)
    linarith
  have hr : ⟪zAxis, Matrix.toEuclideanCLM (𝕜 := ℝ)
      (exp (crossMatrix h - canonicalD (K.map Complex.re))) zAxis⟫ = s - 1 := by
    rw [← blochMatrix_eq_canonical, zAxis_readout, hsread]
    ring
  have hh := canonical_dissipative_rigidity (crossMatrix h) (K.map Complex.re)
    hΩ hS zAxis zAxis_norm s hs0 hs hr
  simpa only [trace_realPart] using hh

#print axioms exists_plane_gram_lower
#print axioms canonical_half_area_upper
#print axioms canonical_dissipative_rigidity
#print axioms bloch_dissipative_rigidity

end TwoStateQuantumEmbedding.Rigidity
