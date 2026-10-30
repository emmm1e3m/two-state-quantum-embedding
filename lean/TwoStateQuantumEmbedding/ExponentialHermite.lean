import TwoStateQuantumEmbedding.Duhamel
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Polynomial.Factorization
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

noncomputable section
set_option backward.isDefEq.respectTransparency false
open NormedSpace Polynomial Matrix Set Filter MeasureTheory
open scoped Matrix.Norms.Operator Topology Interval

namespace TwoStateQuantumEmbedding.ExponentialHermite

abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℝ

/-- 实际矩阵指数属于由该矩阵生成的有限维闭子代数。 -/
theorem exp_mem_adjoin (M : Mat3) : exp M ∈ Algebra.adjoin ℝ {M} := by
  apply NormedSpace.exp_mem (R := ℝ)
  · exact (Algebra.adjoin ℝ {M}).toSubmodule.closed_of_finiteDimensional
  · exact Algebra.subset_adjoin (by simp)

/-- Cayley–Hamilton 给实际三阶实矩阵指数的二次多项式表示。
    这里只给表示存在性；全实谱正系数必须由后续规范积分构造保证。 -/
theorem exists_exp_quadratic (M : Mat3) :
    ∃ b0 b1 b2 : ℝ, exp M = b0 • (1 : Mat3) + b1 • M + b2 • M ^ 2 := by
  have hmem := exp_mem_adjoin M
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
  obtain ⟨p, hp⟩ := hmem
  let q := p %ₘ M.charpoly
  have hchar : M.charpoly.natDegree = 3 := by simp
  have hchar_ne : M.charpoly ≠ 1 := by
    intro h
    rw [h] at hchar
    simp at hchar
  have hdeg : q.natDegree < 3 := by
    simpa only [q, hchar] using natDegree_modByMonic_lt p M.charpoly_monic hchar_ne
  have hq : aeval M q = exp M := by
    rw [← Matrix.aeval_eq_aeval_mod_charpoly]
    exact hp
  refine ⟨q.coeff 0, q.coeff 1, q.coeff 2, ?_⟩
  rw [← hq, aeval_eq_sum_range' hdeg]
  simp [Finset.sum_range_succ, Algebra.smul_def]

/-- 一阶 Newton 差商的无奇点时间积分。 -/
def newtonFirst (a b t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, Real.exp ((t - s) * a + s * b)

/-- 二阶差商采用有序单纯形积分，重根时无需除法或取极限。 -/
def newtonSecond (a b c : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, Real.exp ((1 - s) * a) * newtonFirst b c s

theorem newtonFirst_factor (a b t : ℝ) :
    newtonFirst a b t = Real.exp (t * a) *
      ∫ s in (0 : ℝ)..t, Real.exp (s * (b - a)) := by
  unfold newtonFirst
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [← Real.exp_add]
  congr 1
  ring

theorem continuous_newtonFirst (a b : ℝ) : Continuous (newtonFirst a b) := by
  have hc : Continuous (fun s : ℝ => Real.exp (s * (b - a))) := by fun_prop
  have hp := intervalIntegral.continuous_primitive (μ := volume)
    (fun x y => hc.intervalIntegrable x y) 0
  have hf : newtonFirst a b = fun t => Real.exp (t * a) *
      ∫ s in (0 : ℝ)..t, Real.exp (s * (b - a)) := by
    funext t
    exact newtonFirst_factor a b t
  rw [hf]
  exact (by fun_prop : Continuous (fun t : ℝ => Real.exp (t * a))).mul hp

theorem newtonFirst_nonneg (a b : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ newtonFirst a b t := by
  exact intervalIntegral.integral_nonneg_of_forall ht (fun _ => (Real.exp_pos _).le)

theorem newtonFirst_pos (a b : ℝ) {t : ℝ} (ht : 0 < t) :
    0 < newtonFirst a b t := by
  apply intervalIntegral.integral_pos ht
  · exact (by fun_prop : Continuous (fun s : ℝ => Real.exp ((t - s) * a + s * b))).continuousOn
  · intro s _
    exact (Real.exp_pos _).le
  · exact ⟨0, ⟨le_rfl, ht.le⟩, Real.exp_pos _⟩

theorem newtonSecond_pos (a b c : ℝ) : 0 < newtonSecond a b c := by
  apply intervalIntegral.integral_pos (by norm_num : (0 : ℝ) < 1)
  · exact ((by fun_prop : Continuous (fun s : ℝ => Real.exp ((1 - s) * a))).mul
      (continuous_newtonFirst b c)).continuousOn
  · intro s hs
    exact mul_nonneg (Real.exp_pos _).le (newtonFirst_nonneg b c hs.1.le)
  · exact ⟨1, by simp, mul_pos (Real.exp_pos _) (newtonFirst_pos b c (by norm_num))⟩

theorem newtonSecond_eq_triangle (a b c : ℝ) :
    newtonSecond a b c =
      ∫ s in (0 : ℝ)..1, ∫ r in (0 : ℝ)..s,
        Real.exp ((1 - s) * a + (s - r) * b + r * c) := by
  unfold newtonSecond newtonFirst
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro r _
  dsimp only
  rw [← Real.exp_add]
  congr 1
  ring

section NewtonBanach
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

omit [CompleteSpace A] in
theorem exp_scalar (a : ℝ) : exp (a • (1 : A)) = Real.exp a • (1 : A) := by
  simpa only [Algebra.algebraMap_eq_smul_one, ← Real.exp_eq_exp_ℝ] using
    (NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := A) a).symm

/-- 真实指数继承右特征关系；由指数级数的半共轭定理推出。 -/
theorem factor_exp_reduction (M P : A) (c t : ℝ)
    (hzero : P * (M - c • (1 : A)) = 0) :
    P * exp (t • M) = Real.exp (t * c) • P := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have hPM : P * M = c • P := by
    rw [mul_sub, mul_smul_comm, mul_one, sub_eq_zero] at hzero
    exact hzero
  have hs : SemiconjBy P (t • M) ((t * c) • (1 : A)) := by
    change P * (t • M) = ((t * c) • (1 : A)) * P
    simp only [mul_smul_comm, smul_mul_assoc, one_mul, hPM, smul_smul]
  have he := hs.exp_right
  change P * exp (t • M) = exp ((t * c) • (1 : A)) * P at he
  simpa only [exp_scalar, smul_mul_assoc, one_mul] using he

/-- 以标量矩阵为基点的精确 Duhamel 展开。 -/
theorem scalar_duhamel (M : A) (a t : ℝ) :
    exp (t • M) = Real.exp (t * a) • (1 : A) +
      ∫ s in (0 : ℝ)..t, Real.exp ((t - s) * a) •
        ((M - a • (1 : A)) * exp (s • M)) := by
  have h := exp_add_sub_exp_eq_integral_right (a • (1 : A)) (M - a • (1 : A)) t
  rw [show a • (1 : A) + (M - a • (1 : A)) = M by abel] at h
  simp only [smul_smul, exp_scalar, smul_mul_assoc, one_mul] at h
  simpa only [add_comm] using eq_add_of_sub_eq h

/-- 左乘多项式因子后的 Duhamel 展开，保留所有乘法次序。 -/
theorem scalar_duhamel_left (M P : A) (a t : ℝ) :
    P * exp (t • M) = Real.exp (t * a) • P +
      ∫ s in (0 : ℝ)..t, Real.exp ((t - s) * a) •
        ((P * (M - a • (1 : A))) * exp (s • M)) := by
  have hc : Continuous (fun s : ℝ => Real.exp ((t - s) * a) •
      ((M - a • (1 : A)) * exp (s • M))) := by
    apply Continuous.smul (by fun_prop)
    exact continuous_const.mul (differentiable_exp_smul_const ℝ M).continuous
  have hi := (ContinuousLinearMap.mul ℝ A P).intervalIntegral_comp_comm
    (μ := volume) (hc.intervalIntegrable 0 t)
  have h := congrArg (fun Q : A => P * Q) (scalar_duhamel M a t)
  simp only [mul_add, mul_smul_comm, mul_one] at h
  simp only [ContinuousLinearMap.mul_apply'] at hi
  rw [← hi] at h
  simpa only [ContinuousLinearMap.mul_apply', mul_smul_comm, mul_assoc] using h

/-- 两个 Newton 因子的余项被第三因子湮灭时，第二步展开精确终止。 -/
theorem scalar_duhamel_left_terminated (M P : A) (b c t : ℝ)
    (hzero : (P * (M - b • (1 : A))) * (M - c • (1 : A)) = 0) :
    P * exp (t • M) = Real.exp (t * b) • P +
      newtonFirst b c t • (P * (M - b • (1 : A))) := by
  rw [scalar_duhamel_left M P b t]
  congr 1
  have hk : (fun s : ℝ => Real.exp ((t - s) * b) •
      ((P * (M - b • (1 : A))) * exp (s • M))) =
      (fun s : ℝ => Real.exp ((t - s) * b + s * c) •
        (P * (M - b • (1 : A)))) := by
    funext s
    rw [factor_exp_reduction M _ c s hzero, smul_smul, ← Real.exp_add]
  rw [hk, intervalIntegral.integral_smul_const]
  rfl

/-- 三个实线性因子湮灭 M 时，实际指数等于无奇点 Newton 二次式。 -/
theorem exp_newton_of_cubic_annihilator (M : A) (a b c : ℝ)
    (hzero : ((M - a • (1 : A)) * (M - b • (1 : A))) *
      (M - c • (1 : A)) = 0) :
    exp M = Real.exp a • (1 : A) +
      newtonFirst a b 1 • (M - a • (1 : A)) +
      newtonSecond a b c • ((M - a • (1 : A)) * (M - b • (1 : A))) := by
  have h := scalar_duhamel M a 1
  simp only [one_smul, one_mul] at h
  rw [h]
  have hk : (fun s : ℝ => Real.exp ((1 - s) * a) •
      ((M - a • (1 : A)) * exp (s • M))) =
      (fun s : ℝ =>
        Real.exp ((1 - s) * a + s * b) • (M - a • (1 : A)) +
        (Real.exp ((1 - s) * a) * newtonFirst b c s) •
          ((M - a • (1 : A)) * (M - b • (1 : A)))) := by
    funext s
    rw [scalar_duhamel_left_terminated M (M - a • (1 : A)) b c s hzero,
      smul_add, smul_smul, smul_smul, ← Real.exp_add]
  rw [hk, intervalIntegral.integral_add]
  · simp only [intervalIntegral.integral_smul_const]
    simp only [newtonFirst, newtonSecond, add_assoc]
  · exact ((by fun_prop : Continuous (fun s : ℝ => Real.exp ((1 - s) * a + s * b))).smul
      continuous_const).intervalIntegrable 0 1
  · exact (((by fun_prop : Continuous (fun s : ℝ => Real.exp ((1 - s) * a))).mul
      (continuous_newtonFirst b c)).smul continuous_const).intervalIntegrable 0 1

end NewtonBanach

/-- 全实谱分支的规范表示：二阶系数是严格正的单纯形积分，允许任意重根。 -/
theorem exp_quadratic_of_real_charpoly (M : Mat3) (a b c : ℝ)
    (hpoly : M.charpoly = (X - C a) * (X - C b) * (X - C c)) :
    exp M = (Real.exp a - a * newtonFirst a b 1 + a * b * newtonSecond a b c) •
        (1 : Mat3) +
      (newtonFirst a b 1 - (a + b) * newtonSecond a b c) • M +
      newtonSecond a b c • M ^ 2 := by
  have hz := M.aeval_self_charpoly
  rw [hpoly] at hz
  simp only [map_mul, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at hz
  rw [exp_newton_of_cubic_annihilator M a b c hz]
  simp only [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    smul_sub, smul_smul, sub_smul, add_smul, pow_two]
  module

/-- 三阶实矩阵的全谱分支。实根允许相等；非实分支的频率只有正性约束。 -/
theorem real_cubic_spectral_cases (M : Mat3) :
    (∃ a b c : ℝ, M.charpoly = (X - C a) * (X - C b) * (X - C c)) ∨
    (∃ u v w : ℝ, 0 < w ∧ M.charpoly =
      (X + C u) * (X ^ 2 + C (2 * v) * X + C (v ^ 2 + w ^ 2))) := by
  have hm : IsMonicOfDegree M.charpoly (1 + 2) := ⟨by simp, M.charpoly_monic⟩
  obtain ⟨q, l, hq, hl, hp⟩ := hm.eq_isMonicOfDegree_two_mul_isMonicOfDegree
  obtain ⟨A, B, rfl⟩ := isMonicOfDegree_two_iff.mp hq
  obtain ⟨R, rfl⟩ := isMonicOfDegree_one_iff.mp hl
  by_cases hΔ : 0 ≤ A ^ 2 / 4 - B
  · left
    let δ := Real.sqrt (A ^ 2 / 4 - B)
    have hδ : δ ^ 2 = A ^ 2 / 4 - B := Real.sq_sqrt hΔ
    refine ⟨-R, -A / 2 + δ, -A / 2 - δ, ?_⟩
    rw [hp]
    have hsum : (-A / 2 + δ) + (-A / 2 - δ) = -A := by ring
    have hprod : (-A / 2 + δ) * (-A / 2 - δ) = B := by nlinarith [hδ]
    calc
      _ = (X - C (-R)) * (X ^ 2 - C ((-A / 2 + δ) + (-A / 2 - δ)) * X +
          C ((-A / 2 + δ) * (-A / 2 - δ))) := by rw [hsum, hprod]; simp; ring
      _ = _ := by simp only [map_add, map_mul]; ring
  · right
    have hΔ' : 0 < B - A ^ 2 / 4 := by linarith
    let w := Real.sqrt (B - A ^ 2 / 4)
    have hw : w ^ 2 = B - A ^ 2 / 4 := Real.sq_sqrt hΔ'.le
    refine ⟨R, A / 2, w, Real.sqrt_pos.mpr hΔ', ?_⟩
    rw [hp]
    have hb : (A / 2) ^ 2 + w ^ 2 = B := by nlinarith [hw]
    rw [hb, show 2 * (A / 2) = A by ring, mul_comm]

abbrev CMat3 := Matrix (Fin 3) (Fin 3) ℂ

/-- 实矩阵嵌入复矩阵的实际指数与嵌入交换。 -/
theorem complexify_exp (M : Mat3) :
    (exp M).map Complex.ofReal = exp (M.map Complex.ofReal) := by
  have hc : Continuous (Complex.ofRealHom.mapMatrix : Mat3 → CMat3) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact Complex.continuous_ofReal.comp ((continuous_apply j).comp (continuous_apply i))
  exact NormedSpace.map_exp Complex.ofRealHom.mapMatrix hc M

/-- 复标量矩阵的指数。 -/
theorem exp_complex_scalar (z : ℂ) :
    exp (z • (1 : CMat3)) = Complex.exp z • (1 : CMat3) := by
  simpa only [Algebra.algebraMap_eq_smul_one, ← Complex.exp_eq_exp_ℂ] using
    (NormedSpace.algebraMap_exp_comm (𝕂 := ℂ) (𝔸 := CMat3) z).symm

/-- 特征多项式的真实根在实际指数二次表示上满足标量指数恒等式。
    证明取非零核向量并将其复制为矩阵，指数半共轭不需要 Jordan 分解。 -/
theorem exp_quadratic_at_root (M : CMat3) (z b0 b1 b2 : ℂ)
    (hroot : M.charpoly.eval z = 0)
    (hpoly : exp M = b0 • (1 : CMat3) + b1 • M + b2 • M ^ 2) :
    Complex.exp z = b0 + b1 * z + b2 * z ^ 2 := by
  rw [Matrix.eval_charpoly] at hroot
  obtain ⟨v, hv, he⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hroot
  have hMv : M *ᵥ v = z • v := by
    simp only [Matrix.sub_mulVec, Matrix.scalar_apply, Matrix.diagonal_const_mulVec,
      sub_eq_zero] at he
    exact he.symm
  let P : CMat3 := fun i _ => v i
  have hMP : M * P = z • P := by
    ext i j
    change (M *ᵥ v) i = z * v i
    rw [hMv]
    rfl
  have hM2P : M ^ 2 * P = z ^ 2 • P := by
    rw [pow_two, mul_assoc, hMP, mul_smul_comm, hMP, smul_smul, pow_two]
  have hs : SemiconjBy P (z • (1 : CMat3)) M := by
    change P * (z • (1 : CMat3)) = M * P
    rw [mul_smul_comm, mul_one, hMP]
  have hexp := hs.exp_right
  change P * exp (z • (1 : CMat3)) = exp M * P at hexp
  rw [exp_complex_scalar, mul_smul_comm, mul_one, hpoly] at hexp
  simp only [add_mul, smul_mul_assoc, one_mul, hMP, hM2P, smul_smul] at hexp
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra! hn
    apply hv
    funext i
    exact hn i
  have h := congrArg (fun Q : CMat3 => Q i 0) hexp
  change Complex.exp z * v i = (b0 * v i + (b1 * z) * v i) + (b2 * z ^ 2) * v i at h
  exact (mul_right_cancel₀ hi) (by linear_combination h)

theorem complexify_smul (a : ℝ) (M : Mat3) :
    (a • M).map Complex.ofReal = (a : ℂ) • M.map Complex.ofReal := by
  ext i j
  simp

/-- 实矩阵二次表示在任意复特征根处的真实标量函数演算。 -/
theorem real_exp_quadratic_at_root (M : Mat3) (z : ℂ) (b0 b1 b2 : ℝ)
    (hroot : (M.charpoly.map Complex.ofRealHom).eval z = 0)
    (hpoly : exp M = b0 • (1 : Mat3) + b1 • M + b2 • M ^ 2) :
    Complex.exp z = (b0 : ℂ) + (b1 : ℂ) * z + (b2 : ℂ) * z ^ 2 := by
  apply exp_quadratic_at_root (M.map Complex.ofReal) z b0 b1 b2
  · change (M.map Complex.ofRealHom).charpoly.eval z = 0
    rwa [Matrix.charpoly_map]
  · have h := congrArg (Complex.ofRealHom.mapMatrix : Mat3 → CMat3) hpoly
    have hs (a : ℝ) (N : Mat3) : Complex.ofRealHom.mapMatrix (a • N) =
        (a : ℂ) • Complex.ofRealHom.mapMatrix N := complexify_smul a N
    have he : Complex.ofRealHom.mapMatrix (exp M) =
        exp (Complex.ofRealHom.mapMatrix M) := complexify_exp M
    have hf : (Complex.ofRealHom : ℝ → ℂ) = Complex.ofReal := rfl
    simpa only [map_add, hs, map_pow, map_one, he, RingHom.mapMatrix_apply,
      hf] using h

/-- 非实共轭对分支的全部实部、虚部等式，从真实 exp M 推出。
    w 取任意实数；使用完整谱分支时 w > 0，不截断频率。 -/
theorem nonreal_spectral_values (M : Mat3) (u v w b0 b1 b2 : ℝ)
    (hchar : M.charpoly =
      (X + C u) * (X ^ 2 + C (2 * v) * X + C (v ^ 2 + w ^ 2)))
    (hpoly : exp M = b0 • (1 : Mat3) + b1 • M + b2 • M ^ 2) :
    Real.exp (-u) = b0 - b1 * u + b2 * u ^ 2 ∧
    Real.exp (-v) * Real.cos w = b0 - b1 * v + b2 * (v ^ 2 - w ^ 2) ∧
    Real.exp (-v) * Real.sin w = b1 * w - 2 * b2 * v * w := by
  have hr : (M.charpoly.map Complex.ofRealHom).eval (-(u : ℂ)) = 0 := by
    simp [hchar]
  have hc : (M.charpoly.map Complex.ofRealHom).eval
      (-(v : ℂ) + (w : ℂ) * Complex.I) = 0 := by
    simp only [hchar, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Complex.ofRealHom_eq_coe,
      Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_ofNat]
    ring_nf
    simp [Complex.I_sq]
  have her := congrArg Complex.re (real_exp_quadratic_at_root M _ b0 b1 b2 hr hpoly)
  have he := real_exp_quadratic_at_root M _ b0 b1 b2 hc hpoly
  have hec := congrArg Complex.re he
  have hes := congrArg Complex.im he
  simp [Complex.exp_re, Complex.exp_im, pow_two, Complex.mul_re, Complex.mul_im] at her hec hes
  exact ⟨by nlinarith [her], by nlinarith [hec], by nlinarith [hes]⟩

/-- 复共轭谱分解中的衰减参数和等于负迹。 -/
theorem trace_of_nonreal_charpoly (M : Mat3) (u v w : ℝ)
    (hchar : M.charpoly =
      (X + C u) * (X ^ 2 + C (2 * v) * X + C (v ^ 2 + w ^ 2))) :
    M.trace = -(u + 2 * v) := by
  rw [Matrix.trace_eq_neg_charpoly_coeff, hchar]
  have he : (X + C u) * (X ^ 2 + C (2 * v) * X + C (v ^ 2 + w ^ 2)) =
      (X : ℝ[X]) ^ 3 + C (u + 2 * v) * X ^ 2 +
        C (v ^ 2 + w ^ 2 + 2 * u * v) * X + C (u * (v ^ 2 + w ^ 2)) := by
    simp only [map_add, map_mul, map_pow]
    ring
  rw [he]
  norm_num only [Fintype.card_fin, Nat.reduceSub, Polynomial.coeff_add,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X,
    Polynomial.coeff_C, ite_true, ite_false, mul_one, mul_zero, add_zero, zero_add]

/-- 对 C6 的统一表示接口：实谱选取正二阶系数，复谱保留真实标量指数关系。 -/
theorem exists_exp_quadratic_spectral (M : Mat3) :
    ∃ b0 b1 b2 : ℝ,
      exp M = b0 • (1 : Mat3) + b1 • M + b2 • M ^ 2 ∧
      (0 < b2 ∨ ∃ u v w : ℝ, 0 < w ∧
        M.charpoly = (X + C u) * (X ^ 2 + C (2 * v) * X + C (v ^ 2 + w ^ 2)) ∧
        Real.exp (-u) = b0 - b1 * u + b2 * u ^ 2 ∧
        Real.exp (-v) * Real.cos w = b0 - b1 * v + b2 * (v ^ 2 - w ^ 2) ∧
        Real.exp (-v) * Real.sin w = b1 * w - 2 * b2 * v * w) := by
  rcases real_cubic_spectral_cases M with ⟨a, b, c, hc⟩ | ⟨u, v, w, hw, hc⟩
  · exact ⟨_, _, _, exp_quadratic_of_real_charpoly M a b c hc,
      Or.inl (newtonSecond_pos a b c)⟩
  · obtain ⟨b0, b1, b2, hp⟩ := exists_exp_quadratic M
    exact ⟨b0, b1, b2, hp, Or.inr ⟨u, v, w, hw, hc,
      nonreal_spectral_values M u v w b0 b1 b2 hc hp⟩⟩

/-- 从实际谱值推出论文的正弦、相位及模平方恒等式。
    唯一额外输入是 C4/KKT 所得的仿射系数条件和矩阵迹。 -/
theorem affine_exp_spectral_relations (M : Mat3) (L u v w b1 : ℝ)
    (hb1 : 0 < b1)
    (hchar : M.charpoly =
      (X + C u) * (X ^ 2 + C (2 * v) * X + C (v ^ 2 + w ^ 2)))
    (htrace : M.trace = -2 * L)
    (hpoly : exp M = ((L - 1 / 2) * b1) • (1 : Mat3) + b1 • M)
    (hw : 0 < w) :
    1 / 2 < L - u ∧
    Real.sin w / w = Real.exp ((L - u) - u / 2) / ((L - u) - 1 / 2) ∧
    w * Real.cos w = (u - 1) / 2 * Real.sin w ∧
    (u - 1) ^ 2 / 4 + w ^ 2 =
      ((L - u) - 1 / 2) ^ 2 * Real.exp (u - 2 * (L - u)) := by
  have ht : u + 2 * v = 2 * L := by
    linarith [trace_of_nonreal_charpoly M u v w hchar]
  have hp : exp M = ((L - 1 / 2) * b1) • (1 : Mat3) + b1 • M + (0 : ℝ) • M ^ 2 := by
    simpa using hpoly
  obtain ⟨hr', hc', hs⟩ := nonreal_spectral_values M u v w _ b1 0 hchar hp
  simp only [mul_zero, zero_mul, sub_zero, add_zero] at hr' hc' hs
  have hr : Real.exp (-u) = b1 * ((L - u) - 1 / 2) := by nlinarith [hr']
  have hc : Real.exp (-v) * Real.cos w = b1 * ((u - 1) / 2) := by
    nlinarith [hc']
  have hT : 0 < (L - u) - 1 / 2 := by
    by_contra! hn
    have := mul_nonpos_of_nonneg_of_nonpos hb1.le hn
    rw [← hr] at this
    exact (Real.exp_pos (-u)).not_ge this
  refine ⟨by linarith, ?_, ?_, ?_⟩
  · apply (div_eq_div_iff (ne_of_gt hw) (ne_of_gt hT)).mpr
    have he : Real.exp (-v) * Real.exp ((L - u) - u / 2) = Real.exp (-u) := by
      rw [← Real.exp_add]
      congr 1
      linarith
    apply mul_left_cancel₀ (Real.exp_ne_zero (-v))
    calc
      Real.exp (-v) * (Real.sin w * ((L - u) - 1 / 2)) =
          (b1 * ((L - u) - 1 / 2)) * w := by rw [← mul_assoc, hs]; ring
      _ = Real.exp (-u) * w := by rw [hr]
      _ = Real.exp (-v) * (Real.exp ((L - u) - u / 2) * w) := by rw [← he]; ring
  · apply mul_left_cancel₀ (Real.exp_ne_zero (-v))
    linear_combination w * hc - ((u - 1) / 2) * hs
  · have he : Real.exp (-u) ^ 2 * Real.exp (u - 2 * (L - u)) =
        Real.exp (-v) ^ 2 := by
      simp only [pow_two]
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      linarith
    have hnorm : b1 ^ 2 * ((u - 1) ^ 2 / 4 + w ^ 2) = Real.exp (-v) ^ 2 := by
      calc
        _ = (b1 * ((u - 1) / 2)) ^ 2 + (b1 * w) ^ 2 := by ring
        _ = (Real.exp (-v) * Real.cos w) ^ 2 + (Real.exp (-v) * Real.sin w) ^ 2 := by
          rw [hc, hs]
        _ = Real.exp (-v) ^ 2 * (Real.cos w ^ 2 + Real.sin w ^ 2) := by ring
        _ = _ := by rw [Real.cos_sq_add_sin_sq, mul_one]
    apply mul_left_cancel₀ (pow_ne_zero 2 (ne_of_gt hb1))
    calc
      _ = Real.exp (-v) ^ 2 := hnorm
      _ = Real.exp (-u) ^ 2 * Real.exp (u - 2 * (L - u)) := he.symm
      _ = _ := by rw [hr]; ring

/-- C6 的即用接口。把 C4 对任意指数表示的系数消元作为输入，
    由实际指数自动选出非实谱，且产生 060 谱矛盾所需的解析三式。 -/
theorem spectral_relations_of_coefficient_constraints (M : Mat3) (L : ℝ)
    (htrace : M.trace = -2 * L)
    (hcoeff : ∀ b0 b1 b2 : ℝ,
      exp M = b0 • (1 : Mat3) + b1 • M + b2 • M ^ 2 →
        b2 = 0 ∧ b0 = (L - 1 / 2) * b1 ∧ 0 < b1) :
    ∃ u v w : ℝ, 0 < w ∧
      M.charpoly = (X + C u) * (X ^ 2 + C (2 * v) * X + C (v ^ 2 + w ^ 2)) ∧
      u + 2 * v = 2 * L ∧
      1 / 2 < L - u ∧
      Real.sin w / w = Real.exp ((L - u) - u / 2) / ((L - u) - 1 / 2) ∧
      w * Real.cos w = (u - 1) / 2 * Real.sin w ∧
      (u - 1) ^ 2 / 4 + w ^ 2 =
        ((L - u) - 1 / 2) ^ 2 * Real.exp (u - 2 * (L - u)) := by
  obtain ⟨b0, b1, b2, hp, hs⟩ := exists_exp_quadratic_spectral M
  obtain ⟨hb2, hb0, hb1⟩ := hcoeff b0 b1 b2 hp
  rcases hs with hpos | ⟨u, v, w, hw, hc, _⟩
  · simp [hb2] at hpos
  · refine ⟨u, v, w, hw, hc, ?_, ?_⟩
    · linarith [trace_of_nonreal_charpoly M u v w hc]
    · apply affine_exp_spectral_relations M L u v w b1 hb1 hc htrace _ hw
      simpa [hb2, hb0] using hp

end TwoStateQuantumEmbedding.ExponentialHermite

#print axioms TwoStateQuantumEmbedding.ExponentialHermite.exists_exp_quadratic
#print axioms TwoStateQuantumEmbedding.ExponentialHermite.newtonSecond_pos
#print axioms TwoStateQuantumEmbedding.ExponentialHermite.newtonSecond_eq_triangle
#print axioms TwoStateQuantumEmbedding.ExponentialHermite.exp_quadratic_of_real_charpoly
#print axioms TwoStateQuantumEmbedding.ExponentialHermite.real_cubic_spectral_cases
#print axioms TwoStateQuantumEmbedding.ExponentialHermite.exp_quadratic_at_root
#print axioms TwoStateQuantumEmbedding.ExponentialHermite.exists_exp_quadratic_spectral
#print axioms TwoStateQuantumEmbedding.ExponentialHermite.affine_exp_spectral_relations
#print axioms TwoStateQuantumEmbedding.ExponentialHermite.spectral_relations_of_coefficient_constraints
