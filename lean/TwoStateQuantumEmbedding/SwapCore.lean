import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.Order
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-! 交换端点的精确复二次型；所有常数使用真正的 π 与 √2。 -/
namespace Swap
open Complex Matrix
open scoped ComplexOrder
noncomputable section

noncomputable def rootTwo : ℝ := Real.sqrt 2
noncomputable def slope : ℝ := (Real.pi - 2 * rootTwo) / (Real.pi + 2 * rootTwo)
noncomputable def gap : ℝ := 1 - slope
noncomputable def frequency (j : ℕ) : ℝ := (2 * (j : ℝ) + 1) * Real.pi

theorem rootTwo_pos : 0 < rootTwo := by unfold rootTwo; positivity
theorem rootTwo_sq : rootTwo ^ 2 = 2 := by exact Real.sq_sqrt (by norm_num)
theorem twice_rootTwo_lt_pi : 2 * rootTwo < Real.pi := by
  have h := Real.sqrt_two_lt_three_halves
  have hp := Real.pi_gt_three
  unfold rootTwo
  linarith

theorem slope_pos : 0 < slope := by
  unfold slope
  exact div_pos (sub_pos.mpr twice_rootTwo_lt_pi) (by linarith [rootTwo_pos, Real.pi_pos])
theorem slope_lt_one : slope < 1 := by
  unfold slope
  apply (div_lt_one (by linarith [rootTwo_pos, Real.pi_pos] : 0 < Real.pi + 2 * rootTwo)).2
  linarith [rootTwo_pos]
theorem gap_pos : 0 < gap := sub_pos.mpr slope_lt_one

theorem coupling_identity : (1 + slope) * (4 / Real.pi) = gap * rootTwo := by
  have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hd : Real.pi + 2 * rootTwo ≠ 0 := ne_of_gt (by linarith [rootTwo_pos, Real.pi_pos])
  unfold gap slope
  field_simp
  ring_nf
  rw [rootTwo_sq]
  ring

theorem frequency_pos (j : ℕ) : 0 < frequency j := by unfold frequency; positivity

theorem frequency_zero : frequency 0 = Real.pi := by simp [frequency]

def energy (v : Fin 3 → ℂ) : ℝ :=
  normSq (v 0) + (normSq (v 1) + normSq (v 2)) / 2

def cross (v : Fin 3 → ℂ) : ℝ := ((starRingEnd ℂ) (v 0) * v 2).im

def mass (v : Fin 3 → ℂ) : ℝ := normSq (v 0) + normSq (v 1) + normSq (v 2)

noncomputable def qa (j : ℕ) (v : Fin 3 → ℂ) : ℝ :=
  energy v - (4 / frequency j) * cross v
noncomputable def qb (j : ℕ) (v : Fin 3 → ℂ) : ℝ :=
  energy v + (4 / frequency j) * cross v

noncomputable def squareMinus (v : Fin 3 → ℂ) : ℝ :=
  normSq (v 0 + ((rootTwo / 2 : ℝ) : ℂ) * I * v 2) + normSq (v 1) / 2
noncomputable def squarePlus (v : Fin 3 → ℂ) : ℝ :=
  normSq (v 0 - ((rootTwo / 2 : ℝ) : ℂ) * I * v 2) + normSq (v 1) / 2

theorem squareMinus_identity (v : Fin 3 → ℂ) :
    squareMinus v = energy v - rootTwo * cross v := by
  simp only [squareMinus, energy, cross, normSq_apply, add_re, add_im,
    mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, conj_re, conj_im]
  ring_nf
  rw [rootTwo_sq]
  ring

theorem squarePlus_identity (v : Fin 3 → ℂ) :
    squarePlus v = energy v + rootTwo * cross v := by
  simp only [squarePlus, energy, cross, normSq_apply, sub_re, sub_im,
    mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, conj_re, conj_im]
  ring_nf
  rw [rootTwo_sq]
  ring

theorem squareMinus_nonneg (v : Fin 3 → ℂ) : 0 ≤ squareMinus v := by
  unfold squareMinus
  exact add_nonneg (normSq_nonneg _) (div_nonneg (normSq_nonneg _) (by norm_num))

theorem squarePlus_nonneg (v : Fin 3 → ℂ) : 0 ≤ squarePlus v := by
  unfold squarePlus
  exact add_nonneg (normSq_nonneg _) (div_nonneg (normSq_nonneg _) (by norm_num))

theorem energy_nonneg (v : Fin 3 → ℂ) : 0 ≤ energy v := by
  unfold energy
  linarith [normSq_nonneg (v 0), normSq_nonneg (v 1), normSq_nonneg (v 2)]

theorem mass_nonneg (v : Fin 3 → ℂ) : 0 ≤ mass v := by
  unfold mass
  linarith [normSq_nonneg (v 0), normSq_nonneg (v 1), normSq_nonneg (v 2)]

theorem energy_ge_half_mass (v : Fin 3 → ℂ) : mass v / 2 ≤ energy v := by
  unfold mass energy
  linarith [normSq_nonneg (v 0)]

/-- 首交换的完整复二次型恒等式；它同时覆盖四个非平面实方向。 -/
theorem first_swap_square (v : Fin 3 → ℂ) :
    qa 0 v - slope * qb 0 v = gap * squareMinus v := by
  rw [squareMinus_identity]
  unfold qa qb
  rw [frequency_zero]
  calc
    _ = (1 - slope) * energy v - ((1 + slope) * (4 / Real.pi)) * cross v := by ring
    _ = gap * (energy v - rootTwo * cross v) := by rw [coupling_identity]; unfold gap; ring

theorem first_swap_sharp (v : Fin 3 → ℂ) : slope * qb 0 v ≤ qa 0 v := by
  have h := mul_nonneg (le_of_lt gap_pos) (squareMinus_nonneg v)
  rw [← first_swap_square] at h
  linarith

noncomputable def weight (j : ℕ) : ℝ := 1 / (2 * (j : ℝ) + 1)

theorem weight_pos (j : ℕ) : 0 < weight j := by unfold weight; positivity

theorem weight_le_one (j : ℕ) : weight j ≤ 1 := by
  unfold weight
  apply (div_le_one (by positivity : (0:ℝ) < 2 * (j:ℝ) + 1)).2
  have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j
  linarith

theorem weight_le_third {j : ℕ} (hj : 1 ≤ j) : weight j ≤ 1 / 3 := by
  have hj' : (1:ℝ) ≤ j := by exact_mod_cast hj
  unfold weight
  apply (div_le_div_iff₀ (by positivity : (0:ℝ) < 2 * (j:ℝ) + 1) (by norm_num : (0:ℝ) < 3)).2
  linarith

/-- 全频率形式均为两个非负平方形式的精确组合。 -/
theorem all_frequency_decomposition (j : ℕ) (v : Fin 3 → ℂ) :
    qa j v - slope * qb j v =
      gap * ((1 - weight j) * energy v + weight j * squareMinus v) := by
  rw [squareMinus_identity]
  have hn : (2 * (j:ℝ) + 1) ≠ 0 := ne_of_gt (by positivity)
  have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hw : (4 / frequency j) = (4 / Real.pi) * weight j := by
    unfold frequency weight
    field_simp
  unfold qa qb
  rw [hw]
  calc
    _ = (1 - slope) * energy v - ((1 + slope) * (4 / Real.pi)) * weight j * cross v := by ring
    _ = _ := by rw [coupling_identity]; unfold gap; ring

theorem all_frequency_sharp (j : ℕ) (v : Fin 3 → ℂ) :
    slope * qb j v ≤ qa j v := by
  have h := mul_nonneg (le_of_lt gap_pos)
    (add_nonneg (mul_nonneg (sub_nonneg.mpr (weight_le_one j)) (energy_nonneg v))
      (mul_nonneg (le_of_lt (weight_pos j)) (squareMinus_nonneg v)))
  rw [← all_frequency_decomposition] at h
  linarith

/-- 除首半圈以外，双对偶形式有统一的严格正谱隙。 -/
theorem higher_frequency_gap {j : ℕ} (hj : 1 ≤ j) (v : Fin 3 → ℂ) :
    (gap / 3) * mass v ≤ qa j v - slope * qb j v := by
  rw [all_frequency_decomposition]
  have hw : (2:ℝ)/3 ≤ 1 - weight j := by linarith [weight_le_third hj]
  have h1 := mul_le_mul_of_nonneg_right hw (energy_nonneg v)
  have h2 := mul_le_mul_of_nonneg_left (energy_ge_half_mass v) (by norm_num : (0:ℝ) ≤ 2/3)
  have h3 := mul_nonneg (le_of_lt (weight_pos j)) (squareMinus_nonneg v)
  have h4 : mass v / 3 ≤ (1 - weight j) * energy v + weight j * squareMinus v := by linarith
  have h5 := mul_le_mul_of_nonneg_left h4 (le_of_lt gap_pos)
  nlinarith

/-- 尖锐等号完全确定一个复一维跳跃方向。 -/
theorem first_swap_equality_iff (v : Fin 3 → ℂ) :
    qa 0 v = slope * qb 0 v ↔
      v 1 = 0 ∧ v 0 + ((rootTwo / 2 : ℝ) : ℂ) * I * v 2 = 0 := by
  rw [← sub_eq_zero, first_swap_square]
  rw [mul_eq_zero, or_iff_right (ne_of_gt gap_pos)]
  unfold squareMinus
  constructor
  · intro h
    have hx := normSq_nonneg (v 0 + ((rootTwo / 2 : ℝ) : ℂ) * I * v 2)
    have hy := normSq_nonneg (v 1)
    constructor
    · apply normSq_eq_zero.mp
      linarith
    · apply normSq_eq_zero.mp
      linarith
  · rintro ⟨hy, hx⟩
    rw [hy, hx]
    norm_num

/-- 多个跳跃的谱隙直接求和；没有秩一假设。 -/
theorem finite_jump_gap {n j : ℕ} (hj : 1 ≤ j) (v : Fin n → Fin 3 → ℂ) :
    (gap / 3) * (∑ l, mass (v l)) ≤
      (∑ l, qa j (v l)) - slope * (∑ l, qb j (v l)) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun l _ => higher_frequency_gap hj (v l))
  simpa only [Finset.mul_sum, Finset.sum_sub_distrib] using h

/-- 参考 Hamiltonian 下的实际 Hermitian 二次型矩阵。 -/
def referenceMatrix (t : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 0, (t : ℂ) * I; 0, 1/2, 0; -(t : ℂ) * I, 0, 1/2]

def matrixQa (j : ℕ) : Matrix (Fin 3) (Fin 3) ℂ := referenceMatrix (2 / frequency j)
def matrixQb (j : ℕ) : Matrix (Fin 3) (Fin 3) ℂ := referenceMatrix (-2 / frequency j)

theorem referenceMatrix_hermitian (t : ℝ) : (referenceMatrix t).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [referenceMatrix, Matrix.conjTranspose_apply]

/-- 矩阵与标量形式完全一致，包含复相位交叉项。 -/
theorem referenceMatrix_form (t : ℝ) (v : Fin 3 → ℂ) :
    star v ⬝ᵥ ((referenceMatrix t) *ᵥ v) =
      ((energy v - 2 * t * cross v : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [referenceMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      energy, cross, normSq_apply, Complex.mul_re, Complex.mul_im] <;> ring

theorem matrixQa_form (j : ℕ) (v : Fin 3 → ℂ) :
    star v ⬝ᵥ (matrixQa j *ᵥ v) = ((qa j v : ℝ) : ℂ) := by
  rw [matrixQa, referenceMatrix_form]
  congr 1
  unfold qa
  ring

theorem matrixQb_form (j : ℕ) (v : Fin 3 → ℂ) :
    star v ⬝ᵥ (matrixQb j *ᵥ v) = ((qb j v : ℝ) : ℂ) := by
  rw [matrixQb, referenceMatrix_form]
  congr 1
  unfold qb
  ring

/-- 广义特征多项式；根的辨识将在下面直接给出。 -/
theorem generalized_determinant (t lam : ℝ) :
    (referenceMatrix t - (lam : ℂ) • referenceMatrix (-t)).det =
      (((1 - lam) * ((1 - lam)^2 - 2 * t^2 * (1 + lam)^2) / 4 : ℝ) : ℂ) := by
  rw [Matrix.det_fin_three]
  apply Complex.ext <;>
    simp [referenceMatrix, Matrix.sub_apply, pow_two,
      Complex.mul_re, Complex.mul_im]
  ring


/-- 首圈零方向的正交补平方长度；下面给出勾股分解。 -/
def perpendicularMass (v : Fin 3 → ℂ) : ℝ :=
  (2 / 3) * normSq (v 0 + ((rootTwo / 2 : ℝ) : ℂ) * I * v 2) + normSq (v 1)

def parallelMass (v : Fin 3 → ℂ) : ℝ :=
  (2 / 3) * normSq (-((rootTwo / 2 : ℝ) : ℂ) * I * v 0 - v 2)

theorem mass_orthogonal_split (v : Fin 3 → ℂ) :
    mass v = perpendicularMass v + parallelMass v := by
  simp only [mass, perpendicularMass, parallelMass, normSq_apply, add_re, add_im,
    sub_re, sub_im, neg_re, neg_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im]
  ring_nf
  rw [rootTwo_sq]
  ring

/-- 首圈在精确零方向的正交补上同样具有正谱隙。 -/
theorem first_frequency_gap (v : Fin 3 → ℂ) :
    (gap / 2) * perpendicularMass v ≤ qa 0 v - slope * qb 0 v := by
  rw [first_swap_square]
  unfold perpendicularMass squareMinus
  have hn := normSq_nonneg (v 0 + ((rootTwo / 2 : ℝ) : ℂ) * I * v 2)
  have h := mul_nonneg (le_of_lt gap_pos) hn
  nlinarith

def rankOneDirection (xi s q zeta : ℝ) : Fin 3 → ℂ :=
  ![(xi : ℂ) + (s : ℂ) * I, (q : ℂ) + (zeta : ℂ) * I, -1]

/-- 解析分支中四个完整复秩一方向的精确领先平方形式。 -/
theorem full_complex_leading_square (xi s q zeta : ℝ) :
    qa 0 (rankOneDirection xi s q zeta) - slope * qb 0 (rankOneDirection xi s q zeta) =
      gap * (xi^2 + (s - rootTwo/2)^2 + (q^2 + zeta^2)/2) := by
  rw [first_swap_square]
  congr 1
  simp [squareMinus, rankOneDirection, normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem full_complex_leading_coercive (xi s q zeta : ℝ) :
    (gap / 2) * (xi^2 + (s - rootTwo/2)^2 + q^2 + zeta^2) ≤
      qa 0 (rankOneDirection xi s q zeta) - slope * qb 0 (rankOneDirection xi s q zeta) := by
  rw [full_complex_leading_square]
  have h := mul_nonneg (le_of_lt gap_pos) (add_nonneg (sq_nonneg xi) (sq_nonneg (s-rootTwo/2)))
  nlinarith


/-- 广义特征多项式的实因子分解，保留精确 √2。 -/
theorem generalized_factorization (t lam : ℝ) :
    (referenceMatrix t - (lam : ℂ) • referenceMatrix (-t)).det =
      (((1-lam) * ((1-rootTwo*t)-(1+rootTwo*t)*lam) *
        ((1+rootTwo*t)-(1-rootTwo*t)*lam) / 4 : ℝ) : ℂ) := by
  rw [generalized_determinant]
  congr 1
  ring_nf
  rw [rootTwo_sq]
  ring

/-- 非退化参考矩阵对的全部实广义特征值。 -/
theorem generalized_real_spectrum (t lam : ℝ)
    (hlo : -1 < rootTwo*t) (hhi : rootTwo*t < 1) :
    (referenceMatrix t - (lam : ℂ) • referenceMatrix (-t)).det = 0 ↔
      lam = 1 ∨ lam = (1-rootTwo*t)/(1+rootTwo*t) ∨
        lam = (1+rootTwo*t)/(1-rootTwo*t) := by
  rw [generalized_factorization, Complex.ofReal_eq_zero]
  have hp : 1+rootTwo*t ≠ 0 := by linarith
  have hm : 1-rootTwo*t ≠ 0 := by linarith
  have h1 : 1-lam=0 ↔ lam=1 := by constructor <;> intro h <;> linarith
  have h2 : (1-rootTwo*t)-(1+rootTwo*t)*lam=0 ↔ lam=(1-rootTwo*t)/(1+rootTwo*t) := by
    rw [eq_div_iff hp]
    constructor <;> intro h <;> nlinarith
  have h3 : (1+rootTwo*t)-(1-rootTwo*t)*lam=0 ↔ lam=(1+rootTwo*t)/(1-rootTwo*t) := by
    rw [eq_div_iff hm]
    constructor <;> intro h <;> nlinarith
  simp only [div_eq_zero_iff, mul_eq_zero]
  norm_num
  rw [h1, h2, h3]
  tauto

theorem frequency_ge_pi (j : ℕ) : Real.pi ≤ frequency j := by
  unfold frequency
  have h := mul_nonneg (Nat.cast_nonneg j) (le_of_lt Real.pi_pos)
  nlinarith

theorem frequency_coupling_lt_one (j : ℕ) : rootTwo * (2 / frequency j) < 1 := by
  rw [← mul_div_assoc]
  apply (div_lt_one (frequency_pos j)).2
  linarith [frequency_ge_pi j, twice_rootTwo_lt_pi]

def frequencySlope (j : ℕ) : ℝ :=
  (1-rootTwo*(2/frequency j))/(1+rootTwo*(2/frequency j))

/-- 主稿所有圈数的精确广义谱。 -/
theorem all_frequency_real_spectrum (j : ℕ) (lam : ℝ) :
    (matrixQa j - (lam : ℂ) • matrixQb j).det = 0 ↔
      lam = 1 ∨ lam = frequencySlope j ∨ lam = (frequencySlope j)⁻¹ := by
  have hc : 0 < rootTwo * (2 / frequency j) := mul_pos rootTwo_pos (div_pos (by norm_num) (frequency_pos j))
  unfold matrixQa matrixQb
  rw [show -2 / frequency j = -(2 / frequency j) by ring]
  rw [generalized_real_spectrum _ _ (by linarith) (frequency_coupling_lt_one j)]
  simp only [frequencySlope, inv_div]

theorem frequencySlope_zero : frequencySlope 0 = slope := by
  unfold frequencySlope
  rw [frequency_zero]
  unfold slope
  have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp

theorem frequencySlope_formula (j : ℕ) :
    frequencySlope j = (frequency j-2*rootTwo)/(frequency j+2*rootTwo) := by
  unfold frequencySlope
  have hw : frequency j ≠ 0 := ne_of_gt (frequency_pos j)
  field_simp

theorem frequencySlope_pos (j : ℕ) : 0 < frequencySlope j := by
  unfold frequencySlope
  have hc : 0 < rootTwo*(2/frequency j) :=
    mul_pos rootTwo_pos (div_pos (by norm_num) (frequency_pos j))
  exact div_pos (sub_pos.mpr (frequency_coupling_lt_one j)) (by linarith)

theorem frequencySlope_ge_first (j : ℕ) : slope ≤ frequencySlope j := by
  rw [frequencySlope_formula]
  unfold slope
  apply (div_le_div_iff₀ (by linarith [Real.pi_pos, rootTwo_pos] : 0 < Real.pi+2*rootTwo)
    (by linarith [frequency_pos j, rootTwo_pos] : 0 < frequency j+2*rootTwo)).2
  have h := mul_nonneg (le_of_lt rootTwo_pos) (sub_nonneg.mpr (frequency_ge_pi j))
  nlinarith

/-- 矩阵形式的半正定证书：二次型证明不依赖所选跳跃分解。 -/
theorem dual_matrix_psd (j : ℕ) :
    (matrixQa j - (slope : ℂ) • matrixQb j).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i k
    fin_cases i <;> fin_cases k <;>
      simp [matrixQa, matrixQb, referenceMatrix, Matrix.conjTranspose_apply, sub_eq_add_neg]
  · intro v
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul,
      matrixQa_form, matrixQb_form]
    rw [Complex.le_def]
    constructor
    · simpa using sub_nonneg.mpr (all_frequency_sharp j v)
    · simp


/-- 用真实平方根完成 Young 配方，供统一 Duhamel 余项吸收。 -/
theorem young_remainder (p c d : ℝ) (hp : 0 ≤ p) :
    c * d * Real.sqrt p ≤ gap * p / 2 + (c^2 / (2*gap)) * d^2 := by
  have hg : gap ≠ 0 := ne_of_gt gap_pos
  have hs := Real.sq_sqrt hp
  have hid : gap * p / 2 + (c^2 / (2*gap)) * d^2 - c*d*Real.sqrt p =
      (gap*Real.sqrt p-c*d)^2 / (2*gap) := by
    field_simp
    nlinarith [sq_nonneg (gap*Real.sqrt p-c*d)]
  have h := div_nonneg (sq_nonneg (gap*Real.sqrt p-c*d)) (by linarith [gap_pos] : 0 ≤ 2*gap)
  rw [← hid] at h
  linarith

def remainderSize (p d : ℝ) : ℝ := 34*d*Real.sqrt p + 8*d^2

def localizationConstant (C D : ℝ) : ℝ :=
  C + ((34*(1+slope))^2/(2*gap) + 8*(1+slope))*D^2

/-- 这是连接实际 Duhamel 估计的接口；假设只列出逐项余项界。 -/
theorem localization_energy {n j : ℕ} (v : Fin n → Fin 3 → ℂ)
    (a b p d Ra Rb C D : ℝ)
    (hp : 0 ≤ p) (hd : 0 ≤ d)
    (ha : a = p + (∑ l, qa j (v l)) + Ra)
    (hbexp : b = p + (∑ l, qb j (v l)) + Rb)
    (hRa : |Ra| ≤ remainderSize p d) (hRb : |Rb| ≤ remainderSize p d)
    (hnear : a ≤ slope*b + C*b^2) (hscale : d ≤ D*b) :
    (gap/2)*p + (∑ l, (qa j (v l) - slope*qb j (v l))) ≤
      localizationConstant C D * b^2 := by
  have hRa' := (abs_le.mp hRa).1
  have hRb' := mul_le_mul_of_nonneg_left (abs_le.mp hRb).2 (le_of_lt slope_pos)
  have hyoung := young_remainder p (34*(1+slope)) d hp
  have hdsq : d^2 ≤ D^2*b^2 := by
    have h := mul_self_le_mul_self hd hscale
    nlinarith
  have hcoef : 0 ≤ (34*(1+slope))^2/(2*gap) + 8*(1+slope) := by
    have hr := slope_pos
    have hg := gap_pos
    positivity
  have hbound := mul_le_mul_of_nonneg_left hdsq hcoef
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  unfold localizationConstant remainderSize at *
  unfold gap at *
  have hscaled : slope*b = slope*p + slope*(∑ l, qb j (v l)) + slope*Rb := by
    rw [hbexp]
    ring
  rw [ha] at hnear
  nlinarith only [hnear, hscaled, hRa', hRb', hyoung, hbound]

/-- 一旦解析余项给出能量定位，严格谱隙排除每个较高绕圈数。 -/
theorem exclude_higher_frequencies {n j : ℕ} (v : Fin n → Fin 3 → ℂ)
    (b p L : ℝ) (hb : 0 < b) (hp : 0 ≤ p) (hL : 0 < L)
    (hsmall : b < gap/(12*L))
    (hmass : b/4 ≤ ∑ l, mass (v l))
    (henergy : (gap/2)*p + (∑ l, (qa j (v l)-slope*qb j (v l))) ≤ L*b^2) : j=0 := by
  by_contra hj
  have hj' : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj
  have hs := finite_jump_gap hj' v
  have hm := mul_le_mul_of_nonneg_left hmass (by linarith [gap_pos] : 0 ≤ gap/3)
  have hpp := mul_nonneg (by linarith [gap_pos] : 0 ≤ gap/2) hp
  have hsmall' : b*(12*L) < gap := (lt_div_iff₀ (by positivity : 0 < 12*L)).mp hsmall
  have hstrict := mul_lt_mul_of_pos_right hsmall' hb
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at henergy
  nlinarith


/-- 最优比值由一个明确的非零复跳跃方向达到。 -/
theorem equality_direction_value :
    qb 0 (rankOneDirection 0 (rootTwo/2) 0 0) = 1 + 2*rootTwo/Real.pi := by
  simp [qb, energy, cross, rankOneDirection, frequency_zero, normSq_apply,
    Complex.mul_re, Complex.mul_im]
  ring_nf
  rw [rootTwo_sq]
  norm_num [Complex.mul_re]
  ring

theorem sharp_slope_attained : ∃ v : Fin 3 → ℂ, 0 < qb 0 v ∧ qa 0 v = slope*qb 0 v := by
  refine ⟨rankOneDirection 0 (rootTwo/2) 0 0, ?_, ?_⟩
  · rw [equality_direction_value]
    have h := div_pos (mul_pos (by norm_num : (0:ℝ)<2) rootTwo_pos) Real.pi_pos
    linarith
  · have h := full_complex_leading_square 0 (rootTwo/2) 0 0
    simp only [zero_pow (by norm_num : 2 ≠ 0), sub_self, add_zero, zero_div, mul_zero] at h
    exact sub_eq_zero.mp h


/-- 任意有限跳跃族的实际 Kossakowski 矩阵。 -/
def kossakowski {n : ℕ} (v : Fin n → Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  ∑ l, Matrix.vecMulVec (v l) (star (v l))

theorem trace_matrix_outer (M : Matrix (Fin 3) (Fin 3) ℂ) (v : Fin 3 → ℂ) :
    (M * Matrix.vecMulVec v (star v)).trace = star v ⬝ᵥ (M *ᵥ v) := by
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

theorem trace_outer (v : Fin 3 → ℂ) :
    (Matrix.vecMulVec v (star v)).trace = ((mass v : ℝ) : ℂ) := by
  rw [Matrix.trace_vecMulVec]
  apply Complex.ext <;>
    simp [mass, dotProduct, Fin.sum_univ_succ, normSq_apply, Complex.mul_re, Complex.mul_im] <;> ring

theorem trace_kossakowski {n : ℕ} (v : Fin n → Fin 3 → ℂ) :
    (kossakowski v).trace = ((∑ l, mass (v l) : ℝ) : ℂ) := by
  simp only [kossakowski, Matrix.trace_sum, trace_outer]
  push_cast
  rfl

theorem trace_Qa_kossakowski {n : ℕ} (j : ℕ) (v : Fin n → Fin 3 → ℂ) :
    (matrixQa j * kossakowski v).trace = ((∑ l, qa j (v l) : ℝ) : ℂ) := by
  simp only [kossakowski, Finset.mul_sum, Matrix.trace_sum, trace_matrix_outer, matrixQa_form]
  push_cast
  rfl

theorem trace_Qb_kossakowski {n : ℕ} (j : ℕ) (v : Fin n → Fin 3 → ℂ) :
    (matrixQb j * kossakowski v).trace = ((∑ l, qb j (v l) : ℝ) : ℂ) := by
  simp only [kossakowski, Finset.mul_sum, Matrix.trace_sum, trace_matrix_outer, matrixQb_form]
  push_cast
  rfl

/-- 主稿的 Tr(S_j K) ≥ A Tr(K)/3，适用于所有有限复跳跃族。 -/
theorem kossakowski_trace_gap {n j : ℕ} (hj : 1 ≤ j) (v : Fin n → Fin 3 → ℂ) :
    ((gap/3 : ℝ) : ℂ) * (kossakowski v).trace ≤
      ((matrixQa j - (slope : ℂ) • matrixQb j) * kossakowski v).trace := by
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul,
    trace_kossakowski, trace_Qa_kossakowski, trace_Qb_kossakowski]
  have h := finite_jump_gap hj v
  simp only [smul_eq_mul]
  rw [Complex.le_def]
  constructor
  · simpa using h
  · simp

/-- 切锥等号的多跳跃刚性：每一个跳跃都在同一复一维核中。 -/
theorem finite_jump_equality_rigidity {n : ℕ} (v : Fin n → Fin 3 → ℂ)
    (heq : (∑ l, qa 0 (v l)) = slope*(∑ l, qb 0 (v l))) :
    ∀ l, v l 1 = 0 ∧ v l 0 + ((rootTwo/2 : ℝ) : ℂ)*I*v l 2 = 0 := by
  have hsum : (∑ l, (qa 0 (v l)-slope*qb 0 (v l))) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, heq, sub_self]
  intro l
  have hn : ∀ m : Fin n, 0 ≤ qa 0 (v m)-slope*qb 0 (v m) :=
    fun m => sub_nonneg.mpr (first_swap_sharp (v m))
  have hle := Finset.single_le_sum (fun m _ => hn m) (Finset.mem_univ l)
  rw [hsum] at hle
  apply (first_swap_equality_iff (v l)).mp
  linarith [hn l]


def kernelVector : Fin 3 → ℂ := ![-((rootTwo/2 : ℝ) : ℂ)*I, 0, 1]

theorem equality_vector_factor (v : Fin 3 → ℂ) (heq : qa 0 v = slope*qb 0 v) :
    v = (v 2) • kernelVector := by
  obtain ⟨hy, hx⟩ := (first_swap_equality_iff v).mp heq
  ext i
  fin_cases i
  · change v 0 = v 2 * (-((rootTwo/2 : ℝ) : ℂ)*I)
    have h := eq_neg_of_add_eq_zero_left hx
    calc
      v 0 = -(((rootTwo/2 : ℝ) : ℂ)*I*v 2) := h
      _ = _ := by ring
  · simpa [kernelVector] using hy
  · simp [kernelVector]

theorem outer_smul (c : ℂ) (v : Fin 3 → ℂ) :
    Matrix.vecMulVec (c • v) (star (c • v)) =
      ((normSq c : ℝ) : ℂ) • Matrix.vecMulVec v (star v) := by
  ext i j
  simp [Matrix.vecMulVec, normSq_eq_conj_mul_self, smul_eq_mul]
  ring

/-- 切锥等号直接给出 K 的显式秩至多一分解。 -/
theorem endpoint_kossakowski_factorization {n : ℕ} (v : Fin n → Fin 3 → ℂ)
    (heq : (∑ l, qa 0 (v l)) = slope*(∑ l, qb 0 (v l))) :
    kossakowski v = ((∑ l, normSq (v l 2) : ℝ) : ℂ) •
      Matrix.vecMulVec kernelVector (star kernelVector) := by
  have heach := finite_jump_equality_rigidity v heq
  have hv : ∀ l, v l = (v l 2) • kernelVector := fun l =>
    equality_vector_factor (v l) ((first_swap_equality_iff (v l)).mpr (heach l))
  unfold kossakowski
  conv_lhs => arg 2; ext l; rw [hv l, outer_smul]
  rw [← Finset.sum_smul]
  congr 1
  push_cast
  rfl


/- 审计全部定理的传递公理依赖。 -/
#print axioms rootTwo_pos
#print axioms rootTwo_sq
#print axioms twice_rootTwo_lt_pi
#print axioms slope_pos
#print axioms slope_lt_one
#print axioms gap_pos
#print axioms coupling_identity
#print axioms frequency_pos
#print axioms frequency_zero
#print axioms squareMinus_identity
#print axioms squarePlus_identity
#print axioms squareMinus_nonneg
#print axioms squarePlus_nonneg
#print axioms energy_nonneg
#print axioms mass_nonneg
#print axioms energy_ge_half_mass
#print axioms first_swap_square
#print axioms first_swap_sharp
#print axioms weight_pos
#print axioms weight_le_one
#print axioms weight_le_third
#print axioms all_frequency_decomposition
#print axioms all_frequency_sharp
#print axioms higher_frequency_gap
#print axioms first_swap_equality_iff
#print axioms finite_jump_gap
#print axioms referenceMatrix_hermitian
#print axioms referenceMatrix_form
#print axioms matrixQa_form
#print axioms matrixQb_form
#print axioms generalized_determinant
#print axioms mass_orthogonal_split
#print axioms first_frequency_gap
#print axioms full_complex_leading_square
#print axioms full_complex_leading_coercive
#print axioms generalized_factorization
#print axioms generalized_real_spectrum
#print axioms frequency_ge_pi
#print axioms frequency_coupling_lt_one
#print axioms all_frequency_real_spectrum
#print axioms frequencySlope_zero
#print axioms frequencySlope_formula
#print axioms frequencySlope_pos
#print axioms frequencySlope_ge_first
#print axioms dual_matrix_psd
#print axioms young_remainder
#print axioms localization_energy
#print axioms exclude_higher_frequencies
#print axioms equality_direction_value
#print axioms sharp_slope_attained
#print axioms trace_matrix_outer
#print axioms trace_outer
#print axioms trace_kossakowski
#print axioms trace_Qa_kossakowski
#print axioms trace_Qb_kossakowski
#print axioms kossakowski_trace_gap
#print axioms finite_jump_equality_rigidity
#print axioms equality_vector_factor
#print axioms outer_smul
#print axioms endpoint_kossakowski_factorization
end
end Swap

