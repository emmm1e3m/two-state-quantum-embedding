import Mathlib
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import QICLean.Channel.KrausRepresentation
import QICLean.Channel.CompletelyPositiveBridge
import QICLean.Channel.Semigroup.CPClosure
import QICLean.Channel.Semigroup.LindbladForm

/-! 根层级的显式二次根与有限层斜率。 -/
noncomputable section
namespace TwoStateRoots

/-- q 是恒等通道的混合权重，t 是原文参数 r 的平方。 -/
def probA (q t : ℝ) : ℝ := q ^ 2 + 2 * q * (1 - q) * t / (1 + t)
def probB (q t : ℝ) : ℝ :=
  q ^ 2 + 2 * q * (1 - q) * (1 - t ^ 2 / (1 + t)) + (1 - q) ^ 2 * (1 - t ^ 2)
def discr (a t : ℝ) : ℝ := a + (1 - a) * t ^ 2
def weight (a t : ℝ) : ℝ := a * (1 + t) / (t + Real.sqrt (discr a t))

lemma discr_pos {a t : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) : 0 < discr a t := by
  unfold discr
  positivity

lemma weight_denom_pos {a t : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (ht : 0 ≤ t) :
    0 < t + Real.sqrt (discr a t) := by
  have := Real.sqrt_pos.2 (discr_pos (t := t) ha ha1)
  positivity

lemma weight_mem {a t : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (ht : 0 ≤ t) (_ht1 : t ≤ 1) : weight a t ∈ Set.Icc (0 : ℝ) 1 := by
  have hd := weight_denom_pos ha ha1 ht
  have hs := Real.sqrt_nonneg (discr a t)
  have hs2 := Real.sq_sqrt (le_of_lt (discr_pos (t := t) ha ha1))
  have hn : a * (1 + t) ≤ t + Real.sqrt (discr a t) := by
    have hprod : 0 ≤ a * (1 - a) * (1 + t) ^ 2 := by positivity
    change Real.sqrt (discr a t) ^ 2 = a + (1 - a) * t ^ 2 at hs2
    nlinarith [sq_nonneg (a * (1 + t) - t + Real.sqrt (discr a t))]
  constructor
  · exact div_nonneg (by positivity) (le_of_lt hd)
  · exact (div_le_one hd).2 hn

lemma weight_equation {a t : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (ht : 0 ≤ t) :
    (1 - t) * weight a t ^ 2 + 2 * t * weight a t = a * (1 + t) := by
  have hd := ne_of_gt (weight_denom_pos ha ha1 ht)
  have hs2 := Real.sq_sqrt (le_of_lt (discr_pos (t := t) ha ha1))
  unfold weight
  field_simp
  change Real.sqrt (discr a t) ^ 2 = a + (1 - a) * t ^ 2 at hs2
  nlinarith [hs2]

lemma probA_weight {a t : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (ht : 0 ≤ t) :
    probA (weight a t) t = a := by
  have he := weight_equation ha ha1 ht
  have hd : 1 + t ≠ 0 := by positivity
  unfold probA
  field_simp
  nlinarith [he]

lemma continuousOn_weight {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ContinuousOn (weight a) (Set.Icc (0 : ℝ) 1) := by
  apply ContinuousOn.div
  · fun_prop
  · unfold discr
    fun_prop
  · intro t ht
    exact ne_of_gt (weight_denom_pos ha ha1 ht.1)

lemma weight_one {a : ℝ} (_ha : 0 < a) (_ha1 : a ≤ 1) : weight a 1 = a := by
  simp [weight, discr]
lemma probB_zero (q : ℝ) : probB q 0 = 1 := by
  unfold probB
  norm_num
  ring
lemma probA_one (q : ℝ) : probA q 1 = q := by
  unfold probA
  norm_num
  ring
lemma probB_one (q : ℝ) : probB q 1 = q := by
  unfold probB
  norm_num
  ring

/-- 上三角中的每一点都有合法混合权重和合法 Kraus 参数。 -/
theorem upper_triangle_fill {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ∃ q ∈ Set.Icc (0 : ℝ) 1, ∃ t ∈ Set.Icc (0 : ℝ) 1,
      probA q t = a ∧ probB q t = b := by
  by_cases haz : a = 0
  · subst a
    have hcont : ContinuousOn (fun t : ℝ => 1 - t ^ 2) (Set.Icc (0 : ℝ) 1) := by fun_prop
    have hmem : b ∈ Set.Icc ((fun t : ℝ => 1 - t ^ 2) 1)
        ((fun t : ℝ => 1 - t ^ 2) 0) := by simpa using And.intro hab hb
    obtain ⟨t, ht, htb⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hcont hmem
    refine ⟨0, by norm_num, t, ht, ?_, ?_⟩
    · simp [probA]
    · simpa [probB] using htb
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
    have ha1 : a ≤ 1 := hab.trans hb
    have hw := continuousOn_weight hap ha1
    have hcont : ContinuousOn (fun t => probB (weight a t) t) (Set.Icc (0 : ℝ) 1) := by
      unfold probB
      have hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, 1 + t ≠ 0 := by
        intro t ht
        linarith [ht.1]
      have hf : ContinuousOn (fun t : ℝ => t ^ 2 / (1 + t)) (Set.Icc (0 : ℝ) 1) :=
        (continuousOn_id.pow 2).div (continuousOn_const.add continuousOn_id) hne
      exact ((hw.pow 2).add (((continuousOn_const.mul hw).mul
        (continuousOn_const.sub hw)).mul (continuousOn_const.sub hf))).add
        (((continuousOn_const.sub hw).pow 2).mul
          (continuousOn_const.sub (continuousOn_id.pow 2)))
    have he0 : probB (weight a 0) 0 = 1 := probB_zero _
    have he1 : probB (weight a 1) 1 = a := by rw [weight_one hap ha1, probB_one]
    have hmem : b ∈ Set.Icc (probB (weight a 1) 1) (probB (weight a 0) 0) := by
      rw [he0, he1]
      exact ⟨hab, hb⟩
    obtain ⟨t, ht, htb⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hcont hmem
    exact ⟨weight a t, weight_mem hap ha1 ht.1 ht.2, t, ht,
      probA_weight hap ha1 ht.1, htb⟩
open scoped Matrix ComplexOrder
open Matrix
abbrev M2 := Matrix (Fin 2) (Fin 2) ℂ

def P0 : M2 := !![1, 0; 0, 0]
def P1 : M2 := !![0, 0; 0, 1]
def core (r : ℝ) : M2 := !![(r : ℂ), -(r : ℂ)^2; 1, (r : ℂ)^3]

def sandwich (A : M2) : M2 →ₗ[ℂ] M2 where
  toFun X := A * X * A.conjTranspose
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp

lemma sandwich_real_smul (A X : M2) (c : ℝ) :
    sandwich ((c : ℂ) • A) X = ((c ^ 2 : ℝ) : ℂ) • sandwich A X := by
  simp [sandwich, Matrix.conjTranspose_smul, smul_smul, pow_two]
  rw [← Complex.ofReal_mul, Complex.coe_smul]

def axis (r : ℝ) : M2 →ₗ[ℂ] M2 :=
  ((1 / (1 + r ^ 2) : ℝ) : ℂ) • sandwich (core r) +
    ((1 - r ^ 4 : ℝ) : ℂ) • sandwich P1

def mix (q r : ℝ) : M2 →ₗ[ℂ] M2 :=
  (q : ℂ) • LinearMap.id + ((1 - q : ℝ) : ℂ) • axis r

def mixKraus (q r : ℝ) : Fin 3 → M2 :=
  ![(Real.sqrt q : ℂ) • 1,
    (Real.sqrt ((1 - q) / (1 + r ^ 2)) : ℂ) • core r,
    (Real.sqrt ((1 - q) * (1 - r ^ 4)) : ℂ) • P1]

lemma r_four_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : r ^ 4 ≤ 1 := by
  exact pow_le_one₀ hr0 hr1

lemma mix_kraus {q r : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (X : M2) :
    mix q r X = ∑ i, mixKraus q r i * X * (mixKraus q r i).conjTranspose := by
  have hr4 := r_four_le hr0 hr1
  have hq : 0 ≤ (1 - q) / (1 + r ^ 2) := by positivity
  have hqr : 0 ≤ (1 - q) * (1 - r ^ 4) := by positivity
  simp only [mixKraus, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Matrix.head_cons, Matrix.head_fin_const]
  change mix q r X = sandwich ((Real.sqrt q : ℂ) • 1) X +
    sandwich ((Real.sqrt ((1 - q) / (1 + r ^ 2)) : ℂ) • core r) X +
    sandwich ((Real.sqrt ((1 - q) * (1 - r ^ 4)) : ℂ) • P1) X
  rw [sandwich_real_smul, sandwich_real_smul, sandwich_real_smul,
    Real.sq_sqrt hq0, Real.sq_sqrt hq, Real.sq_sqrt hqr]
  simp [mix, axis, sandwich, smul_add, smul_smul, div_eq_mul_inv, mul_assoc, add_assoc]

lemma axis_trace (r : ℝ) (X : M2) : Matrix.trace (axis r X) = Matrix.trace X := by
  have hdR : 1 + r ^ 2 ≠ 0 := by positivity
  have hd : (1 + (r : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hdR
  simp [axis, sandwich, core, P1, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.conjTranspose, Matrix.vecMul, dotProduct, Matrix.vecHead, Matrix.vecTail, Matrix.transpose_apply, Matrix.map_apply]
  field_simp
  ring

lemma mix_trace (q r : ℝ) (X : M2) : Matrix.trace (mix q r X) = Matrix.trace X := by
  simp [mix, axis_trace]
  ring

lemma mix_channel {q r : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : IsChannel (mix q r) := by
  exact ⟨⟨3, mixKraus q r, mix_kraus hq0 hq1 hr0 hr1⟩, mix_trace q r⟩




lemma mix_sq_a (q r : ℝ) :
    (mix q r (mix q r P0)) 0 0 =
      ((q ^ 2 + 2 * q * (1 - q) * r ^ 2 / (1 + r ^ 2) : ℝ) : ℂ) := by
  have hdR : 1 + r ^ 2 ≠ 0 := by positivity
  have hd : (1 + (r : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hdR
  simp [mix, axis, sandwich, core, P0, P1,
    Fin.sum_univ_two, Matrix.conjTranspose, Matrix.vecMul, dotProduct, Matrix.vecHead, Matrix.vecTail, Matrix.transpose_apply, Matrix.map_apply]
  field_simp
  ring

lemma mix_sq_b (q r : ℝ) :
    (mix q r (mix q r P1)) 1 1 =
      ((q ^ 2 + 2 * q * (1 - q) * (1 - (r ^ 2) ^ 2 / (1 + r ^ 2)) +
        (1 - q) ^ 2 * (1 - (r ^ 2) ^ 2) : ℝ) : ℂ) := by
  have hdR : 1 + r ^ 2 ≠ 0 := by positivity
  have hd : (1 + (r : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hdR
  simp [mix, axis, sandwich, core, P1,
    Fin.sum_univ_two, Matrix.conjTranspose, Matrix.vecMul, dotProduct, Matrix.vecHead, Matrix.vecTail, Matrix.transpose_apply, Matrix.map_apply]
  field_simp
  ring

#print axioms mix_channel
#print axioms mix_sq_a
#print axioms mix_sq_b



/-- 交换两个计算基态的酉算子。 -/
def flipMatrix : M2 := !![0, 1; 1, 0]
def flipMap : M2 →ₗ[ℂ] M2 := sandwich flipMatrix

lemma flipMatrix_star : flipMatrix.conjTranspose = flipMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [flipMatrix, Matrix.conjTranspose_apply]

lemma flipMatrix_sq : flipMatrix * flipMatrix = (1 : M2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [flipMatrix, Matrix.mul_apply, Fin.sum_univ_two]

lemma flipMap_entries (X : M2) : flipMap X = !![X 1 1, X 1 0; X 0 1, X 0 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flipMap, sandwich, flipMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose, Matrix.vecMul, dotProduct]

lemma flipMap_twice (X : M2) : flipMap (flipMap X) = X := by
  rw [flipMap_entries, flipMap_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

lemma flipMap_P0 : flipMap P0 = P1 := by rw [flipMap_entries]; rfl
lemma flipMap_P1 : flipMap P1 = P0 := by rw [flipMap_entries]; rfl

lemma flipMap_trace (X : M2) : Matrix.trace (flipMap X) = Matrix.trace X := by
  rw [flipMap_entries]
  simp [Matrix.trace, Fin.sum_univ_two, add_comm]

def flipped (T : M2 →ₗ[ℂ] M2) : M2 →ₗ[ℂ] M2 := flipMap.comp (T.comp flipMap)

lemma flipped_channel {T : M2 →ₗ[ℂ] M2} (hT : IsChannel T) : IsChannel (flipped T) := by
  obtain ⟨k, K, hK⟩ := hT.cp
  constructor
  · refine ⟨k, fun i => flipMatrix * K i * flipMatrix, ?_⟩
    intro X
    simp only [flipped, LinearMap.comp_apply, flipMap, sandwich, LinearMap.coe_mk,
      AddHom.coe_mk, hK, flipMatrix_star]
    simp [Finset.sum_mul, Finset.mul_sum, Matrix.conjTranspose_mul, flipMatrix_star,
      Matrix.mul_assoc]
  · intro X
    simp only [flipped, LinearMap.comp_apply, flipMap_trace]
    exact (hT.tp (flipMap X)).trans (flipMap_trace X)

lemma flipped_twice (T : M2 →ₗ[ℂ] M2) (X : M2) :
    flipped T (flipped T X) = flipMap (T (T (flipMap X))) := by
  simp [flipped, flipMap_twice]

lemma flipped_sq_a (T : M2 →ₗ[ℂ] M2) :
    (flipped T (flipped T P0)) 0 0 = (T (T P1)) 1 1 := by
  rw [flipped_twice, flipMap_P0, flipMap_entries]
  rfl
lemma flipped_sq_b (T : M2 →ₗ[ℂ] M2) :
    (flipped T (flipped T P1)) 1 1 = (T (T P0)) 0 0 := by
  rw [flipped_twice, flipMap_P1, flipMap_entries]
  rfl






/-- 任意上三角点由一个明确的三 Kraus CPTP 平方根实现。 -/
theorem upper_triangle_channel {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ∃ T : M2 →ₗ[ℂ] M2, IsChannel T ∧
      (T (T P0)) 0 0 = (a : ℂ) ∧ (T (T P1)) 1 1 = (b : ℂ) := by
  obtain ⟨q, hq, t, ht, hqa, hqb⟩ := upper_triangle_fill ha hab hb
  have hr0 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
  have hr1 : Real.sqrt t ≤ 1 := (Real.sqrt_le_one).2 ht.2
  refine ⟨mix q (Real.sqrt t), mix_channel hq.1 hq.2 hr0 hr1, ?_, ?_⟩
  · have he := mix_sq_a q (Real.sqrt t)
    rw [Real.sq_sqrt ht.1] at he
    change _ = (probA q t : ℂ) at he
    rwa [hqa] at he
  · have he := mix_sq_b q (Real.sqrt t)
    rw [Real.sq_sqrt ht.1] at he
    change _ = (probB q t : ℂ) at he
    rwa [hqb] at he

/-- 全正方形中的任意二态随机矩阵都拥有量子 CPTP 平方根实现。 -/
theorem square_root_realization {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    ∃ T : M2 →ₗ[ℂ] M2, IsChannel T ∧
      (T (T P0)) 0 0 = (a : ℂ) ∧ (T (T P1)) 1 1 = (b : ℂ) := by
  rcases le_total a b with hab | hba
  · exact upper_triangle_channel ha.1 hab hb.2
  · obtain ⟨T, hT, hTb, hTa⟩ := upper_triangle_channel hb.1 hba ha.2
    refine ⟨flipped T, flipped_channel hT, ?_, ?_⟩
    · rwa [flipped_sq_a]
    · rwa [flipped_sq_b]

lemma P0_density : P0 ∈ densityMatrices 2 := by
  constructor
  · have hd : (Matrix.diagonal (![1, 0] : Fin 2 → ℂ)).PosSemidef :=
      Matrix.PosSemidef.diagonal (by intro i; fin_cases i <;> norm_num)
    convert hd using 1
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [P0, Matrix.diagonal]
  · norm_num [P0, Matrix.trace, Fin.sum_univ_two]

lemma P1_density : P1 ∈ densityMatrices 2 := by
  constructor
  · have hd : (Matrix.diagonal (![0, 1] : Fin 2 → ℂ)).PosSemidef :=
      Matrix.PosSemidef.diagonal (by intro i; fin_cases i <;> norm_num)
    convert hd using 1
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [P1, Matrix.diagonal]
  · norm_num [P1, Matrix.trace, Fin.sum_univ_two]

lemma density_diag_bounds {X : M2} (hX : X ∈ densityMatrices 2) (i : Fin 2) :
    (X i i).re ∈ Set.Icc (0 : ℝ) 1 := by
  have h0 : 0 ≤ (X 0 0).re := (RCLike.nonneg_iff.mp (hX.1.diag_nonneg (i := 0))).1
  have h1 : 0 ≤ (X 1 1).re := (RCLike.nonneg_iff.mp (hX.1.diag_nonneg (i := 1))).1
  have hsum : (X 0 0).re + (X 1 1).re = 1 := by
    have he := congrArg Complex.re hX.2
    simpa [Matrix.trace, Fin.sum_univ_two] using he
  fin_cases i
  · change (X 0 0).re ∈ Set.Icc (0 : ℝ) 1
    exact ⟨h0, by linarith⟩
  · change (X 1 1).re ∈ Set.Icc (0 : ℝ) 1
    exact ⟨h1, by linarith⟩

/-- 与论文一致的经典作用投影。 -/
def classicalAction (T : M2 →ₗ[ℂ] M2) : ℝ × ℝ := ((T P0) 0 0 |>.re, (T P1) 1 1 |>.re)

/-- 根层允许每个 n 选取不同的底层 CPTP 通道。 -/
def rootLayer (n : ℕ) : Set (ℝ × ℝ) :=
  {p | ∃ T : M2 →ₗ[ℂ] M2, IsChannel T ∧ classicalAction (T ^ n) = p}

def probabilitySquare : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1

/-- K009 的二次根层结论，包含两边集合包含关系。 -/
theorem rootLayer_two_eq_square : rootLayer 2 = probabilitySquare := by
  ext p
  constructor
  · rintro ⟨T, hT, rfl⟩
    constructor
    · have hD := hT.map_densityMatrices T (T P0) (hT.map_densityMatrices T P0 P0_density)
      simpa [classicalAction, pow_two, Module.End.mul_apply] using density_diag_bounds hD 0
    · have hD := hT.map_densityMatrices T (T P1) (hT.map_densityMatrices T P1 P1_density)
      simpa [classicalAction, pow_two, Module.End.mul_apply] using density_diag_bounds hD 1
  · intro hp
    obtain ⟨T, hT, ha, hb⟩ := square_root_realization hp.1 hp.2
    refine ⟨T, hT, ?_⟩
    apply Prod.ext
    · simpa [classicalAction, pow_two, Module.End.mul_apply] using congrArg Complex.re ha
    · simpa [classicalAction, pow_two, Module.End.mul_apply] using congrArg Complex.re hb

#print axioms upper_triangle_fill
#print axioms square_root_realization
#print axioms rootLayer_two_eq_square
#print axioms IsCPMap.toCompletelyPositiveMap


lemma channel_pow_trace {T : M2 →ₗ[ℂ] M2} (hT : IsChannel T) (n : ℕ) (X : M2) :
    Matrix.trace ((T ^ n) X) = Matrix.trace X := by
  induction n generalizing X with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    exact hT.tp X

lemma channel_pow {T : M2 →ₗ[ℂ] M2} (hT : IsChannel T) (n : ℕ) : IsChannel (T ^ n) :=
  ⟨hT.cp.pow n, channel_pow_trace hT n⟩

/-- 整除关系给出实际 CPTP 根层的反向包含。 -/
theorem rootLayer_antitone_dvd {m n : ℕ} (hmn : m ∣ n) : rootLayer n ⊆ rootLayer m := by
  rcases hmn with ⟨k, rfl⟩
  rintro p ⟨T, hT, hproj⟩
  refine ⟨T ^ k, channel_pow hT k, ?_⟩
  simpa only [← pow_mul, Nat.mul_comm] using hproj

/-- 阶乘子序列与全部正整数根层具有相同交集；这里尚未认同为 GKSL 闭包。 -/
theorem all_roots_iff_factorial (p : ℝ × ℝ) :
    (∀ n : ℕ, 0 < n → p ∈ rootLayer n) ↔
      (∀ m : ℕ, p ∈ rootLayer ((m + 1).factorial)) := by
  constructor
  · intro h m
    exact h _ (Nat.factorial_pos _)
  · intro h n hn
    have hnf : n ∣ n.factorial := Nat.dvd_factorial hn (Nat.le_refl _)
    apply rootLayer_antitone_dvd hnf
    have he : n - 1 + 1 = n := by omega
    simpa only [he] using h (n - 1)

#print axioms rootLayer_antitone_dvd
#print axioms all_roots_iff_factorial


/-- 明确记录所给三 Kraus 算子的归一化，而不仅记录通道保迹。 -/
theorem mixKraus_normalized {q r : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∑ i, (mixKraus q r i).conjTranspose * mixKraus q r i = (1 : M2) :=
  kraus_sum_conjTranspose_mul_of_tp (mixKraus q r) (mix q r)
    (mix_kraus hq0 hq1 hr0 hr1) (mix_trace q r)

/-- 所构造根在任意辅助维度上保持正性，使用 mathlib 的真实 CP 语义。 -/
theorem mix_all_auxiliary_positive {q r : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (k : ℕ)
    (M : CStarMatrix (Fin k) (Fin k) (CStarMatrix (Fin 2) (Fin 2) ℂ)) (hM : 0 ≤ M) :
    0 ≤ M.map (IsCPMap.cstarMap (mix q r)) :=
  (mix_channel hq0 hq1 hr0 hr1).cp.map_cstarMatrix_nonneg k M hM

#print axioms mixKraus_normalized
#print axioms mix_all_auxiliary_positive


def finiteSlope (n : ℕ) : ℝ :=
  ((n : ℝ) - Real.sqrt 2 / Real.sin (Real.pi / (2 * n))) /
    ((n : ℝ) + Real.sqrt 2 / Real.sin (Real.pi / (2 * n)))
def limitingSlope : ℝ := (Real.pi - 2 * Real.sqrt 2) / (Real.pi + 2 * Real.sqrt 2)

lemma angle_pos {n : ℕ} (hn : 2 ≤ n) : 0 < Real.pi / (2 * (n : ℝ)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  positivity

lemma angle_lt_pi {n : ℕ} (hn : 2 ≤ n) : Real.pi / (2 * (n : ℝ)) < Real.pi := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  apply (div_lt_iff₀ (by positivity : 0 < 2 * (n : ℝ))).2
  nlinarith [Real.pi_pos]

/-- 每个有限根层的解析弱噪声斜率严格小于连续极限斜率。 -/
theorem finiteSlope_lt_limit {n : ℕ} (hn : 2 ≤ n) : finiteSlope n < limitingSlope := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs := Real.sin_pos_of_pos_of_lt_pi (angle_pos hn) (angle_lt_pi hn)
  have hsqrt : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hangle := Real.sin_lt (angle_pos hn)
  have hns : 2 * (n : ℝ) * Real.sin (Real.pi / (2 * n)) < Real.pi := by
    nlinarith [(lt_div_iff₀ (by positivity : 0 < 2 * (n : ℝ))).1 hangle]
  have hc : 2 * Real.sqrt 2 * (n : ℝ) <
      Real.pi * (Real.sqrt 2 / Real.sin (Real.pi / (2 * n))) := by
    rw [← mul_div_assoc]
    apply (lt_div_iff₀ hs).2
    nlinarith [mul_lt_mul_of_pos_right hns hsqrt]
  unfold finiteSlope limitingSlope
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
  nlinarith

lemma angle_chord {n : ℕ} (hn : 2 ≤ n) :
    Real.sqrt 2 / (n : ℝ) ≤ Real.sin (Real.pi / (2 * n)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hz0 : 0 ≤ (2 : ℝ) / n := by positivity
  have hz1 : (2 : ℝ) / n ≤ 1 := (div_le_one hn0).2 hnR
  have hc := strictConcaveOn_sin_Icc.concaveOn.2
    (show (0 : ℝ) ∈ Set.Icc 0 Real.pi from ⟨le_rfl, Real.pi_pos.le⟩)
    (show Real.pi / 4 ∈ Set.Icc 0 Real.pi from ⟨by positivity, by linarith [Real.pi_pos]⟩)
    (sub_nonneg.2 hz1) hz0 (by ring : (1 - 2 / (n : ℝ)) + 2 / n = 1)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.sin_zero, Real.sin_pi_div_four] at hc
  have hl : (2 / (n : ℝ)) * (Real.sqrt 2 / 2) = Real.sqrt 2 / n := by field_simp
  have hr : (2 / (n : ℝ)) * (Real.pi / 4) = Real.pi / (2 * n) := by
    field_simp
    norm_num
  simpa only [hl, hr] using hc

lemma finiteSlope_nonneg {n : ℕ} (hn : 2 ≤ n) : 0 ≤ finiteSlope n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs := Real.sin_pos_of_pos_of_lt_pi (angle_pos hn) (angle_lt_pi hn)
  have hc := angle_chord hn
  have hnum : Real.sqrt 2 / Real.sin (Real.pi / (2 * n)) ≤ (n : ℝ) := by
    apply (div_le_iff₀ hs).2
    nlinarith [(div_le_iff₀ hn0).1 hc]
  unfold finiteSlope
  exact div_nonneg (sub_nonneg.2 hnum) (by positivity)

#print axioms finiteSlope_lt_limit
#print axioms finiteSlope_nonneg



/-- 用 sinc 消除 n 趋于无穷时的表面奇点。 -/
def slopeSinc (x : ℝ) : ℝ :=
  (Real.pi * Real.sinc x - 2 * Real.sqrt 2) /
    (Real.pi * Real.sinc x + 2 * Real.sqrt 2)

lemma finiteSlope_eq_sinc {n : ℕ} (hn : 2 ≤ n) :
    finiteSlope n = slopeSinc (Real.pi / (2 * n)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hs := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (angle_pos hn) (angle_lt_pi hn))
  have hp := ne_of_gt (angle_pos hn)
  have hspos := Real.sin_pos_of_pos_of_lt_pi (angle_pos hn) (angle_lt_pi hn)
  have hh : Real.pi * Real.sinc (Real.pi / (2 * (n : ℝ))) =
      2 * (n : ℝ) * Real.sin (Real.pi / (2 * n)) := by
    rw [Real.sinc_of_ne_zero hp]
    field_simp
  unfold finiteSlope slopeSinc
  rw [hh]
  generalize hval : Real.sin (Real.pi / (2 * (n : ℝ))) = s at *
  apply (div_eq_div_iff (by positivity) (by positivity)).2
  field_simp

lemma slopeSinc_continuous_zero : ContinuousAt slopeSinc 0 := by
  unfold slopeSinc
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · simp only [Real.sinc_zero, mul_one]
    positivity

/-- 有限根斜率序列收敛于论文中的连续时间极限常数。 -/
theorem finiteSlope_tendsto : Filter.Tendsto finiteSlope Filter.atTop (nhds limitingSlope) := by
  have hi : Filter.Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hx : Filter.Tendsto (fun n : ℕ => Real.pi / (2 * (n : ℝ))) Filter.atTop (nhds 0) := by
    convert hi.const_mul (Real.pi / 2) using 1 <;>
      simp [div_eq_mul_inv, mul_comm, mul_left_comm]
  have he : ∀ᶠ n : ℕ in Filter.atTop, finiteSlope n = slopeSinc (Real.pi / (2 * n)) := by
    filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    exact finiteSlope_eq_sinc hn
  have h := slopeSinc_continuous_zero.tendsto.comp hx
  have h0 : slopeSinc 0 = limitingSlope := by simp [slopeSinc, limitingSlope]
  rw [h0] at h
  exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm he) h

#print axioms finiteSlope_tendsto





lemma limitingSlope_pos : 0 < limitingSlope := by
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs := Real.sqrt_nonneg (2 : ℝ)
  have hp := Real.pi_gt_three
  unfold limitingSlope
  apply div_pos
  · nlinarith
  · positivity

lemma limitingSlope_lt_one : limitingSlope < 1 := by
  unfold limitingSlope
  apply (div_lt_one (by positivity)).2
  have hs : 0 < Real.sqrt (2 : ℝ) := by positivity
  linarith

lemma finiteSlope_two : finiteSlope 2 = 0 := by
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have he : Real.sqrt (2 : ℝ) / (Real.sqrt 2 / 2) = 2 := by field_simp
  norm_num [finiteSlope, Real.sin_pi_div_four, he]

#print axioms finiteSlope_two
#print axioms limitingSlope_pos



/-- 任意矩阵的单跳算子 GKSL 耗散器，Hamiltonian 取零。 -/
def singleJumpForm (A : M2) : LindbladForm 2 where
  r := 1
  H := 0
  L := fun _ => A
  H_hermitian := by simp

lemma singleJumpForm_apply (A X : M2) :
    (singleJumpForm A).toLinearMap X = dissipator A X := by
  change Complex.I • (X * 0 - 0 * X) + (∑ _ : Fin 1, dissipator A X) = dissipator A X
  simp

lemma singleJump_gksl (A : M2) : IsGKSLGenerator (singleJumpForm A).toLinearMap :=
  (gksl_iff_lindbladForm _).2 ⟨singleJumpForm A, rfl⟩

def rotation (x : ℝ) : M2 :=
  !![(Real.cos x : ℂ), -Complex.I * (Real.sin x : ℂ);
    -Complex.I * (Real.sin x : ℂ), (Real.cos x : ℂ)]

lemma rotation_unitary (x : ℝ) : (rotation x).conjTranspose * rotation x = (1 : M2) := by
  have ht : (Real.cos x : ℂ) ^ 2 + (Real.sin x : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq x
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      -Complex.ofReal_sin, -Complex.ofReal_cos]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq]


lemma sandwich_channel {U : M2} (hU : U.conjTranspose * U = 1) : IsChannel (sandwich U) := by
  have hK : ∀ X, sandwich U X = ∑ i : Fin 1, (fun _ => U) i * X * ((fun _ => U) i).conjTranspose := by
    intro X
    simp [sandwich]
  refine ⟨⟨1, fun _ => U, hK⟩, ?_⟩
  intro X
  rw [hK]
  exact kraus_tp_of_sum_conjTranspose_mul (fun _ : Fin 1 => U) (by simpa using hU) X

lemma channel_comp {T S : M2 →ₗ[ℂ] M2} (hT : IsChannel T) (hS : IsChannel S) :
    IsChannel (T.comp S) := by
  refine ⟨hT.cp.comp hS.cp, ?_⟩
  intro X
  exact (hT.tp (S X)).trans (hS.tp X)

def pauliY : M2 := !![0, -Complex.I; Complex.I, 0]
def pauliZ : M2 := !![1, 0; 0, -1]

/-- 原文 C/R=sin(π/(2n)), S/R=cos(π/(2n)) 的显式跳算子。 -/
def finiteJump (n : ℕ) : M2 := flipMatrix +
  (Complex.I * (Real.sqrt 2 : ℂ)) •
    ((Real.sin (Real.pi / (2 * n)) : ℂ) • pauliY +
      (Real.cos (Real.pi / (2 * n)) : ℂ) • pauliZ)

/-- 原文有限 n 根：酉旋转接单跳算子 GKSL 指数。 -/
def finiteRoot (n : ℕ) (ε : ℝ) : M2 →ₗ[ℂ] M2 :=
  (sandwich (rotation (Real.pi / (2 * n)))).comp
    (expSemigroup (singleJumpForm (finiteJump n)).toLinearMap ε)

/-- 对每个 n 和每个非负噪声参数，该根都是实际 CPTP 通道。 -/
theorem finiteRoot_channel (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) : IsChannel (finiteRoot n ε) :=
  channel_comp (sandwich_channel (rotation_unitary _)) (singleJump_gksl _ ε hε)

/-- 构造族的 n 次作用确实落在定义中的 R_n。 -/
theorem finiteRoot_projection_mem (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    classicalAction ((finiteRoot n ε) ^ n) ∈ rootLayer n :=
  ⟨finiteRoot n ε, finiteRoot_channel n hε, rfl⟩

lemma rotation_add (x y : ℝ) : rotation (x + y) = rotation x * rotation y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq]
  all_goals ring

lemma rotation_zero : rotation 0 = (1 : M2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotation]

lemma rotation_pow (x : ℝ) (n : ℕ) : rotation x ^ n = rotation ((n : ℝ) * x) := by
  induction n with
  | zero => simp [rotation_zero]
  | succ n ih =>
    rw [pow_succ, ih, ← rotation_add]
    congr 1
    push_cast
    ring

lemma sandwich_comp (U V : M2) : (sandwich U).comp (sandwich V) = sandwich (U * V) := by
  ext X i j
  simp [sandwich, Matrix.conjTranspose_mul, Matrix.mul_assoc]

lemma sandwich_pow (U : M2) (n : ℕ) : sandwich U ^ n = sandwich (U ^ n) := by
  induction n with
  | zero => ext X i j; simp [sandwich]
  | succ n ih => rw [pow_succ, pow_succ, ih, Module.End.mul_eq_comp, sandwich_comp]

lemma finiteRoot_zero (n : ℕ) : finiteRoot n 0 = sandwich (rotation (Real.pi / (2 * n))) := by
  simp [finiteRoot, expSemigroup_zero]

/-- 零噪声 n 次作用为经典交换，因而两对角概率均为零。 -/
theorem finiteRoot_zero_projection {n : ℕ} (hn : 0 < n) :
    classicalAction ((finiteRoot n 0) ^ n) = (0, 0) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [finiteRoot_zero, sandwich_pow, rotation_pow]
  have hang : (n : ℝ) * (Real.pi / (2 * n)) = Real.pi / 2 := by field_simp
  rw [hang]
  ext <;> simp [classicalAction, sandwich, rotation, P0, P1,
    Fin.sum_univ_two, Matrix.conjTranspose, Matrix.vecMul, dotProduct,
    Matrix.vecHead, Matrix.vecTail]

#print axioms singleJump_gksl
#print axioms finiteRoot_channel
#print axioms finiteRoot_projection_mem
#print axioms finiteRoot_zero_projection




/-- 每个整数根层都位于真实概率方形中。 -/
theorem rootLayer_subset_square (n : ℕ) : rootLayer n ⊆ probabilitySquare := by
  rintro p ⟨T, hT, rfl⟩
  have hN := channel_pow hT n
  constructor
  · have hD := hN.map_densityMatrices (T ^ n) P0 P0_density
    simpa [classicalAction] using density_diag_bounds hD 0
  · have hD := hN.map_densityMatrices (T ^ n) P1 P1_density
    simpa [classicalAction] using density_diag_bounds hD 1

#print axioms rootLayer_subset_square
end TwoStateRoots
