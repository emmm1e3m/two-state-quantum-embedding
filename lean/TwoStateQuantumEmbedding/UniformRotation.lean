import TwoStateQuantumEmbedding.FirstOrderBridge

noncomputable section
open Matrix Complex NormedSpace
open scoped Matrix.Norms.L2Operator
namespace TwoStateQuantumEmbedding.SwapComparison
open GKSLAlgebra CanonicalBloch GKSLBounds
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

/-- 真实 Bloch 空间中绕 Y 轴的坐标旋转，迹坐标固定。 -/
def axisLinear (a b : ℝ) : AugmentedSpace →ₗ[ℝ] AugmentedSpace where
  toFun x := (x.1, euclid ![a*x.2 0-b*x.2 2, x.2 1, b*x.2 0+a*x.2 2])
  map_add' x y := by
    apply Prod.ext
    · rfl
    · ext i
      fin_cases i <;> simp [euclid] <;> ring
  map_smul' c x := by
    apply Prod.ext
    · rfl
    · ext i
      fin_cases i <;> simp [euclid] <;> ring

def axisCLM (a b : ℝ) : AugmentedSpace →L[ℝ] AugmentedSpace :=
  (axisLinear a b).toContinuousLinearMap

@[simp] theorem axisCLM_apply (a b : ℝ) (x : AugmentedSpace) :
    axisCLM a b x=(x.1, euclid ![a*x.2 0-b*x.2 2, x.2 1, b*x.2 0+a*x.2 2]) := rfl

/-- 单位轴旋转是乘积范数的等距映射。 -/
theorem axisCLM_norm_apply (a b : ℝ) (hab : a^2+b^2=1) (x : AugmentedSpace) :
    ‖axisCLM a b x‖=‖x‖ := by
  have he : ‖euclid ![a*x.2 0-b*x.2 2, x.2 1, b*x.2 0+a*x.2 2]‖^2=‖x.2‖^2 := by
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, euclid]
    linear_combination hab*((x.2 0)^2+(x.2 2)^2)
  have hn : ‖euclid ![a*x.2 0-b*x.2 2, x.2 1, b*x.2 0+a*x.2 2]‖=‖x.2‖ := by
    nlinarith [norm_nonneg (euclid ![a*x.2 0-b*x.2 2, x.2 1, b*x.2 0+a*x.2 2]),
      norm_nonneg x.2]
  simp only [axisCLM_apply, Prod.norm_def, hn]

theorem norm_axisCLM_le (a b : ℝ) (hab : a^2+b^2=1) : ‖axisCLM a b‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [axisCLM_norm_apply a b hab, one_mul]

theorem axisCLM_mul_inverse (a b : ℝ) (hab : a^2+b^2=1) :
    axisCLM a b * axisCLM a (-b)=1 := by
  apply ContinuousLinearMap.ext
  intro x
  apply Prod.ext
  · rfl
  · ext i
    fin_cases i <;> simp [axisCLM_apply, mul_apply_eq_comp, euclid]
    · linear_combination (x.2 0)*hab
    · linear_combination (x.2 2)*hab

/-- 轴偏差估计无频率因子；常数 2 足以给 B2 的 34。 -/
theorem norm_axisCLM_sub_one_le (a b : ℝ) (ha : 0≤a) (hab : a^2+b^2=1) :
    ‖axisCLM a b-1‖≤2*|b| := by
  have ha1 : a≤1 := by nlinarith [sq_nonneg b]
  have hcoef : 0≤1-a ∧ 1-a≤b^2 := by constructor <;> nlinarith
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  let y : R3 := euclid ![(a-1)*x.2 0-b*x.2 2, 0, b*x.2 0+(a-1)*x.2 2]
  have hy : (axisCLM a b-1) x=(0,y) := by
    apply Prod.ext
    · simp
    · ext i
      fin_cases i <;> simp [axisCLM_apply, y, euclid] <;> ring
  have he : ‖y‖^2=2*(1-a)*((x.2 0)^2+(x.2 2)^2) := by
    simp [y, norm_euclid_sq]
    linear_combination ((x.2 0)^2+(x.2 2)^2)*hab
  have hs : (x.2 0)^2+(x.2 2)^2≤‖x.2‖^2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    nlinarith [sq_nonneg (x.2 1)]
  have hsq : ‖y‖^2≤(2*|b| *‖x.2‖)^2 := by
    calc
      ‖y‖^2 = 2*(1-a)*((x.2 0)^2+(x.2 2)^2) := he
      _ ≤ 2*b^2*‖x.2‖^2 := by gcongr; exact hcoef.2
      _ ≤ (2*|b| *‖x.2‖)^2 := by rw [mul_pow, mul_pow, sq_abs]; nlinarith [sq_nonneg b, sq_nonneg ‖x.2‖]
  have hn : ‖y‖≤2*|b| *‖x.2‖ := by
    have hp : 0≤2*|b| * ‖x.2‖ := by positivity
    nlinarith only [hsq, norm_nonneg y, hp]
  rw [hy]
  simp only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg y)]
  exact hn.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity))

@[simp] theorem hamiltonianCLM_xz_apply (a b : ℝ) (x : AugmentedSpace) :
    hamiltonianCLM ![a,0,b] x =
      (0, euclid ![-b*x.2 1, b*x.2 0-a*x.2 2, a*x.2 1]) := by
  change (0, euclid (crossMatrix ![a,0,b] *ᵥ (fun i => x.2 i))+x.1 • (0:R3))=_
  simp only [smul_zero, add_zero]
  apply congrArg (fun y : R3 => ((0:ℝ),y))
  ext i
  fin_cases i <;> simp [euclid, crossMatrix, dotProduct, Fin.sum_univ_succ]
  ring

theorem axisCLM_semiconj_hamiltonian (a b w : ℝ) (hab : a^2+b^2=1) :
    SemiconjBy (axisCLM a b) (hamiltonianCLM ![w,0,0])
      (hamiltonianCLM ![w*a,0,w*b]) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Prod.ext
  · rfl
  · ext i
    fin_cases i <;> simp [mul_apply_eq_comp, axisCLM_apply, hamiltonianCLM_xz_apply, euclid] <;> ring_nf
    linear_combination (w*x.2 2)*hab

/-- 同频率下先旋转轴，再传播，等于真实目标 Hamiltonian 的传播。 -/
theorem exp_hamiltonian_axis_conj (a b w t : ℝ) (hab : a^2+b^2=1) :
    exp (t • hamiltonianCLM ![w*a,0,w*b]) =
      axisCLM a b * exp (t • hamiltonianCLM ![w,0,0]) * axisCLM a (-b) := by
  let : NormedAlgebra ℚ (AugmentedSpace →L[ℝ] AugmentedSpace) := .restrictScalars ℚ ℝ _
  have hs : SemiconjBy (axisCLM a b) (t • hamiltonianCLM ![w,0,0])
      (t • hamiltonianCLM ![w*a,0,w*b]) := by
    apply ContinuousLinearMap.ext
    intro x
    change axisCLM a b (t • (hamiltonianCLM ![w,0,0] x)) =
      t • (hamiltonianCLM ![w*a,0,w*b] (axisCLM a b x))
    rw [map_smul]
    exact congrArg (fun z => t • z)
      (congrArg (fun L : AugmentedSpace →L[ℝ] AugmentedSpace => L x)
        (axisCLM_semiconj_hamiltonian a b w hab))
  have he := hs.exp_right
  change _=_ at he
  rw [he, mul_assoc, axisCLM_mul_inverse a b hab, mul_one]




/-- 轴差产生的传播子误差独立于角度和圈数。 -/
theorem norm_exp_hamiltonian_axis_sub_le (a b w t : ℝ)
    (ha : 0≤a) (hab : a^2+b^2=1) (ht : 0≤t) :
    ‖exp (t • hamiltonianCLM ![w*a,0,w*b])-
      exp (t • hamiltonianCLM ![w,0,0])‖≤4*|b| := by
  rw [exp_hamiltonian_axis_conj a b w t hab]
  let E := exp (t • hamiltonianCLM ![w,0,0])
  have he : ‖E‖≤1 := norm_exp_hamiltonianCLM_le _ ht
  have hi : a^2+(-b)^2=1 := by simpa using hab
  have hdiff : axisCLM a b * E * axisCLM a (-b)-E =
      (axisCLM a b-1)*E*axisCLM a (-b)+E*(axisCLM a (-b)-1) := by
    rw [sub_mul, sub_mul, mul_sub, one_mul, mul_one]
    abel
  change ‖axisCLM a b * E * axisCLM a (-b)-E‖≤_
  rw [hdiff]
  have hleft := norm_axisCLM_sub_one_le a b ha hab
  have hright : ‖axisCLM a (-b)-1‖≤2*|b| := by
    simpa only [abs_neg] using norm_axisCLM_sub_one_le a (-b) ha hi
  calc
    ‖(axisCLM a b-1)*E*axisCLM a (-b)+E*(axisCLM a (-b)-1)‖ ≤
        ‖(axisCLM a b-1)*E*axisCLM a (-b)‖+‖E*(axisCLM a (-b)-1)‖ := norm_add_le _ _
    _ ≤ (‖axisCLM a b-1‖*‖E‖)*‖axisCLM a (-b)‖+‖E‖*‖axisCLM a (-b)-1‖ := by
      exact add_le_add
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
        (norm_mul_le _ _)
    _ ≤ (2*|b| *1)*1+1*(2*|b|) := by
      gcongr
      exact norm_axisCLM_le a (-b) hi
    _ = 4*|b| := by ring

theorem norm_hamiltonianCLM_x_le (w : ℝ) : ‖hamiltonianCLM ![w,0,0]‖≤|w| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg _)
  intro x
  have he : ‖euclid ![0, -w*x.2 2, w*x.2 1]‖^2 =
      w^2*((x.2 1)^2+(x.2 2)^2) := by simp [norm_euclid_sq]; ring
  have hs : (x.2 1)^2+(x.2 2)^2 ≤ ‖x.2‖^2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    nlinarith [sq_nonneg (x.2 0)]
  have hsq : ‖euclid ![0, -w*x.2 2, w*x.2 1]‖^2≤(|w| * ‖x.2‖)^2 := by
    rw [he, mul_pow, sq_abs]
    exact mul_le_mul_of_nonneg_left hs (sq_nonneg _)
  have hn : ‖euclid ![0, -w*x.2 2, w*x.2 1]‖ ≤ |w| * ‖x.2‖ := by
    have hp : 0≤|w| * ‖x.2‖ := by positivity
    nlinarith only [hsq, norm_nonneg (euclid ![0, -w*x.2 2, w*x.2 1]), hp]
  simpa only [hamiltonianCLM_xz_apply, neg_zero, zero_mul, zero_sub, neg_mul,
    Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)] using
    hn.trans (mul_le_mul_of_nonneg_left (le_max_right ‖x.1‖ ‖x.2‖) (abs_nonneg _))

theorem hamiltonianCLM_x_sub (a b : ℝ) :
    hamiltonianCLM ![a,0,0]-hamiltonianCLM ![b,0,0]=hamiltonianCLM ![a-b,0,0] := by
  apply ContinuousLinearMap.ext
  intro x
  apply Prod.ext
  · simp
  · ext i
    fin_cases i <;> simp [hamiltonianCLM_xz_apply, euclid] <;> ring

/-- 同轴实际 Hamiltonian 传播子的频率 Lipschitz 界。 -/
theorem norm_exp_hamiltonian_x_sub_le (a b t : ℝ) (ht : 0≤t) :
    ‖exp (t • hamiltonianCLM ![a,0,0])-exp (t • hamiltonianCLM ![b,0,0])‖≤|a-b| * t := by
  let A := hamiltonianCLM ![b,0,0]
  let B := hamiltonianCLM ![a,0,0]-A
  have hab : A+B=hamiltonianCLM ![a,0,0] := by dsimp [B]; abel
  have h := norm_exp_add_sub_le_of_bounds A B t ht 1 1
    (fun s hs => norm_exp_hamiltonianCLM_le _ hs.1)
    (fun s hs => by rw [hab]; exact norm_exp_hamiltonianCLM_le _ hs.1)
  rw [hab] at h
  simp only [one_mul, mul_one] at h
  have hb : ‖B‖≤|a-b| := by
    dsimp [B,A]
    rw [hamiltonianCLM_x_sub]
    exact norm_hamiltonianCLM_x_le _
  exact h.trans (mul_le_mul_of_nonneg_right hb ht)

/-- 对所有圈数的实际增广传播子比较。 -/
theorem norm_exp_hamiltonian_near_swap (a b θ p t : ℝ) (j : ℕ)
    (ha : 0≤a) (hab : a^2+b^2=1) (_hp : 0≤p)
    (hb : |b|≤Real.sqrt p) (hθ : |θ-Swap.frequency j/2|≤2*Real.sqrt p)
    (ht : t∈Set.Icc (0:ℝ) 1) :
    ‖exp (t • hamiltonianCLM ![2*θ*a,0,2*θ*b])-
      exp (t • hamiltonianCLM ![Swap.frequency j,0,0])‖≤8*Real.sqrt p := by
  have hx := norm_exp_hamiltonian_x_sub_le (2*θ) (Swap.frequency j) t ht.1
  have ha' : |2*θ-Swap.frequency j|≤4*Real.sqrt p := by
    rw [show 2*θ-Swap.frequency j=2*(θ-Swap.frequency j/2) by ring, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith
  calc
    ‖exp (t • hamiltonianCLM ![2*θ*a,0,2*θ*b])-exp (t • hamiltonianCLM ![Swap.frequency j,0,0])‖ ≤
        ‖exp (t • hamiltonianCLM ![2*θ*a,0,2*θ*b])-exp (t • hamiltonianCLM ![2*θ,0,0])‖+
        ‖exp (t • hamiltonianCLM ![2*θ,0,0])-exp (t • hamiltonianCLM ![Swap.frequency j,0,0])‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 4*|b| + |2*θ-Swap.frequency j| * t := add_le_add
      (norm_exp_hamiltonian_axis_sub_le a b (2*θ) t ha hab ht.1) hx
    _ ≤ 4*Real.sqrt p + (4*Real.sqrt p)*1 := by
      gcongr <;> first | exact ht.1 | exact ht.2
    _ = 8*Real.sqrt p := by ring

#print axioms exp_hamiltonian_axis_conj
#print axioms norm_exp_hamiltonian_near_swap
end TwoStateQuantumEmbedding.SwapComparison


