import TwoStateQuantumEmbedding.FirstOrderBridge
import TwoStateQuantumEmbedding.HamiltonianHessian
import TwoStateQuantumEmbedding.CanonicalRigidity

noncomputable section
open Matrix Complex NormedSpace
open scoped Matrix.Norms.L2Operator ComplexOrder
namespace TwoStateQuantumEmbedding.SwapComparison
open GKSLAlgebra CanonicalBloch GKSLBounds
set_option maxHeartbeats 1000000

/-- 078 的共同纯 Hamiltonian 概率就是同一个实际 canonicalOutput。 -/
theorem unitaryProbability_eq_output (h : BlochVec) (t : ℝ) :
    unitaryProbability h t=(canonicalOutput h 0 t).1 := by
  simp [unitaryProbability, canonicalOutput, canonicalEvolution_zero_drift_column]

theorem unitaryProbability_nonneg (h : BlochVec) {t : ℝ} (ht : 0≤t) :
    0≤unitaryProbability h t := by
  rw [unitaryProbability_eq_output]
  exact (Q2_subset_unitSquare (canonicalOutput_mem_Q2 h 0 (Matrix.PosSemidef.zero) t ht)).1.1

@[simp] theorem unitaryProbability_zero (t : ℝ) : unitaryProbability 0 t=1 := by
  have hz : (![0,0,0] : BlochVec)=0 := by ext i; fin_cases i <;> rfl
  rw [unitaryProbability_eq_output, ← hz, canonicalOutput_x_zero]
  simp
/-- 精确正规化后的实际纯 Hamiltonian 生存概率。 -/
theorem unitaryProbability_normalized (a b θ : ℝ) (hab : a^2+b^2=1) (hθ : 0<θ) :
    unitaryProbability ![2*θ*a,0,2*θ*b] 1=unitarySurvival θ b := by
  have hr : HamiltonianHessian.radius (2*θ*a) (θ*b)=θ := by
    unfold HamiltonianHessian.radius
    rw [show ((2*θ*a)/2)^2+(θ*b)^2=θ^2 by nlinarith [congrArg (fun x => θ^2*x) hab]]
    exact Real.sqrt_sq hθ.le
  rw [unitaryProbability_eq_output]
  have hout := HamiltonianHessian.canonicalOutput_formula (2*θ*a) (θ*b) (by rw [hr]; exact hθ)
  rw [show 2*θ*b=2*(θ*b) by ring, hout]
  simp only [HamiltonianHessian.probability, hr, unitarySurvival]
  field_simp

/-- 实际概率逼近交换就强制 Hamiltonian 非零，并给出所有圈数的参考选择。 -/
theorem normalized_swap_reference (hx hz : ℝ) (hxpos : 0≤hx)
    (hp : unitaryProbability ![hx,0,hz] 1<1) :
    ∃ (a b θ : ℝ) (j : ℕ),
      θ=Real.sqrt (hx^2+hz^2)/2 ∧ 0<θ ∧ 0≤a ∧ a^2+b^2=1 ∧
      ![hx,0,hz]=![2*θ*a,0,2*θ*b] ∧
      |b|≤Real.sqrt (unitaryProbability ![hx,0,hz] 1) ∧
      |θ-Swap.frequency j/2|≤2*Real.sqrt (unitaryProbability ![hx,0,hz] 1) ∧
      |hz|≤2*θ*Real.sqrt (unitaryProbability ![hx,0,hz] 1) := by
  let r := Real.sqrt (hx^2+hz^2)
  have hr2 : r^2=hx^2+hz^2 := Real.sq_sqrt (by positivity)
  have hr : 0<r := by
    have hn : 0≤r := Real.sqrt_nonneg _
    by_contra h
    have hz0 : r=0 := by linarith
    have hx0 : hx=0 := by nlinarith [sq_nonneg hz]
    have hh0 : hz=0 := by nlinarith [sq_nonneg hx]
    have hv : (![hx,0,hz] : BlochVec)=0 := by simp [hx0,hh0]
    rw [hv, unitaryProbability_zero] at hp
    linarith
  let a := hx/r
  let b := hz/r
  let θ := r/2
  have ha : 0≤a := div_nonneg hxpos hr.le
  have ht : 0<θ := by dsimp [θ]; positivity
  have hab : a^2+b^2=1 := by
    dsimp [a,b]
    field_simp
    nlinarith only [hr2]
  have hh : (![hx,0,hz] : BlochVec)=![2*θ*a,0,2*θ*b] := by
    dsimp [a,b,θ]
    ext i
    fin_cases i <;> simp <;> field_simp
  have he : unitaryProbability ![hx,0,hz] 1=unitarySurvival θ b := by
    rw [hh]
    exact unitaryProbability_normalized a b θ hab ht
  have hp0 := unitaryProbability_nonneg ![hx,0,hz] (t:=1) (by norm_num)
  have hb2 : b^2≤unitaryProbability ![hx,0,hz] 1 := by
    rw [he]
    exact axis_sq_le_survival θ b (by nlinarith [sq_nonneg a])
  have hb : |b|≤Real.sqrt (unitaryProbability ![hx,0,hz] 1) := by
    have hs := Real.sq_sqrt hp0
    nlinarith [Real.sqrt_nonneg (unitaryProbability ![hx,0,hz] 1), sq_abs b, abs_nonneg b]
  obtain ⟨j,hj⟩ := exists_winding_close θ (unitaryProbability ![hx,0,hz] 1) ht.le hp0
    (by rw [he]; exact cos_sq_le_survival θ b)
  refine ⟨a,b,θ,j,rfl,ht,ha,hab,hh,hb,hj,?_⟩
  have hzid : hz=2*θ*b := congrFun hh 2
  calc
    |hz| = 2*θ*|b| := by rw [hzid, abs_mul, abs_of_pos (by positivity : 0<2*θ)]
    _ ≤ 2*θ*Real.sqrt (unitaryProbability ![hx,0,hz] 1) :=
      mul_le_mul_of_nonneg_left hb (by positivity)

/-- B1 与真实 4d 概率估计给出统一 p≤35s/3。 -/
theorem unitaryProbability_le_small_sum (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ)
    (hK : K.PosSemidef) (s : ℝ)
    (hsread : s=(canonicalOutput h K 1).1+(canonicalOutput h K 1).2) (hs : s≤1/16) :
    unitaryProbability h 1≤(35/3)*s := by
  have hr := Rigidity.canonicalOutput_dissipative_rigidity h K hK s hsread hs
  have hd : dissipationSize K≤(8/3)*s := by
    have ht : dissipationSize K=K.trace.re := by simp [dissipationSize, Matrix.trace, Complex.re_sum]
    rw [ht]
    exact hr.1.trans hr.2
  have hb := (Q2_subset_unitSquare (canonicalOutput_mem_Q2 h K hK 1 (by norm_num))).2.1
  have he := (canonicalOutput_perturbation_common_le h K hK (t:=1) (by norm_num)).1
  have hh := (abs_le.mp he).1
  simp only [mul_one] at hh
  linarith

#print axioms normalized_swap_reference
#print axioms unitaryProbability_le_small_sum
end TwoStateQuantumEmbedding.SwapComparison



