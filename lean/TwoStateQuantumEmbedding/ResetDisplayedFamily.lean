import TwoStateQuantumEmbedding.ResetUniform

noncomputable section
open Matrix Complex Filter Topology
open scoped ComplexOrder
open TwoStateQuantumEmbedding.ResetFamily

namespace TwoStateQuantumEmbedding.ResetDisplayedFamily

/-- 不限制总衰减率的相干本征模。 -/
theorem triangular_coherence_general (m n : ℝ) :
    dissipator (triangularJump m n) coherence =
      (- ((m ^ 2 + n ^ 2) / 2 : ℂ)) • coherence := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [dissipator, triangularJump, coherence, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Matrix.vecMul, dotProduct] <;> ring

/-- 不限制总衰减率的人口本征模。 -/
theorem triangular_fast_general (m n k : ℝ) (hk : k = n ^ 2 - m ^ 2) :
    dissipator (triangularJump m n)
        ((k : ℂ) • (excited - ground) + (2 * m * n : ℂ) • coherence) =
      (-(n ^ 2 : ℂ)) •
        ((k : ℂ) • (excited - ground) + (2 * m * n : ℂ) • coherence) := by
  have hkC : (k : ℂ) = (n : ℂ) ^ 2 - (m : ℂ) ^ 2 := by exact_mod_cast hk
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [dissipator, triangularJump, excited, ground, coherence, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.vecMul, dotProduct] <;>
    rw [hkC] <;> ring

theorem coherence_eigen_general (c s m n : ℝ) (hc : c ^ 2 + s ^ 2 = 1) :
    gkslAction 0 (jumps c s m n) (coherenceMode c s) =
      (- ((m ^ 2 + n ^ 2) / 2 : ℂ)) • coherenceMode c s := by
  simp only [gkslAction, zero_mul, mul_zero, sub_self, smul_zero,
    zero_add, jumps, Fin.sum_univ_one, jump, coherenceMode]
  rw [dissipator_conjugate _ _ _ (rotation_unitary c s hc).1,
    triangular_coherence_general]
  simp only [conjugate, Matrix.mul_smul, Matrix.smul_mul]

theorem fast_eigen_general (c s m n k : ℝ) (hc : c ^ 2 + s ^ 2 = 1)
    (hk : k = n ^ 2 - m ^ 2) :
    gkslAction 0 (jumps c s m n) (fastMode c s m n k) =
      (-(n ^ 2 : ℂ)) • fastMode c s m n k := by
  simp only [gkslAction, zero_mul, mul_zero, sub_self, smul_zero,
    zero_add, jumps, Fin.sum_univ_one, jump, fastMode]
  rw [dissipator_conjugate _ _ _ (rotation_unitary c s hc).1,
    triangular_fast_general m n k hk]
  simp only [conjugate, Matrix.mul_smul, Matrix.smul_mul]

theorem evolution_modes_general (c s m n k t : ℝ) (hc : c ^ 2 + s ^ 2 = 1)
    (hk : k = n ^ 2 - m ^ 2) :
    gkslSuperoperatorEvolution 0 (jumps c s m n) t (groundMode c s) = groundMode c s ∧
    gkslSuperoperatorEvolution 0 (jumps c s m n) t (coherenceMode c s) =
      (Real.exp (-(m ^ 2 + n ^ 2) * t / 2) : ℂ) • coherenceMode c s ∧
    gkslSuperoperatorEvolution 0 (jumps c s m n) t (fastMode c s m n k) =
      (Real.exp (-n ^ 2 * t) : ℂ) • fastMode c s m n k := by
  constructor
  · have h := evolution_eigen 0 (jumps c s m n) t (groundMode c s) 0
      (by simpa using ground_eigen c s m n hc)
    simpa using h
  constructor
  · have h := evolution_eigen 0 (jumps c s m n) t (coherenceMode c s)
      (- ((m ^ 2 + n ^ 2) / 2 : ℂ)) (coherence_eigen_general c s m n hc)
    convert h using 1
    congr 1
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  · have h := evolution_eigen 0 (jumps c s m n) t (fastMode c s m n k)
      (-(n ^ 2 : ℂ)) (fast_eigen_general c s m n k hc hk)
    convert h using 1
    congr 1
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring

def epsilonGeneral (c s m n k t : ℝ) : ℝ :=
  s ^ 2 * (1 - (1 + bCoefficient c s m n k) * Real.exp (-(m ^ 2 + n ^ 2) * t / 2) +
    bCoefficient c s m n k * Real.exp (-n ^ 2 * t))
def aGeneral (c s m n k t : ℝ) : ℝ :=
  epsilonGeneral c s m n k t + (c ^ 2 - s ^ 2) * bCoefficient c s m n k *
    Real.exp (-n ^ 2 * t) -
    ((c ^ 2 - s ^ 2) * bCoefficient c s m n k - 1) *
      Real.exp (-(m ^ 2 + n ^ 2) * t / 2)

/-- 任意三角单跳跃的精确有限输出，直接复用已证输入分解及指数本征模。 -/
theorem finiteOutput_general (c s m n k t : ℝ) (hc : c ^ 2 + s ^ 2 = 1)
    (hk : k = n ^ 2 - m ^ 2) (hk0 : k ≠ 0) :
    finiteOutput 0 (jumps c s m n) t =
      (aGeneral c s m n k t, 1 - epsilonGeneral c s m n k t) := by
  obtain ⟨hG, hW, hF⟩ := evolution_modes_general c s m n k t hc hk
  rw [finiteOutput_eq_superoperator_probabilities,
    input_zero_decomposition c s m n k hc hk0, input_one_decomposition c s m n k hc hk0]
  simp only [map_add, map_smul, hG, hW, hF]
  unfold aGeneral epsilonGeneral
  generalize Real.exp (-(m ^ 2 + n ^ 2) * t / 2) = S
  generalize Real.exp (-n ^ 2 * t) = F
  apply Prod.ext <;>
    simp [bCoefficient, groundMode, coherenceMode, fastMode,
      conjugate, rotation, ground, excited, coherence,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Complex.mul_re, Complex.mul_im, pow_two] <;> field_simp
  · linear_combination k * S * (c ^ 2 + 1) * hc
  · linear_combination (k + S * k * s ^ 2) * hc

def fastKernel (n t : ℝ) : ℝ := Real.exp (-n ^ 2 * t)
def slowKernel (m n t : ℝ) : ℝ := Real.exp (-(m ^ 2 + n ^ 2) * t / 2)
def crossKernel (m n t : ℝ) : ℝ :=
  2 * m * n / (n ^ 2 - m ^ 2) * (slowKernel m n t - fastKernel n t)
def populationDifference (c s : ℝ) : ℝ := c ^ 2 - s ^ 2
def coherenceDifference (c s : ℝ) : ℝ := 2 * c * s
def epsilonKernel (c s m n t : ℝ) : ℝ :=
  s ^ 2 + populationDifference c s * s ^ 2 * fastKernel n t -
    coherenceDifference c s ^ 2 / 2 * slowKernel m n t -
    s ^ 2 * coherenceDifference c s * crossKernel m n t
def qKernel (c s m n t : ℝ) : ℝ :=
  populationDifference c s ^ 2 * fastKernel n t +
    coherenceDifference c s ^ 2 * slowKernel m n t -
    populationDifference c s * coherenceDifference c s * crossKernel m n t

theorem epsilon_kernel_identity (c s m n k F S : ℝ)
    (hc : c ^ 2 + s ^ 2 = 1) (hk : k ≠ 0) :
    s ^ 2 * (1 - (1 + bCoefficient c s m n k) * S + bCoefficient c s m n k * F) =
      s ^ 2 + (c ^ 2 - s ^ 2) * s ^ 2 * F - (2 * c * s) ^ 2 / 2 * S -
        s ^ 2 * (2 * c * s) * (2 * m * n / k * (S - F)) := by
  unfold bCoefficient
  field_simp
  linear_combination k * s ^ 2 * S * hc

theorem q_kernel_identity (c s m n k F S : ℝ)
    (hc : c ^ 2 + s ^ 2 = 1) (hk : k ≠ 0) :
    (c ^ 2 - s ^ 2) * bCoefficient c s m n k * F -
        ((c ^ 2 - s ^ 2) * bCoefficient c s m n k - 1) * S =
      (c ^ 2 - s ^ 2) ^ 2 * F + (2 * c * s) ^ 2 * S -
        (c ^ 2 - s ^ 2) * (2 * c * s) * (2 * m * n / k * (S - F)) := by
  unfold bCoefficient
  field_simp
  linear_combination -k * S * (c ^ 2 + s ^ 2 + 1) * hc

/-- 稿件 q 和实际 ε 的核公式，尚未对 L 作渐近换元。 -/
theorem finiteOutput_kernel (c s m n t : ℝ) (hc : c ^ 2 + s ^ 2 = 1)
    (hk : n ^ 2 - m ^ 2 ≠ 0) :
    finiteOutput 0 (jumps c s m n) t =
      (epsilonKernel c s m n t + qKernel c s m n t, 1 - epsilonKernel c s m n t) := by
  have hε : epsilonGeneral c s m n (n ^ 2 - m ^ 2) t = epsilonKernel c s m n t :=
    epsilon_kernel_identity c s m n (n ^ 2 - m ^ 2) (fastKernel n t)
      (slowKernel m n t) hc hk
  have hq := q_kernel_identity c s m n (n ^ 2 - m ^ 2) (fastKernel n t)
    (slowKernel m n t) hc hk
  rw [finiteOutput_general c s m n (n ^ 2 - m ^ 2) t hc rfl hk]
  apply Prod.ext
  · change epsilonGeneral c s m n (n ^ 2 - m ^ 2) t +
        (c ^ 2 - s ^ 2) * bCoefficient c s m n (n ^ 2 - m ^ 2) * fastKernel n t -
          ((c ^ 2 - s ^ 2) * bCoefficient c s m n (n ^ 2 - m ^ 2) - 1) *
            slowKernel m n t = _
    rw [hε]
    dsimp only [qKernel, populationDifference, coherenceDifference, crossKernel]
    linear_combination hq
  · exact congrArg (fun x => 1 - x) hε

def v (p : ℝ) : ℝ := 1 - 2 * p
def w (p : ℝ) : ℝ := 2 * Real.sqrt (p * (1 - p))
def F (A : ℝ) : ℝ := Real.exp (-A)
def S (A B : ℝ) : ℝ := Real.exp (-(A + B) / 2)
def K (A B : ℝ) : ℝ := Real.sqrt (A * B) / (A - (A + B) / 2) * (S A B - F A)
def actualError (p A B : ℝ) : ℝ :=
  p + v p * p * F A - w p ^ 2 / 2 * S A B - p * w p * K A B
def determinant (p A B : ℝ) : ℝ :=
  v p ^ 2 * F A + w p ^ 2 * S A B - v p * w p * K A B
def simpleJumps (p A B : ℝ) : Fin 1 → QubitMatrix :=
  jumps (Real.sqrt (1 - p)) (Real.sqrt p) (Real.sqrt B) (Real.sqrt A)

/-- 稿件显示的实际单跳跃在任意非简并正参数处满足 q 与实际 ε 公式。 -/
theorem simple_output_exact (p A B : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hne : A - B ≠ 0) :
    finiteOutput 0 (simpleJumps p A B) 1 =
      (actualError p A B + determinant p A B, 1 - actualError p A B) := by
  have hc : Real.sqrt (1 - p) ^ 2 + Real.sqrt p ^ 2 = 1 := by
    rw [Real.sq_sqrt (by linarith [hp.2] : 0 ≤ 1 - p), Real.sq_sqrt hp.1]
    ring
  have hv : populationDifference (Real.sqrt (1 - p)) (Real.sqrt p) = v p := by
    simp only [populationDifference, Real.sq_sqrt (by linarith [hp.2] : 0 ≤ 1 - p),
      Real.sq_sqrt hp.1, v]
    ring
  have hw : coherenceDifference (Real.sqrt (1 - p)) (Real.sqrt p) = w p := by
    rw [coherenceDifference, w, Real.sqrt_mul hp.1]
    ring
  have hf : fastKernel (Real.sqrt A) 1 = F A := by
    simp only [fastKernel, F, Real.sq_sqrt hA, mul_one]
  have hs : slowKernel (Real.sqrt B) (Real.sqrt A) 1 = S A B := by
    simp only [slowKernel, S, Real.sq_sqrt hA, Real.sq_sqrt hB, mul_one, add_comm B A]
  have hk : crossKernel (Real.sqrt B) (Real.sqrt A) 1 = K A B := by
    have hd : A - (A + B) / 2 ≠ 0 := by intro h; apply hne; linarith
    rw [crossKernel, Real.sq_sqrt hA, Real.sq_sqrt hB, hs, hf, K,
      Real.sqrt_mul hA]
    rw [show A - (A + B) / 2 = (A - B) / 2 by ring]
    field_simp [hne]
  have hε : epsilonKernel (Real.sqrt (1 - p)) (Real.sqrt p)
      (Real.sqrt B) (Real.sqrt A) 1 = actualError p A B := by
    simp only [epsilonKernel, Real.sq_sqrt hp.1, hv, hw, hf, hs, hk, actualError]
  have hq : qKernel (Real.sqrt (1 - p)) (Real.sqrt p)
      (Real.sqrt B) (Real.sqrt A) 1 = determinant p A B := by
    simp only [qKernel, hv, hw, hf, hs, hk, determinant]
  exact (finiteOutput_kernel _ _ _ _ _ hc
    (by simpa only [Real.sq_sqrt hA, Real.sq_sqrt hB] using hne)).trans
    (by rw [hε, hq])

def pFamily (L : ℝ) : ℝ := Real.exp (-L)
def AFamily (L : ℝ) : ℝ := L + Real.log L + 1 - Real.log 4
def BFamily (L : ℝ) : ℝ := AFamily L / L
def displayedJumps (L : ℝ) : Fin 1 → QubitMatrix :=
  simpleJumps (pFamily L) (AFamily L) (BFamily L)
def displayedError (L : ℝ) : ℝ := actualError (pFamily L) (AFamily L) (BFamily L)
def displayedDeterminant (L : ℝ) : ℝ := determinant (pFamily L) (AFamily L) (BFamily L)

theorem displayed_parameters (L : ℝ) (hL : 4 < L) :
    pFamily L ∈ Set.Icc (0 : ℝ) 1 ∧ 0 < AFamily L ∧ 0 < BFamily L ∧
      AFamily L - BFamily L ≠ 0 := by
  have hL0 : 0 < L := by linarith
  have ha : 0 < AFamily L := by
    have hl := Real.log_pos (show 1 < L by linarith)
    have h4 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    unfold AFamily
    linarith
  have hb : 0 < BFamily L := div_pos ha hL0
  have hba : BFamily L < AFamily L := by
    exact (div_lt_self ha (by linarith)).trans_le le_rfl
  exact ⟨⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith)⟩,
    ha, hb, (sub_pos.mpr hba).ne'⟩

/-- 新稿显示参数族的有限时间输出，使用真实测量误差。 -/
theorem displayed_output_exact (L : ℝ) (hL : 4 < L) :
    finiteOutput 0 (displayedJumps L) 1 =
      (displayedError L + displayedDeterminant L, 1 - displayedError L) := by
  obtain ⟨hp, hA, hB, hne⟩ := displayed_parameters L hL
  exact simple_output_exact _ _ _ hp hA.le hB.le hne

theorem displayed_output_is_finite (L : ℝ) :
    finiteOutput 0 (displayedJumps L) 1 ∈ finiteOutputs :=
  ⟨1, 0, displayedJumps L, 1, by simp, by norm_num, rfl⟩

/-- 显示族的快核恒等式 F=4p/(eL)，无渐近误差。 -/
theorem displayed_fast_exact (L : ℝ) (hL : 0 < L) :
    F (AFamily L) = 4 * pFamily L / (Real.exp 1 * L) := by
  unfold F AFamily pFamily
  rw [show -(L + Real.log L + 1 - Real.log 4) = Real.log 4 - 1 - Real.log L - L by ring]
  simp only [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 4),
    Real.exp_log hL, Real.exp_neg]
  ring

theorem displayed_error_continuousAt (L : ℝ) (hL : 4 < L) :
    ContinuousAt displayedError L := by
  obtain ⟨hp, hA, hB, hne⟩ := displayed_parameters L hL
  have hL0 : L ≠ 0 := by linarith
  have hd : AFamily L - (AFamily L + BFamily L) / 2 ≠ 0 := by
    intro h; apply hne; linarith
  have hpcont : ContinuousAt pFamily L := by unfold pFamily; fun_prop
  have ha : ContinuousAt AFamily L := by unfold AFamily; fun_prop (disch := assumption)
  have hb : ContinuousAt BFamily L := ha.div continuousAt_id hL0
  unfold displayedError actualError v w K S F
  fun_prop (disch := assumption)

theorem displayed_pure_stationary (L : ℝ) (hL : 4 < L) :
    ∃ ρ : QubitMatrix, ρ.PosSemidef ∧ Matrix.trace ρ = 1 ∧ ρ * ρ = ρ ∧
      gkslAction 0 (displayedJumps L) ρ = 0 := by
  have hp := (displayed_parameters L hL).1
  have hc : Real.sqrt (1 - pFamily L) ^ 2 + Real.sqrt (pFamily L) ^ 2 = 1 := by
    rw [Real.sq_sqrt (by linarith [hp.2] : 0 ≤ 1 - pFamily L), Real.sq_sqrt hp.1]
    ring
  have hg := groundMode_is_pure_density _ _ hc
  refine ⟨groundMode (Real.sqrt (1 - pFamily L)) (Real.sqrt (pFamily L)),
    hg.1, hg.2.1, hg.2.2, ?_⟩
  exact ground_eigen _ _ _ _ hc

end TwoStateQuantumEmbedding.ResetDisplayedFamily

#print axioms TwoStateQuantumEmbedding.ResetDisplayedFamily.finiteOutput_general
#print axioms TwoStateQuantumEmbedding.ResetDisplayedFamily.finiteOutput_kernel
#print axioms TwoStateQuantumEmbedding.ResetDisplayedFamily.simple_output_exact
#print axioms TwoStateQuantumEmbedding.ResetDisplayedFamily.displayed_output_exact
#print axioms TwoStateQuantumEmbedding.ResetDisplayedFamily.displayed_output_is_finite
#print axioms TwoStateQuantumEmbedding.ResetDisplayedFamily.displayed_fast_exact
#print axioms TwoStateQuantumEmbedding.ResetDisplayedFamily.displayed_error_continuousAt
#print axioms TwoStateQuantumEmbedding.ResetDisplayedFamily.displayed_pure_stationary
