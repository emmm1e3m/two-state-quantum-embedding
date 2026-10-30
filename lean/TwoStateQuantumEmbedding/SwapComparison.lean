import TwoStateQuantumEmbedding.GKSLAlgebra
import TwoStateQuantumEmbedding.SwapCore
import TwoStateQuantumEmbedding.Duhamel
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Order.Floor.Semiring
noncomputable section

open Matrix Complex NormedSpace MeasureTheory
open scoped Interval Matrix.Norms.Operator

namespace TwoStateQuantumEmbedding.SwapComparison
open GKSLAlgebra

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-- 由实际指数导数证明平方为 -1 的旋转公式。 -/
theorem exp_of_square_neg_one {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] (J : A) (hJ : J*J = -1) (t : ℝ) :
    exp (t • J) = Real.cos t • (1:A) + Real.sin t • J := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  let f : ℝ → A := fun r => Real.cos r • (1:A) + Real.sin r • J
  have hf (r : ℝ) : HasDerivAt f (f r * J) r := by
    convert ((Real.hasDerivAt_cos r).smul_const (1:A)).add
      ((Real.hasDerivAt_sin r).smul_const J) using 1
    simp [f, add_mul, smul_mul_assoc, hJ]
    module
  have hg (r : ℝ) : HasDerivAt (fun s => f s * exp ((-s) • J)) 0 r := by
    have he : HasDerivAt (fun s : ℝ => exp ((-s) • J))
        (-(J*exp ((-r) • J))) r := by
      simpa [Function.comp_def] using
        (hasDerivAt_exp_smul_const' J (-r)).scomp r ((hasDerivAt_id r).neg)
    convert (hf r).mul he using 1
    noncomm_ring
  have hc := is_const_of_deriv_eq_zero (fun r => (hg r).differentiableAt)
    (fun r => (hg r).deriv) t 0
  have hc' : f t * exp (-(t • J)) = 1 := by simpa [f] using hc
  have hi : exp (-(t • J)) * exp (t • J) = 1 := by
    rw [← NormedSpace.exp_add_of_commute (Commute.refl (t • J)).neg_left, neg_add_cancel, NormedSpace.exp_zero]
  have h := congrArg (fun a : A => a * exp (t • J)) hc'
  simpa [mul_assoc, hi, f] using h.symm

/-- 一般实际 Pauli Hamiltonian 的平方，不预设轴归一化。 -/
theorem realPauli_square (n : BlochVec) :
    realPauli n * realPauli n =
      (((n 0)^2+(n 1)^2+(n 2)^2 : ℝ) : ℂ) • (1 : QubitMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [realPauli, pauli, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply, smul_eq_mul, pow_two, Complex.mul_re, Complex.mul_im] <;> ring

def pauliUnitary (n : BlochVec) (angle t : ℝ) : QubitMatrix :=
  exp ((angle*t) • ((-Complex.I) • realPauli n))

/-- 此闭式等于真正的 NormedSpace.exp，不是替代定义。 -/
theorem pauliUnitary_formula (n : BlochVec)
    (hn : (n 0)^2+(n 1)^2+(n 2)^2=1) (angle t : ℝ) :
    pauliUnitary n angle t =
      Real.cos (angle*t) • (1:QubitMatrix) +
        Real.sin (angle*t) • ((-Complex.I) • realPauli n) := by
  unfold pauliUnitary
  apply exp_of_square_neg_one
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, realPauli_square, hn]
  simp [smul_smul, Complex.I_sq]

#print axioms exp_of_square_neg_one
#print axioms pauliUnitary_formula
end TwoStateQuantumEmbedding.SwapComparison

open Complex MeasureTheory
open scoped Interval
namespace TwoStateQuantumEmbedding.SwapComparison

set_option maxHeartbeats 800000

theorem sin_frequency (j : ℕ) : Real.sin (Swap.frequency j) = 0 := by
  have h : Swap.frequency j = ((2*j+1 : ℕ) : ℝ)*Real.pi := by
    simp [Swap.frequency, Nat.cast_add, Nat.cast_mul]
  rw [h, Real.sin_nat_mul_pi]

theorem cos_frequency (j : ℕ) : Real.cos (Swap.frequency j) = -1 := by
  have h : Swap.frequency j = (j:ℝ)*(2*Real.pi)+Real.pi := by unfold Swap.frequency; ring
  rw [h, Real.cos_nat_mul_two_pi_add_pi]

theorem integral_frequency_sin (j : ℕ) :
    (∫ t in (0:ℝ)..1, Real.sin (Swap.frequency j*t)) = 2 / Swap.frequency j := by
  rw [intervalIntegral.integral_comp_mul_left Real.sin (ne_of_gt (Swap.frequency_pos j))]
  simp [integral_sin, cos_frequency]
  ring

theorem integral_frequency_cos (j : ℕ) :
    (∫ t in (0:ℝ)..1, Real.cos (Swap.frequency j*t)) = 0 := by
  rw [intervalIntegral.integral_comp_mul_left Real.cos (ne_of_gt (Swap.frequency_pos j))]
  simp [integral_cos, sin_frequency]

theorem integral_frequency_sin_sq (j : ℕ) :
    (∫ t in (0:ℝ)..1, (Real.sin (Swap.frequency j*t))^2) = 1/2 := by
  rw [intervalIntegral.integral_comp_mul_left (fun x => (Real.sin x)^2)
    (ne_of_gt (Swap.frequency_pos j))]
  simp [integral_sin_sq, sin_frequency]
  field_simp [ne_of_gt (Swap.frequency_pos j)]

theorem integral_frequency_cos_sq (j : ℕ) :
    (∫ t in (0:ℝ)..1, (Real.cos (Swap.frequency j*t))^2) = 1/2 := by
  rw [intervalIntegral.integral_comp_mul_left (fun x => (Real.cos x)^2)
    (ne_of_gt (Swap.frequency_pos j))]
  simp [integral_cos_sq, sin_frequency]
  field_simp [ne_of_gt (Swap.frequency_pos j)]

theorem integral_frequency_sin_cos (j : ℕ) :
    (∫ t in (0:ℝ)..1, Real.sin (Swap.frequency j*t)*Real.cos (Swap.frequency j*t)) = 0 := by
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.sin x*Real.cos x)
    (ne_of_gt (Swap.frequency_pos j))]
  simp [integral_sin_mul_cos₁, sin_frequency]

def referenceAmplitude (sign : ℝ) (j : ℕ) (v : Fin 3 → ℂ) (t : ℝ) : ℂ :=
  v 0 + (sign : ℂ)*I*(v 1*(Real.cos (Swap.frequency j*t) : ℂ) +
    v 2*(Real.sin (Swap.frequency j*t) : ℂ))

def crossImag (x y : ℂ) : ℝ := ((starRingEnd ℂ) x*y).im
def crossReal (x y : ℂ) : ℝ := ((starRingEnd ℂ) x*y).re

/-- 实际参考幅度的模平方展开，保留任意复跳跃的全部相位项。 -/
theorem amplitude_square (sign : ℝ) (hs : sign^2=1) (j : ℕ) (v : Fin 3 → ℂ) (t : ℝ) :
    normSq (referenceAmplitude sign j v t) =
      normSq (v 0) + normSq (v 1)*(Real.cos (Swap.frequency j*t))^2 +
      normSq (v 2)*(Real.sin (Swap.frequency j*t))^2 +
      2*crossReal (v 1) (v 2)*Real.sin (Swap.frequency j*t)*Real.cos (Swap.frequency j*t) -
      2*sign*crossImag (v 0) (v 1)*Real.cos (Swap.frequency j*t) -
      2*sign*crossImag (v 0) (v 2)*Real.sin (Swap.frequency j*t) := by
  simp only [referenceAmplitude, normSq_apply, crossReal, crossImag,
    add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, conj_re, conj_im]
  ring_nf
  rw [hs]
  ring

theorem integral_reference_amplitude (sign : ℝ) (hs : sign^2=1) (j : ℕ) (v : Fin 3 → ℂ) :
    (∫ t in (0:ℝ)..1, normSq (referenceAmplitude sign j v t)) =
      Swap.energy v-sign*(4/Swap.frequency j)*Swap.cross v := by
  have heq : (fun t => normSq (referenceAmplitude sign j v t)) =
      (fun t => normSq (v 0) + normSq (v 1)*(Real.cos (Swap.frequency j*t))^2 +
      normSq (v 2)*(Real.sin (Swap.frequency j*t))^2 +
      (2*crossReal (v 1) (v 2))*(Real.sin (Swap.frequency j*t)*Real.cos (Swap.frequency j*t)) -
      (2*sign*crossImag (v 0) (v 1))*Real.cos (Swap.frequency j*t) -
      (2*sign*crossImag (v 0) (v 2))*Real.sin (Swap.frequency j*t)) := by
    funext t
    rw [amplitude_square sign hs]
    ring
  rw [heq]
  simp (disch := (apply Continuous.intervalIntegrable; fun_prop)) only
    [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
      integral_frequency_cos_sq, integral_frequency_sin_sq, integral_frequency_sin_cos,
      integral_frequency_cos, integral_frequency_sin]
  unfold Swap.energy Swap.cross crossImag
  ring

theorem integral_reference_amplitude_a (j : ℕ) (v : Fin 3 → ℂ) :
    (∫ t in (0:ℝ)..1, normSq (referenceAmplitude 1 j v t)) = Swap.qa j v := by
  rw [integral_reference_amplitude 1 (by norm_num)]
  simp [Swap.qa]

theorem integral_reference_amplitude_b (j : ℕ) (v : Fin 3 → ℂ) :
    (∫ t in (0:ℝ)..1, normSq (referenceAmplitude (-1) j v t)) = Swap.qb j v := by
  rw [integral_reference_amplitude (-1) (by norm_num)]
  simp [Swap.qb]

#print axioms integral_reference_amplitude_a
#print axioms integral_reference_amplitude_b
#print axioms integral_frequency_sin_sq
#print axioms amplitude_square
end TwoStateQuantumEmbedding.SwapComparison

namespace TwoStateQuantumEmbedding.SwapComparison

/-- 真实单位轴 Hamiltonian 的共同酉存活概率。 -/
def unitarySurvival (angle nz : ℝ) : ℝ :=
  (Real.cos angle)^2 + nz^2*(Real.sin angle)^2

theorem survival_nonneg (angle nz : ℝ) : 0 ≤ unitarySurvival angle nz := by
  unfold unitarySurvival
  positivity

theorem cos_sq_le_survival (angle nz : ℝ) : (Real.cos angle)^2 ≤ unitarySurvival angle nz := by
  unfold unitarySurvival
  nlinarith [mul_nonneg (sq_nonneg nz) (sq_nonneg (Real.sin angle))]

theorem axis_sq_le_survival (angle nz : ℝ) (hn : nz^2≤1) :
    nz^2 ≤ unitarySurvival angle nz := by
  have h := Real.sin_sq_add_cos_sq angle
  have hp := mul_nonneg (sub_nonneg.mpr hn) (sq_nonneg (Real.cos angle))
  unfold unitarySurvival
  nlinarith

/-- 对任意非负 Hamiltonian 半角直接构造自然绕圈数，常数不依赖圈数。 -/
theorem exists_winding_close (angle p : ℝ) (ha : 0 ≤ angle) (hp : 0 ≤ p)
    (hc : (Real.cos angle)^2 ≤ p) :
    ∃ j : ℕ, |angle-Swap.frequency j/2| ≤ 2*Real.sqrt p := by
  let j : ℕ := Nat.floor (angle/Real.pi)
  have hfloor : (j:ℝ) ≤ angle/Real.pi := Nat.floor_le (div_nonneg ha (le_of_lt Real.pi_pos))
  have hceil : angle/Real.pi < (j:ℝ)+1 := Nat.lt_floor_add_one (angle/Real.pi)
  have hlo : (j:ℝ)*Real.pi ≤ angle := (le_div_iff₀ Real.pi_pos).mp hfloor
  have hhi : angle < ((j:ℝ)+1)*Real.pi := (div_lt_iff₀ Real.pi_pos).mp hceil
  have hdelta : |angle-Swap.frequency j/2| ≤ Real.pi/2 := by
    rw [abs_le]
    unfold Swap.frequency
    constructor <;> nlinarith
  have hsin : |Real.sin (angle-Swap.frequency j/2)| = |Real.cos angle| := by
    have he : angle-Swap.frequency j/2 = (angle-(j:ℝ)*Real.pi)-Real.pi/2 := by
      unfold Swap.frequency
      ring
    rw [he, Real.sin_sub_pi_div_two, Real.cos_sub_nat_mul_pi]
    simp
  have hroot : |Real.cos angle| ≤ Real.sqrt p := by
    have hs := Real.sq_sqrt hp
    have ha' := abs_nonneg (Real.cos angle)
    have hr := Real.sqrt_nonneg p
    nlinarith [sq_abs (Real.cos angle)]
  have hjordan := Real.mul_abs_le_abs_sin hdelta
  rw [hsin] at hjordan
  have hcoef : (1/2:ℝ) ≤ 2/Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).2
    linarith [Real.pi_lt_four]
  have hm := mul_le_mul_of_nonneg_right hcoef (abs_nonneg (angle-Swap.frequency j/2))
  exact ⟨j, by nlinarith⟩

#print axioms exists_winding_close
end TwoStateQuantumEmbedding.SwapComparison
namespace TwoStateQuantumEmbedding.SwapComparison
open GKSLAlgebra
/-- 真实矩阵指数的对角振幅给出精确酉存活概率。 -/
theorem pauliUnitary_survival (n : BlochVec)
    (hn : (n 0)^2+(n 1)^2+(n 2)^2=1) (angle : ℝ) :
    normSq (pauliUnitary n angle 1 0 0) = unitarySurvival angle (n 2) ∧
    normSq (pauliUnitary n angle 1 1 1) = unitarySurvival angle (n 2) := by
  rw [pauliUnitary_formula n hn]
  constructor <;>
    simp [unitarySurvival, realPauli, pauli, normSq_apply,
      Matrix.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re] <;> ring

def xRotation (a : ℝ) : QubitMatrix :=
  !![(Real.cos a : ℂ), -I*(Real.sin a : ℂ);
     -I*(Real.sin a : ℂ), (Real.cos a : ℂ)]

theorem xRotation_eq_exp (a : ℝ) :
    xRotation a = pauliUnitary ![1,0,0] a 1 := by
  rw [pauliUnitary_formula _ (by norm_num)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xRotation, realPauli, pauli, Matrix.smul_apply, smul_eq_mul] <;> ring

theorem xRotation_mul (a b : ℝ) : xRotation a*xRotation b = xRotation (a+b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [xRotation, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add,
      Complex.mul_re, Complex.mul_im] <;> ring

theorem cos_half_frequency (j : ℕ) : Real.cos (Swap.frequency j/2) = 0 := by
  have h : Swap.frequency j/2 = (j:ℝ)*Real.pi+Real.pi/2 := by unfold Swap.frequency; ring
  rw [h, Real.cos_add_pi_div_two, Real.sin_nat_mul_pi]
  simp

theorem sin_half_frequency_sq (j : ℕ) : (Real.sin (Swap.frequency j/2))^2=1 := by
  have h := Real.sin_sq_add_cos_sq (Swap.frequency j/2)
  rw [cos_half_frequency] at h
  simpa using h

/-- 使用真正参考旋转矩阵的复跳跃振幅，与积分中的幅度仅差模一相位。 -/
theorem actual_reference_amplitude_a (j : ℕ) (v : Fin 3 → ℂ) (t : ℝ) :
    (xRotation (Swap.frequency j/2*(1-t))*pauli v*xRotation (Swap.frequency j/2*t)) 0 0 =
      (-I*(Real.sin (Swap.frequency j/2) : ℂ))*referenceAmplitude 1 j v t := by
  have harg : Swap.frequency j/2*(1-t) = Swap.frequency j/2-Swap.frequency j/2*t := by ring
  have hdouble : Swap.frequency j*t = Swap.frequency j/2*t+Swap.frequency j/2*t := by ring
  have htrig : ((Real.sin (Swap.frequency j/2*t) : ℂ))^2+
      ((Real.cos (Swap.frequency j/2*t) : ℂ))^2=1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq (Swap.frequency j/2*t)
  simp [xRotation, pauli, referenceAmplitude, Matrix.mul_apply, Fin.sum_univ_two,
    harg, Real.sin_sub, Real.cos_sub, cos_half_frequency, hdouble, Real.sin_add, Real.cos_add]
  push_cast at htrig
  linear_combination (norm := ring_nf) (-I*Complex.sin ((Swap.frequency j:ℂ)/2)*v 0)*htrig
  simp [Complex.I_sq]

theorem actual_reference_amplitude_b (j : ℕ) (v : Fin 3 → ℂ) (t : ℝ) :
    (xRotation (Swap.frequency j/2*(1-t))*pauli v*xRotation (Swap.frequency j/2*t)) 1 1 =
      (-I*(Real.sin (Swap.frequency j/2) : ℂ))*referenceAmplitude (-1) j v t := by
  have harg : Swap.frequency j/2*(1-t) = Swap.frequency j/2-Swap.frequency j/2*t := by ring
  have hdouble : Swap.frequency j*t = Swap.frequency j/2*t+Swap.frequency j/2*t := by ring
  have htrig : ((Real.sin (Swap.frequency j/2*t) : ℂ))^2+
      ((Real.cos (Swap.frequency j/2*t) : ℂ))^2=1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq (Swap.frequency j/2*t)
  simp [xRotation, pauli, referenceAmplitude, Matrix.mul_apply, Fin.sum_univ_two,
    harg, Real.sin_sub, Real.cos_sub, cos_half_frequency, hdouble, Real.sin_add, Real.cos_add]
  push_cast at htrig
  linear_combination (norm := ring_nf) (-I*Complex.sin ((Swap.frequency j:ℂ)/2)*v 0)*htrig
  simp [Complex.I_sq]

#print axioms pauliUnitary_survival
#print axioms actual_reference_amplitude_a
#print axioms actual_reference_amplitude_b

def diagonalReal (M : QubitMatrix) (l : Fin 2) : ℝ := (M l l).re

/-- 基矢纯态的矩阵夹积逐项等于振幅外积。 -/
theorem basis_sandwich_entry (A B : QubitMatrix) (l : Fin 2) :
    ((A*(Matrix.single l l (1:ℂ) : QubitMatrix)*B.conjTranspose) : QubitMatrix) l l =
      A l l*star (B l l) := by
  fin_cases l <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply, Matrix.conjTranspose_apply]

/-- 精确交换时反对易子项确实为零；此处使用实际 GKSL dissipator。 -/
theorem dissipator_read_at_zero (W U V : QubitMatrix) (l : Fin 2)
    (hzero : (W*U) l l=0) :
    diagonalReal (W*GKSLAlgebra.dissipator V
      (U*Matrix.single l l 1*U.conjTranspose)*W.conjTranspose) l =
      normSq ((W*V*U) l l) := by
  have he : W*GKSLAlgebra.dissipator V (U*Matrix.single l l 1*U.conjTranspose)*W.conjTranspose =
      (W*V*U)*Matrix.single l l 1*(W*V*U).conjTranspose - (1/2:ℂ) •
      ((W*V.conjTranspose*V*U)*Matrix.single l l 1*(W*U).conjTranspose +
       (W*U)*Matrix.single l l 1*(W*V.conjTranspose*V*U).conjTranspose) := by
    simp [GKSLAlgebra.dissipator, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [he]
  simp only [diagonalReal, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, basis_sandwich_entry,
    hzero, star_zero, mul_zero, zero_mul, add_zero, zero_add, smul_zero, sub_zero]
  simp [normSq_apply, Complex.mul_re]

/-- 以实际指数旋转和实际 dissipator 定义的首阶概率贡献。 -/
def referenceFirstOrder (j : ℕ) (v : Fin 3 → ℂ) (l : Fin 2) : ℝ :=
  ∫ t in (0:ℝ)..1,
    diagonalReal (xRotation (Swap.frequency j/2*(1-t)) *
      GKSLAlgebra.dissipator (pauli v)
        (xRotation (Swap.frequency j/2*t)*Matrix.single l l 1*
          (xRotation (Swap.frequency j/2*t)).conjTranspose) *
      (xRotation (Swap.frequency j/2*(1-t))).conjTranspose) l

theorem reference_composition_zero (j : ℕ) (t : ℝ) (l : Fin 2) :
    (xRotation (Swap.frequency j/2*(1-t))*xRotation (Swap.frequency j/2*t)) l l=0 := by
  rw [xRotation_mul, show Swap.frequency j/2*(1-t)+Swap.frequency j/2*t=Swap.frequency j/2 by ring]
  fin_cases l <;> simp [xRotation, cos_half_frequency]

theorem reference_phase_normSq (j : ℕ) :
    normSq (-I*(Real.sin (Swap.frequency j/2) : ℂ))=1 := by
  rw [normSq_mul, Complex.normSq_neg, Complex.normSq_I, one_mul, normSq_ofReal]
  simpa [pow_two] using sin_half_frequency_sq j

/-- Qa 的来源已接回实际单跳跃一阶 Duhamel 积分。 -/
theorem referenceFirstOrder_a (j : ℕ) (v : Fin 3 → ℂ) :
    referenceFirstOrder j v 0 = Swap.qa j v := by
  unfold referenceFirstOrder
  have he (t : ℝ) :
      diagonalReal (xRotation (Swap.frequency j/2*(1-t)) *
      GKSLAlgebra.dissipator (pauli v)
        (xRotation (Swap.frequency j/2*t)*Matrix.single 0 0 1*
          (xRotation (Swap.frequency j/2*t)).conjTranspose) *
      (xRotation (Swap.frequency j/2*(1-t))).conjTranspose) 0 =
      normSq (referenceAmplitude 1 j v t) := by
    rw [dissipator_read_at_zero _ _ _ _ (reference_composition_zero j t 0),
      actual_reference_amplitude_a, normSq_mul, reference_phase_normSq, one_mul]
  simp_rw [he]
  exact integral_reference_amplitude_a j v

theorem referenceFirstOrder_b (j : ℕ) (v : Fin 3 → ℂ) :
    referenceFirstOrder j v 1 = Swap.qb j v := by
  unfold referenceFirstOrder
  have he (t : ℝ) :
      diagonalReal (xRotation (Swap.frequency j/2*(1-t)) *
      GKSLAlgebra.dissipator (pauli v)
        (xRotation (Swap.frequency j/2*t)*Matrix.single 1 1 1*
          (xRotation (Swap.frequency j/2*t)).conjTranspose) *
      (xRotation (Swap.frequency j/2*(1-t))).conjTranspose) 1 =
      normSq (referenceAmplitude (-1) j v t) := by
    rw [dissipator_read_at_zero _ _ _ _ (reference_composition_zero j t 1),
      actual_reference_amplitude_b, normSq_mul, reference_phase_normSq, one_mul]
  simp_rw [he]
  exact integral_reference_amplitude_b j v

#print axioms referenceFirstOrder_a
#print axioms referenceFirstOrder_b
end TwoStateQuantumEmbedding.SwapComparison
