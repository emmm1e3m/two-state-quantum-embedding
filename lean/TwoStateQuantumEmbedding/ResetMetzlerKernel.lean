import TwoStateQuantumEmbedding.ExponentialHermite
import TwoStateQuantumEmbedding.AffineExponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
open Matrix NormedSpace MeasureTheory Set
open scoped Matrix.Norms.Operator Interval

namespace TwoStateQuantumEmbedding.ResetMetzler
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

abbrev M2 := Matrix (Fin 2) (Fin 2) ℝ
def matrix (a l r c : ℝ) : M2 := !![-a, r; c, -l]
def gap (a l r c : ℝ) : ℝ := Real.sqrt ((a - l)^2 + 4*r*c)
def beta (a l r c : ℝ) : ℝ := (a+l-gap a l r c)/2
def gamma (a l r c : ℝ) : ℝ := (a+l+gap a l r c)/2

/-- 积分定义在重根时仍然有效。 -/
def kernel (b g t : ℝ) : ℝ :=
  ExponentialHermite.newtonFirst (-b) (-g) t

theorem kernel_integral (b g t : ℝ) :
    kernel b g t = ∫ u in (0:ℝ)..t, Real.exp (-b*(t-u))*Real.exp (-g*u) := by
  unfold kernel ExponentialHermite.newtonFirst
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [← Real.exp_add]
  congr 1
  ring

theorem kernel_symmetric (b g t : ℝ) : kernel b g t = kernel g b t := by
  unfold kernel ExponentialHermite.newtonFirst
  have h := intervalIntegral.integral_comp_sub_left
    (fun u : ℝ => Real.exp ((t-u)*(-g)+u*(-b))) t (a:=0) (b:=t)
  simp only [sub_self, sub_zero] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro u _
  congr 1
  ring

theorem kernel_nonneg (b g : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ kernel b g t :=
  ExponentialHermite.newtonFirst_nonneg (-b) (-g) ht

theorem kernel_continuous (b g : ℝ) : Continuous (kernel b g) :=
  ExponentialHermite.continuous_newtonFirst (-b) (-g)

theorem gap_sq (a l r c : ℝ) (hh : 0 ≤ r*c) :
    gap a l r c ^ 2 = (a-l)^2+4*r*c := by
  exact Real.sq_sqrt (by nlinarith [sq_nonneg (a-l)])

theorem decay_sum (a l r c : ℝ) : beta a l r c + gamma a l r c = a+l := by
  unfold beta gamma
  ring

theorem decay_prod (a l r c : ℝ) (hh : 0 ≤ r*c) :
    beta a l r c * gamma a l r c = a*l-r*c := by
  have h := gap_sq a l r c hh
  unfold beta gamma
  nlinarith

theorem decay_diff (a l r c : ℝ) : gamma a l r c-beta a l r c = gap a l r c := by
  unfold beta gamma
  ring

theorem annihilator (a l r c b g : ℝ) (hs : b+g=a+l) (hp : b*g=a*l-r*c) :
    (matrix a l r c-(-b) • (1:M2)) * (matrix a l r c-(-g) • (1:M2)) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  · linear_combination -a*hs+hp
  · linear_combination r*hs
  · linear_combination c*hs
  · linear_combination -l*hs+hp

/-- 二次湮灭关系接到真实指数；不需要谱差非零。 -/
theorem exp_kernel_of_roots (a l r c b g t : ℝ)
    (hs : b+g=a+l) (hp : b*g=a*l-r*c) :
    exp (t • matrix a l r c) = Real.exp (-b*t) • (1:M2) +
      kernel b g t • (matrix a l r c - (-b) • (1:M2)) := by
  have h := ExponentialHermite.scalar_duhamel_left_terminated
    (matrix a l r c) (1:M2) (-b) (-g) t (by
      simpa only [one_mul] using annihilator a l r c b g hs hp)
  simpa only [one_mul, kernel, mul_neg, neg_mul, mul_comm t b] using h

theorem exp_kernel (a l r c t : ℝ) (hh : 0 ≤ r*c) :
    exp (t • matrix a l r c) = Real.exp (-beta a l r c*t) • (1:M2) +
      kernel (beta a l r c) (gamma a l r c) t •
        (matrix a l r c - (-beta a l r c) • (1:M2)) :=
  exp_kernel_of_roots a l r c _ _ t (decay_sum a l r c) (decay_prod a l r c hh)

theorem exp_entry01 (a l r c t : ℝ) (hh : 0 ≤ r*c) :
    exp (t • matrix a l r c) 0 1 = r * kernel (beta a l r c) (gamma a l r c) t := by
  rw [exp_kernel a l r c t hh]
  simp [matrix, Matrix.one_apply, mul_comm]

theorem exp_entry10 (a l r c t : ℝ) (hh : 0 ≤ r*c) :
    exp (t • matrix a l r c) 1 0 = c * kernel (beta a l r c) (gamma a l r c) t := by
  rw [exp_kernel a l r c t hh]
  simp [matrix, Matrix.one_apply, mul_comm]

theorem exp_entry00_kernel (a l r c t : ℝ) (hh : 0 ≤ r*c) :
    exp (t • matrix a l r c) 0 0 = Real.exp (-beta a l r c*t) +
      (beta a l r c-a)*kernel (beta a l r c) (gamma a l r c) t := by
  rw [exp_kernel a l r c t hh]
  simp [matrix, Matrix.one_apply]
  ring

theorem exp_entry11_kernel (a l r c t : ℝ) (hh : 0 ≤ r*c) :
    exp (t • matrix a l r c) 1 1 = Real.exp (-beta a l r c*t) +
      (beta a l r c-l)*kernel (beta a l r c) (gamma a l r c) t := by
  rw [exp_kernel a l r c t hh]
  simp [matrix, Matrix.one_apply]
  ring

theorem kernel_mul_gap (b g t : ℝ) :
    (g-b)*kernel b g t = Real.exp (-b*t)-Real.exp (-g*t) := by
  have hd (u : ℝ) : HasDerivAt
      (fun u : ℝ => Real.exp ((t-u)*(-b)+u*(-g)))
      ((b-g)*Real.exp ((t-u)*(-b)+u*(-g))) u := by
    convert ((((hasDerivAt_const u t).sub (hasDerivAt_id u)).mul_const (-b)).add
      ((hasDerivAt_id u).mul_const (-g))).exp using 1
    · ext x
      dsimp
    · dsimp
      ring
  have hc : Continuous (fun u : ℝ => (b-g)*Real.exp ((t-u)*(-b)+u*(-g))) := by
    fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a:=0) (b:=t) (fun u _ => hd u) (hc.intervalIntegrable 0 t)
  rw [intervalIntegral.integral_const_mul] at hi
  change (b-g)*kernel b g t = _ at hi
  simp only [sub_self, zero_mul, zero_add, sub_zero, add_zero] at hi
  have e₁ : t * -g = -g*t := by ring
  have e₂ : t * -b = -b*t := by ring
  rw [e₁, e₂] at hi
  linarith

theorem kernel_distinct (b g t : ℝ) (hbg : g ≠ b) :
    kernel b g t = (Real.exp (-b*t)-Real.exp (-g*t))/(g-b) := by
  exact (eq_div_iff (sub_ne_zero.mpr hbg)).2 (by
    simpa only [mul_comm] using kernel_mul_gap b g t)

theorem kernel_repeated (b t : ℝ) : kernel b b t = t * Real.exp (-b*t) := by
  unfold kernel ExponentialHermite.newtonFirst
  have h : (fun u : ℝ => Real.exp ((t-u)*(-b)+u*(-b))) =
      (fun _ : ℝ => Real.exp (-b*t)) := by
    funext u
    congr 1
    ring
  rw [h]
  simp

theorem kernel_le_time (b g t : ℝ) (hbg : b ≤ g) (ht : 0 ≤ t) :
    kernel b g t ≤ t*Real.exp (-b*t) := by
  unfold kernel ExponentialHermite.newtonFirst
  have hc : Continuous (fun u : ℝ => Real.exp ((t-u)*(-b)+u*(-g))) := by fun_prop
  have hm := intervalIntegral.integral_mono_on (μ:=volume) ht (hc.intervalIntegrable 0 t)
    (continuous_const.intervalIntegrable 0 t)
    (g:=fun _ : ℝ => Real.exp (-b*t)) (fun u hu => by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hbg) hu.1])
  simpa using hm

theorem kernel_le_inv_gap (b g t : ℝ) (hbg : b < g) :
    kernel b g t ≤ Real.exp (-b*t)/(g-b) := by
  rw [kernel_distinct b g t (ne_of_gt hbg)]
  exact div_le_div_of_nonneg_right (by linarith [Real.exp_pos (-g*t)])
    (sub_nonneg.mpr hbg.le)

theorem decay_order (a l r c : ℝ) (hh : 0 ≤ r*c) :
    beta a l r c ≤ a ∧ beta a l r c ≤ l ∧
    a ≤ gamma a l r c ∧ l ≤ gamma a l r c := by
  have hsq := gap_sq a l r c hh
  have hg : 0 ≤ gap a l r c := Real.sqrt_nonneg _
  have h₁ : a-l ≤ gap a l r c := by nlinarith [sq_nonneg (gap a l r c-(a-l))]
  have h₂ : l-a ≤ gap a l r c := by nlinarith [sq_nonneg (gap a l r c+(a-l))]
  unfold beta gamma
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem exp_entry11_bounds (a l r c t : ℝ) (hh : 0 ≤ r*c) (ht : 0 ≤ t) :
    0 ≤ exp (t • matrix a l r c) 1 1 ∧
    exp (t • matrix a l r c) 1 1 ≤ Real.exp (-beta a l r c*t) := by
  have ho := decay_order a l r c hh
  have hk := kernel_nonneg (beta a l r c) (gamma a l r c) ht
  constructor
  · have he := exp_kernel_of_roots a l r c (gamma a l r c) (beta a l r c) t
      (by linarith [decay_sum a l r c]) (by simpa [mul_comm] using decay_prod a l r c hh)
    rw [he]
    simp [matrix]
    rw [kernel_symmetric]
    apply add_nonneg (Real.exp_nonneg _)
    nlinarith [mul_nonneg hk (sub_nonneg.mpr ho.2.2.2)]
  · rw [exp_entry11_kernel a l r c t hh]
    exact add_le_of_nonpos_right (mul_nonpos_of_nonpos_of_nonneg (by linarith [ho.2.1]) hk)

/-- 任意实向量的二模权重。 -/
def slowWeight (a l r c b g v w : ℝ) : ℝ :=
  ((g-a)*v^2+(g-l)*w^2+(r+c)*(v*w))/(g-b)

theorem quadratic_two_modes_of_roots (a l r c b g v w t : ℝ)
    (hs : b+g=a+l) (hp : b*g=a*l-r*c) (hbg : g ≠ b) :
    dotProduct ![v,w] (exp (t • matrix a l r c) *ᵥ ![v,w]) =
      slowWeight a l r c b g v w * Real.exp (-b*t) +
      (v^2+w^2-slowWeight a l r c b g v w)*Real.exp (-g*t) := by
  rw [exp_kernel_of_roots a l r c b g t hs hp, kernel_distinct b g t hbg]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, matrix, slowWeight]
  field_simp
  <;> ring

theorem quadratic_two_modes (a l r c v w t : ℝ) (hh : 0 ≤ r*c)
    (hd : 0 < gap a l r c) (hv : v^2+w^2=1) :
    dotProduct ![v,w] (exp (t • matrix a l r c) *ᵥ ![v,w]) =
      slowWeight a l r c (beta a l r c) (gamma a l r c) v w *
        Real.exp (-beta a l r c*t) +
      (1-slowWeight a l r c (beta a l r c) (gamma a l r c) v w)*
        Real.exp (-gamma a l r c*t) := by
  have hbg : gamma a l r c ≠ beta a l r c := by
    intro he
    have h := decay_diff a l r c
    rw [he, sub_self] at h
    linarith
  simpa only [hv] using quadratic_two_modes_of_roots a l r c _ _ v w t
    (decay_sum a l r c) (decay_prod a l r c hh) hbg

theorem exp_entry00_two_modes (a l r c t : ℝ) (hh : 0 ≤ r*c)
    (hd : 0 < gap a l r c) :
    exp (t • matrix a l r c) 0 0 =
      ((gamma a l r c-a)/gap a l r c)*Real.exp (-beta a l r c*t) +
      (1-(gamma a l r c-a)/gap a l r c)*Real.exp (-gamma a l r c*t) := by
  simpa [slowWeight, Matrix.mulVec, dotProduct, Fin.sum_univ_two, decay_diff] using
    quadratic_two_modes a l r c 1 0 t hh hd (by norm_num)

/-- Duhamel恒等式保留人口自由衰减，重根无需另分支。 -/
theorem exp_entry00_volterra (a l r c t : ℝ) (hh : 0 ≤ r*c) :
    exp (t • matrix a l r c) 0 0-Real.exp (-a*t) =
      (r*c) * ∫ u in (0:ℝ)..t, Real.exp (-a*(t-u))*
        kernel (beta a l r c) (gamma a l r c) u := by
  let f : ℝ → M2 := fun u => Real.exp ((t-u)*(-a)) •
    ((matrix a l r c-(-a) • (1:M2))*exp (u • matrix a l r c))
  have hc : Continuous f := by
    exact (show Continuous (fun u : ℝ => Real.exp ((t-u)*(-a))) by fun_prop).smul
      (continuous_const.mul (differentiable_exp_smul_const ℝ (matrix a l r c)).continuous)
  have hi := (AffineExponential.entryCLM (n:=Fin 2) 0 0).intervalIntegral_comp_comm
    (μ:=volume) (hc.intervalIntegrable 0 t)
  change (∫ u in (0:ℝ)..t, f u 0 0) = (∫ u in (0:ℝ)..t, f u) 0 0 at hi
  have he := congrArg (fun Q : M2 => Q 0 0)
    (ExponentialHermite.scalar_duhamel (matrix a l r c) (-a) t)
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply_eq, mul_one] at he
  change exp (t • matrix a l r c) 0 0 =
    Real.exp (t*(-a)) + (∫ u in (0:ℝ)..t, f u) 0 0 at he
  rw [← hi] at he
  have hrow (Q : M2) : ((matrix a l r c-(-a) • (1:M2))*Q) 0 0 = r*Q 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, matrix]
  have hf (u : ℝ) : f u 0 0 = (r*c)*(Real.exp (-a*(t-u))*
      kernel (beta a l r c) (gamma a l r c) u) := by
    change Real.exp ((t-u)*(-a)) *
      (((matrix a l r c-(-a) • (1:M2))*exp (u • matrix a l r c)) 0 0) = _
    rw [hrow, exp_entry10 a l r c u hh]
    rw [show (t-u)*(-a) = -a*(t-u) by ring]
    ring
  simp_rw [hf] at he
  rw [intervalIntegral.integral_const_mul] at he
  have ha : t*(-a) = -a*t := by ring
  rw [ha] at he
  linarith

theorem exp_entry00_free_le (a l r c t : ℝ) (hh : 0 ≤ r*c) (ht : 0 ≤ t) :
    Real.exp (-a*t) ≤ exp (t • matrix a l r c) 0 0 := by
  have he := exp_entry00_volterra a l r c t hh
  have hi : 0 ≤ ∫ u in (0:ℝ)..t, Real.exp (-a*(t-u))*
      kernel (beta a l r c) (gamma a l r c) u := by
    apply intervalIntegral.integral_nonneg ht
    intro u hu
    exact mul_nonneg (Real.exp_nonneg _)
      (kernel_nonneg _ _ (show 0 ≤ u from hu.1))
  nlinarith [mul_nonneg hh hi]

/-- 无谱差分母的Volterra上界。 -/
theorem convolution_kernel_le_time (a b g t : ℝ) (ha : b ≤ a)
    (hbg : b ≤ g) (ht : 0 ≤ t) :
    (∫ u in (0:ℝ)..t, Real.exp (-a*(t-u))*kernel b g u) ≤
      t^2*Real.exp (-b*t) := by
  have hc : Continuous (fun u : ℝ => Real.exp (-a*(t-u))*kernel b g u) :=
    (by fun_prop : Continuous (fun u : ℝ => Real.exp (-a*(t-u)))).mul
      (kernel_continuous b g)
  have hm := intervalIntegral.integral_mono_on (μ:=volume) ht
    (hc.intervalIntegrable 0 t) (continuous_const.intervalIntegrable 0 t)
    (g:=fun _ : ℝ => t*Real.exp (-b*t)) (fun u hu => by
      have he : Real.exp (-a*(t-u)) ≤ Real.exp (-b*(t-u)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hu.2)]
      have hk : kernel b g u ≤ t*Real.exp (-b*u) :=
        (kernel_le_time b g u hbg hu.1).trans
          (mul_le_mul_of_nonneg_right hu.2 (Real.exp_nonneg _))
      calc
        _ ≤ Real.exp (-b*(t-u))*(t*Real.exp (-b*u)) :=
          mul_le_mul he hk (kernel_nonneg b g hu.1) (Real.exp_nonneg _)
        _ = t*Real.exp (-b*t) := by
          rw [mul_left_comm, ← Real.exp_add]
          congr 1
          ring)
  simpa [pow_two, mul_assoc] using hm

theorem convolution_kernel_le_gap (a b g t : ℝ) (ha : b ≤ a)
    (hbg : b < g) (ht : 0 ≤ t) :
    (∫ u in (0:ℝ)..t, Real.exp (-a*(t-u))*kernel b g u) ≤
      t*Real.exp (-b*t)/(g-b) := by
  have hc : Continuous (fun u : ℝ => Real.exp (-a*(t-u))*kernel b g u) :=
    (by fun_prop : Continuous (fun u : ℝ => Real.exp (-a*(t-u)))).mul
      (kernel_continuous b g)
  have hm := intervalIntegral.integral_mono_on (μ:=volume) ht
    (hc.intervalIntegrable 0 t) (continuous_const.intervalIntegrable 0 t)
    (g:=fun _ : ℝ => Real.exp (-b*t)/(g-b)) (fun u hu => by
      have he : Real.exp (-a*(t-u)) ≤ Real.exp (-b*(t-u)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hu.2)]
      calc
        _ ≤ Real.exp (-b*(t-u))*(Real.exp (-b*u)/(g-b)) :=
          mul_le_mul he (kernel_le_inv_gap b g u hbg)
            (kernel_nonneg b g hu.1) (Real.exp_nonneg _)
        _ = Real.exp (-b*t)/(g-b) := by
          rw [← mul_div_assoc, ← Real.exp_add]
          congr 2
          ring)
  simpa [mul_div_assoc] using hm

theorem exp_entry00_correction_le_time (a l r c t : ℝ) (hh : 0 ≤ r*c)
    (ht : 0 ≤ t) :
    exp (t • matrix a l r c) 0 0-Real.exp (-a*t) ≤
      (r*c)*t^2*Real.exp (-beta a l r c*t) := by
  rw [exp_entry00_volterra a l r c t hh]
  have hbg : beta a l r c ≤ gamma a l r c := by
    have h := decay_diff a l r c
    have hd : 0 ≤ gap a l r c := Real.sqrt_nonneg _
    linarith
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left
    (convolution_kernel_le_time a _ _ t (decay_order a l r c hh).1 hbg ht) hh

theorem exp_entry00_correction_le_gap (a l r c t : ℝ) (hh : 0 ≤ r*c)
    (hd : 0 < gap a l r c) (ht : 0 ≤ t) :
    exp (t • matrix a l r c) 0 0-Real.exp (-a*t) ≤
      (r*c)*t*Real.exp (-beta a l r c*t)/gap a l r c := by
  rw [exp_entry00_volterra a l r c t hh]
  have hbg : beta a l r c < gamma a l r c := by linarith [decay_diff a l r c]
  simpa [mul_assoc, mul_div_assoc, decay_diff] using mul_le_mul_of_nonneg_left
    (convolution_kernel_le_gap a _ _ t (decay_order a l r c hh).1 hbg ht) hh

#print axioms exp_kernel
#print axioms exp_entry01
#print axioms exp_entry11_bounds
#print axioms quadratic_two_modes
#print axioms exp_entry00_volterra
#print axioms exp_entry00_correction_le_time
#print axioms exp_entry00_correction_le_gap

end TwoStateQuantumEmbedding.ResetMetzler
