import TwoStateQuantumEmbedding.UnitaryBoundary
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Pow

noncomputable section
open Matrix NormedSpace Filter
open scoped Topology Matrix.Norms.Operator

namespace TwoStateQuantumEmbedding.HamiltonianHessian
open GKSLAlgebra CanonicalBloch

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

def radius (ω h : ℝ) : ℝ := Real.sqrt ((ω / 2)^2 + h^2)
def probability (ω h : ℝ) : ℝ :=
  Real.cos (radius ω h)^2 + h^2 / (radius ω h)^2 * Real.sin (radius ω h)^2
def actualProbability (ω h : ℝ) : ℝ := (canonicalOutput ![ω, 0, 2*h] 0 1).1

def outputReadout (E : AugmentedMatrix) : ℝ × ℝ :=
  ((1 + E 3 3 + E 3 0)/2, (1 + E 3 3 - E 3 0)/2)

section Cubic
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- 从真实常系数 ODE 导出的三次最小多项式旋转公式。 -/
theorem exp_of_cube (Q : A) (s : ℝ) (hs : s ≠ 0)
    (hQ : Q^3 = -(s^2) • Q) (t : ℝ) :
    exp (t • Q) = 1 + (Real.sin (s*t)/s) • Q +
      ((1-Real.cos (s*t))/s^2) • Q^2 := by
  let F : ℝ → A := fun u => 1 + (Real.sin (s*u)/s) • Q +
    ((1-Real.cos (s*u))/s^2) • Q^2
  have hd1 (u : ℝ) : HasDerivAt (fun r : ℝ => Real.sin (s*r)/s) (Real.cos (s*u)) u := by
    convert (((hasDerivAt_id u).const_mul s).sin.div_const s) using 1 <;> simp [hs]
  have hd2 (u : ℝ) : HasDerivAt (fun r : ℝ => (1-Real.cos (s*r))/s^2)
      (Real.sin (s*u)/s) u := by
    convert ((hasDerivAt_const u 1).sub (((hasDerivAt_id u).const_mul s).cos)).div_const (s^2) using 1
    · funext r
      simp [div_eq_mul_inv, mul_comm]
    · dsimp
      field_simp
      ring
  have hF (u : ℝ) : HasDerivAt F (Q * F u) u := by
    have hd := ((hasDerivAt_const u (1:A)).add ((hd1 u).smul_const Q)).add
      ((hd2 u).smul_const (Q^2))
    convert hd using 1
    dsimp [F]
    rw [mul_add, mul_add, mul_one, mul_smul_comm, mul_smul_comm,
      ← pow_two, ← pow_succ', hQ, smul_smul]
    have hc : ((1-Real.cos (s*u))/s^2) * (-(s^2)) = Real.cos (s*u)-1 := by
      field_simp
      ring
    rw [hc]
    module
  exact (eq_exp_of_hasDerivAt_left Q F (by simp [F]) hF t).symm
end Cubic

theorem radius_sq (ω h : ℝ) : (radius ω h)^2 = (ω/2)^2+h^2 :=
  Real.sq_sqrt (by positivity)

theorem augmentedGenerator_cube (ω h : ℝ) :
    (augmentedGenerator ![ω,0,2*h] 0)^3 =
      -((2 * radius ω h)^2) • augmentedGenerator ![ω,0,2*h] 0 := by
  rw [mul_pow, radius_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [augmentedGenerator, blochMatrix, crossMatrix, drift, Matrix.trace,
      Matrix.diag, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals ring

/-- 完整真实矩阵指数的两个概率，范围为 R>0。 -/
theorem canonicalOutput_formula (ω h : ℝ) (hR : 0 < radius ω h) :
    canonicalOutput ![ω, 0, 2*h] 0 1 = (probability ω h, probability ω h) := by
  have hn : 2 * radius ω h ≠ 0 := by positivity
  have he := exp_of_cube (augmentedGenerator ![ω,0,2*h] 0) (2*radius ω h) hn
    (augmentedGenerator_cube ω h) 1
  change outputReadout (exp (1 • augmentedGenerator ![ω,0,2*h] 0)) = _
  simp only [one_smul] at he ⊢
  erw [he]
  simp [outputReadout, augmentedGenerator, blochMatrix, crossMatrix, drift, Matrix.trace,
    Matrix.diag, pow_two]
  have hr := radius_sq ω h
  have hc := Real.sin_sq_add_cos_sq (radius ω h)
  rw [Real.cos_two_mul]
  unfold probability
  field_simp
  nlinarith [mul_pos hR hR]

theorem actualProbability_formula (ω h : ℝ) (hR : 0 < radius ω h) :
    actualProbability ω h = probability ω h :=
  congrArg Prod.fst (canonicalOutput_formula ω h hR)

abbrev Point := ℝ × ℝ
def base : Point := (Real.pi, 0)
def radiusFunction (p : Point) : ℝ := radius p.1 p.2
def cosineFunction (p : Point) : ℝ := Real.cos (radiusFunction p)
def waveFunction (p : Point) : ℝ := (Real.sin (radiusFunction p) / radiusFunction p)^2
def explicitProbability (p : Point) : ℝ := cosineFunction p ^ 2 + p.2^2 * waveFunction p
def actual (p : Point) : ℝ := actualProbability p.1 p.2
abbrev omegaDual : Point →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
abbrev hDual : Point →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ

theorem probability_eq_explicit (ω h : ℝ) : probability ω h = explicitProbability (ω,h) := by
  simp [probability, explicitProbability, cosineFunction, waveFunction, radiusFunction, div_pow]
  ring

theorem radiusFunction_base : radiusFunction base = Real.pi / 2 := by
  simp [radiusFunction, radius, base, Real.sqrt_sq (by positivity : 0 ≤ Real.pi / 2)]

theorem radiusFunction_continuous : Continuous radiusFunction := by
  unfold radiusFunction radius
  fun_prop

theorem radiusFunction_base_pos : 0 < radiusFunction base := by
  rw [radiusFunction_base]
  positivity

theorem actual_eventually_eq_explicit : actual =ᶠ[𝓝 base] explicitProbability := by
  have hp : ∀ᶠ p in 𝓝 base, 0 < radiusFunction p :=
    radiusFunction_continuous.continuousAt.eventually (lt_mem_nhds radiusFunction_base_pos)
  filter_upwards [hp] with p hp
  exact (actualProbability_formula p.1 p.2 hp).trans (probability_eq_explicit _ _)

theorem radiusFunction_contDiffAt (p : Point) (hp : 0 < radiusFunction p) :
    ContDiffAt ℝ 2 radiusFunction p := by
  have hn : (p.1/2)^2+p.2^2 ≠ 0 := by
    intro hz
    have : radiusFunction p = 0 := by simp [radiusFunction, radius, hz]
    linarith
  unfold radiusFunction radius
  have hh : ContDiffAt ℝ 2 (fun p : Point => (p.1/2)^2+p.2^2) p := by fun_prop
  exact hh.sqrt hn

theorem cosineFunction_contDiffAt (p : Point) (hp : 0 < radiusFunction p) :
    ContDiffAt ℝ 2 cosineFunction p := (radiusFunction_contDiffAt p hp).cos

theorem waveFunction_contDiffAt (p : Point) (hp : 0 < radiusFunction p) :
    ContDiffAt ℝ 2 waveFunction p := by
  exact (((radiusFunction_contDiffAt p hp).sin).div
    (radiusFunction_contDiffAt p hp) (ne_of_gt hp)).pow 2

theorem radiusFunction_hasFDerivAt_base :
    HasFDerivAt radiusFunction ((1/2:ℝ) • omegaDual) base := by
  have hw : HasFDerivAt (fun p : Point => p.1/2) ((1/2:ℝ) • omegaDual) base := by
    convert (hasFDerivAt_fst (𝕜:=ℝ) (p:=base)).const_mul (1/2:ℝ) using 1
    funext p
    ring
  have hf : HasFDerivAt (fun p : Point => (p.1/2)^2+p.2^2)
      ((2 * (base.1/2)) • ((1/2:ℝ) • omegaDual) + (2 * base.2) • hDual) base := by
    convert (hw.pow 2).add
      ((hasFDerivAt_snd (𝕜:=ℝ) (p:=base)).pow 2) using 1
    simp
  have hn : (base.1/2)^2+base.2^2 ≠ 0 := by dsimp [base]; positivity
  have hs := hf.sqrt hn
  convert hs using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro v
    change (1/2:ℝ) * v.1 = (1/(2*radiusFunction base)) *
      ((2*(base.1/2))*((1/2)*v.1)+(2*base.2)*v.2)
    rw [radiusFunction_base]
    dsimp [base]
    field_simp
    ring

theorem cosineFunction_hasFDerivAt_base :
    HasFDerivAt cosineFunction ((-1/2:ℝ) • omegaDual) base := by
  have hd := radiusFunction_hasFDerivAt_base.cos
  convert hd using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro v
    simp [radiusFunction_base, smul_smul, smul_eq_mul]
    ring

theorem cosineFunction_base : cosineFunction base = 0 := by
  simp [cosineFunction, radiusFunction_base]

theorem waveFunction_base : waveFunction base = 4 / Real.pi^2 := by
  simp [waveFunction, radiusFunction_base]
  ring

def gradientExpression (p : Point) : Point →L[ℝ] ℝ :=
  (2 * cosineFunction p) • fderiv ℝ cosineFunction p +
    p.2^2 • fderiv ℝ waveFunction p +
      (2 * p.2 * waveFunction p) • hDual

theorem explicitProbability_hasFDerivAt (p : Point) (hp : 0 < radiusFunction p) :
    HasFDerivAt explicitProbability (gradientExpression p) p := by
  have hf := (cosineFunction_contDiffAt p hp).differentiableAt (by norm_num)
  have hg := (waveFunction_contDiffAt p hp).differentiableAt (by norm_num)
  convert (hf.hasFDerivAt.pow 2).add
    (((hasFDerivAt_snd (𝕜:=ℝ) (p:=p)).pow 2).mul hg.hasFDerivAt) using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro v
    simp [gradientExpression, smul_eq_mul]
    ring

theorem gradientExpression_base : gradientExpression base = 0 := by
  simp only [gradientExpression, cosineFunction_base]
  simp [base]

/-- 真概率在交换基点的一阶 Fréchet 导数为零。 -/
theorem actual_hasFDerivAt_base : HasFDerivAt actual (0 : Point →L[ℝ] ℝ) base := by
  have hd := explicitProbability_hasFDerivAt base radiusFunction_base_pos
  rw [gradientExpression_base] at hd
  exact hd.congr_of_eventuallyEq actual_eventually_eq_explicit

/-- Hessian 按 (ω,h) 的次序定义为对角双线性映射。 -/
def expectedHessian : Point →L[ℝ] (Point →L[ℝ] ℝ) :=
  (1/2:ℝ) • omegaDual.smulRight omegaDual +
    (8/Real.pi^2) • hDual.smulRight hDual

theorem gradientExpression_hasFDerivAt_base :
    HasFDerivAt gradientExpression expectedHessian base := by
  have hf2 : DifferentiableAt ℝ (fderiv ℝ cosineFunction) base :=
    ((cosineFunction_contDiffAt base radiusFunction_base_pos).fderiv_right
      (m:=1) (by norm_num)).differentiableAt (by norm_num)
  have hg2 : DifferentiableAt ℝ (fderiv ℝ waveFunction) base :=
    ((waveFunction_contDiffAt base radiusFunction_base_pos).fderiv_right
      (m:=1) (by norm_num)).differentiableAt (by norm_num)
  have hg := (waveFunction_contDiffAt base radiusFunction_base_pos).differentiableAt (by norm_num)
  have h1 := (cosineFunction_hasFDerivAt_base.const_mul 2).smul hf2.hasFDerivAt
  have h2 := ((hasFDerivAt_snd (𝕜:=ℝ) (p:=base)).pow 2).smul hg2.hasFDerivAt
  have h3 := (((hasFDerivAt_snd (𝕜:=ℝ) (p:=base)).const_mul 2).mul
    hg.hasFDerivAt).smul_const hDual
  convert (h1.add h2).add h3 using 1
  · rfl
  · rw [cosineFunction_base, waveFunction_base, cosineFunction_hasFDerivAt_base.fderiv]
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    simp [expectedHessian, base, smul_eq_mul]
    ring

theorem explicit_fderiv_eventually_eq_gradient :
    fderiv ℝ explicitProbability =ᶠ[𝓝 base] gradientExpression := by
  have hp : ∀ᶠ p in 𝓝 base, 0 < radiusFunction p :=
    radiusFunction_continuous.continuousAt.eventually (lt_mem_nhds radiusFunction_base_pos)
  filter_upwards [hp] with p hp
  exact (explicitProbability_hasFDerivAt p hp).fderiv

/-- 真概率的实际二阶 Fréchet 导数，不以闭式概率对应作为假设。 -/
theorem actual_fderiv_hasFDerivAt_base :
    HasFDerivAt (fderiv ℝ actual) expectedHessian base := by
  exact gradientExpression_hasFDerivAt_base.congr_of_eventuallyEq
    (actual_eventually_eq_explicit.fderiv.trans explicit_fderiv_eventually_eq_gradient)

theorem actual_hessian_omega_omega :
    fderiv ℝ (fderiv ℝ actual) base (1,0) (1,0) = 1/2 := by
  rw [actual_fderiv_hasFDerivAt_base.fderiv]
  simp [expectedHessian]

theorem actual_hessian_h_h :
    fderiv ℝ (fderiv ℝ actual) base (0,1) (0,1) = 8/Real.pi^2 := by
  rw [actual_fderiv_hasFDerivAt_base.fderiv]
  simp [expectedHessian]

theorem actual_hessian_omega_h :
    fderiv ℝ (fderiv ℝ actual) base (1,0) (0,1) = 0 := by
  rw [actual_fderiv_hasFDerivAt_base.fderiv]
  simp [expectedHessian]

theorem actual_hessian_h_omega :
    fderiv ℝ (fderiv ℝ actual) base (0,1) (1,0) = 0 := by
  rw [actual_fderiv_hasFDerivAt_base.fderiv]
  simp [expectedHessian]

theorem actual_base : actual base = 0 := by
  rw [actual_eventually_eq_explicit.eq_of_nhds]
  simp only [explicitProbability, cosineFunction_base]
  simp [base]

theorem canonicalOutput_eq_diagonal_actual (ω h : ℝ) (hR : 0 < radius ω h) :
    canonicalOutput ![ω,0,2*h] 0 1 = (actualProbability ω h, actualProbability ω h) := by
  rw [actualProbability_formula ω h hR, canonicalOutput_formula ω h hR]

/-- 080 可直接据此把零耗散目标写为 (1−μ) 倍的同一真实概率。 -/
theorem canonicalOutput_eventually_eq_diagonal :
    (fun p : Point => canonicalOutput ![p.1,0,2*p.2] 0 1) =ᶠ[𝓝 base]
      fun p => (actual p, actual p) := by
  have hp : ∀ᶠ p in 𝓝 base, 0 < radiusFunction p :=
    radiusFunction_continuous.continuousAt.eventually (lt_mem_nhds radiusFunction_base_pos)
  filter_upwards [hp] with p hp
  exact canonicalOutput_eq_diagonal_actual p.1 p.2 hp

def actualB (p : Point) : ℝ := (canonicalOutput ![p.1,0,2*p.2] 0 1).2

theorem actualB_eventually_eq_actual : actualB =ᶠ[𝓝 base] actual := by
  filter_upwards [canonicalOutput_eventually_eq_diagonal] with p hp
  exact congrArg Prod.snd hp

theorem actualB_base : actualB base = 0 :=
  actualB_eventually_eq_actual.eq_of_nhds.trans actual_base

theorem actualB_hasFDerivAt_base : HasFDerivAt actualB (0 : Point →L[ℝ] ℝ) base :=
  actual_hasFDerivAt_base.congr_of_eventuallyEq actualB_eventually_eq_actual

theorem actualB_fderiv_hasFDerivAt_base :
    HasFDerivAt (fderiv ℝ actualB) expectedHessian base :=
  actual_fderiv_hasFDerivAt_base.congr_of_eventuallyEq actualB_eventually_eq_actual.fderiv

#print axioms exp_of_cube
#print axioms canonicalOutput_formula
#print axioms actual_eventually_eq_explicit
#print axioms actual_base
#print axioms actual_hasFDerivAt_base
#print axioms actual_fderiv_hasFDerivAt_base
#print axioms actual_hessian_omega_omega
#print axioms actual_hessian_h_h
#print axioms actual_hessian_omega_h
#print axioms actual_hessian_h_omega
#print axioms canonicalOutput_eventually_eq_diagonal
#print axioms actualB_fderiv_hasFDerivAt_base

end TwoStateQuantumEmbedding.HamiltonianHessian
