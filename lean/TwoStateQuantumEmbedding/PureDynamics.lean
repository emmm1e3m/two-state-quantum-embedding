import TwoStateQuantumEmbedding.PureStationary
import TwoStateQuantumEmbedding.Duhamel
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! 一般共同暗态生成元的三角动力学与实际矩阵指数。 -/
noncomputable section
open Matrix Complex MeasureTheory
open scoped BigOperators Matrix.Norms.Operator Interval

namespace TwoStateQuantumEmbedding.PureStationary

def decayRate {n : ℕ} (y : Fin n → ℂ) : ℝ := ∑ μ, normSq (y μ)
def dephaseRate {n : ℕ} (x : Fin n → ℂ) : ℝ := ∑ μ, normSq (x μ)
def source {n : ℕ} (x y : Fin n → ℂ) : ℂ := ∑ μ, x μ * star (y μ)
def transverseRate {n : ℕ} (x y : Fin n → ℂ) : ℝ := (decayRate y + dephaseRate x) / 2
def complexRate {n : ℕ} (x y : Fin n → ℂ) (ω : ℝ) : ℂ := transverseRate x y + I * ω

theorem decayRate_nonneg {n : ℕ} (y : Fin n → ℂ) : 0 ≤ decayRate y :=
  Finset.sum_nonneg (fun μ _ => normSq_nonneg (y μ))
theorem dephaseRate_nonneg {n : ℕ} (x : Fin n → ℂ) : 0 ≤ dephaseRate x :=
  Finset.sum_nonneg (fun μ _ => normSq_nonneg (x μ))

theorem dark_dissipator_exact (x y : ℂ) (X : QubitMatrix) :
    dissipator (darkJump x y) X =
      !![-(normSq y : ℂ) * X 0 0,
          x * star y * X 0 0 - ((normSq x + normSq y : ℝ) : ℂ) / 2 * X 0 1;
          star x * y * X 0 0 - ((normSq x + normSq y : ℝ) : ℂ) / 2 * X 1 0,
          (normSq y : ℂ) * X 0 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [dissipator, darkJump, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      normSq_apply] <;> ring

theorem dark_action_exact {n : ℕ} (x y : Fin n → ℂ) (ω : ℝ) (X : QubitMatrix) :
    gkslAction (diagonalHamiltonian ω) (darkJumps x y) X =
      !![-(decayRate y : ℂ) * X 0 0,
          source x y * X 0 0 - complexRate x y ω * X 0 1;
          star (source x y) * X 0 0 - star (complexRate x y ω) * X 1 0,
          (decayRate y : ℂ) * X 0 0] := by
  simp only [gkslAction, darkJumps, dark_dissipator_exact]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [diagonalHamiltonian, decayRate, dephaseRate, source, transverseRate,
      complexRate, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.sum_apply, Finset.sum_sub_distrib, star_sum, star_mul] <;>
    simp only [add_mul, div_mul_eq_mul_div, Finset.sum_add_distrib,
      ← Finset.sum_div, ← Finset.sum_mul] <;> simp only [mul_comm] <;> ring

def stateEvaluation (X : QubitMatrix) : LiouvilleMatrix →L[ℝ] QubitMatrix :=
  (show LiouvilleMatrix →ₗ[ℝ] QubitMatrix from
    { toFun := fun M i j => (M *ᵥ (fun kl => X kl.1 kl.2)) (i, j)
      map_add' := by
        intros M N
        ext i j
        change ((M + N) *ᵥ (fun kl => X kl.1 kl.2)) (i, j) =
          (M *ᵥ (fun kl => X kl.1 kl.2)) (i, j) + (N *ᵥ (fun kl => X kl.1 kl.2)) (i, j)
        simp [Matrix.add_mulVec]
      map_smul' := by
        intros c M
        ext i j
        change ((c • M) *ᵥ (fun kl => X kl.1 kl.2)) (i, j) =
          c • (M *ᵥ (fun kl => X kl.1 kl.2)) (i, j)
        simp [Matrix.smul_mulVec] }).toContinuousLinearMap

def actualState {n : ℕ} (H : QubitMatrix) (J : Fin n → QubitMatrix)
    (X : QubitMatrix) (t : ℝ) : QubitMatrix := gkslSuperoperatorEvolution H J t X

theorem stateEvaluation_exp {n : ℕ} (H : QubitMatrix) (J : Fin n → QubitMatrix)
    (X : QubitMatrix) (t : ℝ) :
    stateEvaluation X (NormedSpace.exp (t • gkslMatrix H J)) = actualState H J X t := by
  ext i j
  exact congrFun (finiteEvolution_mulVec_eq_superoperator H J t X) (i, j)

theorem stateEvaluation_generator {n : ℕ} (H : QubitMatrix) (J : Fin n → QubitMatrix)
    (X : QubitMatrix) (M : LiouvilleMatrix) :
    stateEvaluation X (gkslMatrix H J * M) = gkslAction H J (stateEvaluation X M) := by
  ext i j
  change ((gkslMatrix H J * M) *ᵥ (fun kl => X kl.1 kl.2)) (i, j) = _
  rw [← Matrix.mulVec_mulVec]
  exact congrFun (gkslMatrix_mulVec H J (stateEvaluation X M)) (i, j)

/-- 从正式 Liouville 指数求导，未假设 ODE 解的形式。 -/
theorem actualState_hasDerivAt {n : ℕ} (H : QubitMatrix) (J : Fin n → QubitMatrix)
    (X : QubitMatrix) (t : ℝ) :
    HasDerivAt (actualState H J X) (gkslAction H J (actualState H J X t)) t := by
  have h := (stateEvaluation X).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const' (gkslMatrix H J) t)
  change HasDerivAt (fun s : ℝ => stateEvaluation X (NormedSpace.exp (s • gkslMatrix H J)))
    (stateEvaluation X (gkslMatrix H J * NormedSpace.exp (t • gkslMatrix H J))) t at h
  rw [stateEvaluation_generator] at h
  simpa only [stateEvaluation_exp] using h

theorem actualState_zero {n : ℕ} (H : QubitMatrix) (J : Fin n → QubitMatrix)
    (X : QubitMatrix) : actualState H J X 0 = X := by
  rw [← stateEvaluation_exp]
  simp only [zero_smul, NormedSpace.exp_zero]
  change (fun i j => ((1 : LiouvilleMatrix) *ᵥ (fun kl => X kl.1 kl.2)) (i, j)) = X
  simp

theorem actualState_entry_hasDerivAt {n : ℕ} (H : QubitMatrix) (J : Fin n → QubitMatrix)
    (X : QubitMatrix) (t : ℝ) (i j : Fin 2) :
    HasDerivAt (fun s => actualState H J X s i j)
      (gkslAction H J (actualState H J X t) i j) t :=
  hasDerivAt_pi.mp (hasDerivAt_pi.mp (actualState_hasDerivAt H J X t) i) j

theorem complex_exp_mul_hasDerivAt (a : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (a * s)) (a * Complex.exp (a * t)) t := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul a).cexp
  simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one, mul_comm] using h

theorem scalar_decay_solution (a : ℂ) (u : ℝ → ℂ)
    (hu : ∀ t, HasDerivAt u (-a * u t) t) (t : ℝ) :
    u t = Complex.exp (-a * t) * u 0 := by
  have hzero (s : ℝ) : HasDerivAt (fun r : ℝ => Complex.exp (a * r) * u r) 0 s := by
    convert (complex_exp_mul_hasDerivAt a s).mul (hu s) using 1
    ring
  have hc := is_const_of_deriv_eq_zero (fun s => (hzero s).differentiableAt)
    (fun s => (hzero s).deriv) t 0
  have he : Complex.exp (a * t) * u t = u 0 := by simpa using hc
  have hmul := congrArg (fun z => Complex.exp (-a * t) * z) he
  have hexp : Complex.exp (-a * t) * Complex.exp (a * t) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 1
    ring
  simpa only [← mul_assoc, hexp, one_mul] using hmul

def interferenceKernel (a b : ℂ) (t : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..t, Complex.exp (-b * (t - s)) * Complex.exp (-a * s)

theorem scalar_forced_solution (a b C : ℂ) (u z : ℝ → ℂ)
    (hu : ∀ t, HasDerivAt u (-a * u t) t)
    (hz : ∀ t, HasDerivAt z (C * u t - b * z t) t) (t : ℝ) :
    z t = Complex.exp (-b * t) * z 0 + C * u 0 * interferenceKernel a b t := by
  have hu' (s : ℝ) := scalar_decay_solution a u hu s
  have hprod (s : ℝ) : HasDerivAt (fun r : ℝ => Complex.exp (b * r) * z r)
      (C * u 0 * (Complex.exp (b * s) * Complex.exp (-a * s))) s := by
    convert (complex_exp_mul_hasDerivAt b s).mul (hz s) using 1
    rw [hu' s]
    ring
  have hc : Continuous (fun s : ℝ => C * u 0 * (Complex.exp (b * s) * Complex.exp (-a * s))) := by
    fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := t) (fun s _ => hprod s) (hc.intervalIntegrable 0 t)
  have hexp : Complex.exp (-b * t) * Complex.exp (b * t) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 1
    ring
  have hm := congrArg (fun w => Complex.exp (-b * t) * w) hi
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, mul_sub,
    ← mul_assoc, hexp] at hm
  rw [← intervalIntegral.integral_const_mul] at hm
  have hk : (∫ s in (0 : ℝ)..t, Complex.exp (-b * t) *
      (C * u 0 * (Complex.exp (b * s) * Complex.exp (-a * s)))) =
      C * u 0 * interferenceKernel a b t := by
    unfold interferenceKernel
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    have hfactor : Complex.exp (-b * t) * Complex.exp (b * s) =
        Complex.exp (-b * (t - s)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    calc
      _ = C * u 0 * ((Complex.exp (-b * t) * Complex.exp (b * s)) * Complex.exp (-a * s)) := by ring
      _ = _ := by rw [hfactor]
  simp only [mul_assoc] at hm hk
  rw [hk] at hm
  linear_combination -hm

theorem source_norm_le {n : ℕ} (x y : Fin n → ℂ) :
    ‖source x y‖ ≤ Real.sqrt (dephaseRate x) * Real.sqrt (decayRate y) := by
  calc
    ‖source x y‖ ≤ ∑ μ, ‖x μ * star (y μ)‖ := norm_sum_le _ _
    _ = ∑ μ, ‖x μ‖ * ‖y μ‖ := by simp
    _ ≤ Real.sqrt (dephaseRate x) * Real.sqrt (decayRate y) := by
      simpa [dephaseRate, decayRate, Complex.normSq_eq_norm_sq] using
        Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun μ => ‖x μ‖) (fun μ => ‖y μ‖)

theorem source_normSq_le {n : ℕ} (x y : Fin n → ℂ) :
    normSq (source x y) ≤ decayRate y * dephaseRate x := by
  have h := sq_le_sq₀ (norm_nonneg (source x y))
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) |>.mpr (source_norm_le x y)
  rw [mul_pow, Real.sq_sqrt (dephaseRate_nonneg x), Real.sq_sqrt (decayRate_nonneg y)] at h
  simpa [Complex.normSq_eq_norm_sq, mul_comm] using h

def realInterferenceKernel (a b t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, Real.exp (-b * (t - s)) * Real.exp (-a * s)

theorem interferenceKernel_norm_le (a γ ω t : ℝ) (ht : 0 ≤ t) :
    ‖interferenceKernel (a : ℂ) (γ + I * ω) t‖ ≤ realInterferenceKernel a γ t := by
  calc
    _ ≤ ∫ s in (0 : ℝ)..t,
      ‖Complex.exp (-(γ + I * ω) * (t - s)) * Complex.exp (-(a : ℂ) * s)‖ :=
        intervalIntegral.norm_integral_le_integral_norm ht
    _ = realInterferenceKernel a γ t := by
      apply intervalIntegral.integral_congr
      intro s _
      simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- 任意初始矩阵的三角流；共振时仍使用同一个积分公式。 -/
def darkFlow {n : ℕ} (x y : Fin n → ℂ) (ω : ℝ) (X : QubitMatrix) (t : ℝ) : QubitMatrix :=
  let F := Complex.exp (-(decayRate y : ℂ) * t)
  let b := complexRate x y ω
  !![F * X 0 0,
     Complex.exp (-b * t) * X 0 1 + source x y * X 0 0 * interferenceKernel (decayRate y) b t;
     Complex.exp (-star b * t) * X 1 0 + star (source x y) * X 0 0 *
       interferenceKernel (decayRate y) (star b) t,
     X 1 1 + (1 - F) * X 0 0]

theorem triangular_flow_solution {n : ℕ} (x y : Fin n → ℂ) (ω : ℝ)
    (f : ℝ → QubitMatrix)
    (hf : ∀ t, HasDerivAt f (gkslAction (diagonalHamiltonian ω) (darkJumps x y) (f t)) t)
    (t : ℝ) : f t = darkFlow x y ω (f 0) t := by
  have he (s : ℝ) (i j : Fin 2) :=
    hasDerivAt_pi.mp (hasDerivAt_pi.mp (hf s) i) j
  have hu (s : ℝ) : HasDerivAt (fun r => f r 0 0) (-(decayRate y : ℂ) * f s 0 0) s := by
    simpa [dark_action_exact] using he s 0 0
  have hz (s : ℝ) : HasDerivAt (fun r => f r 0 1)
      (source x y * f s 0 0 - complexRate x y ω * f s 0 1) s := by
    simpa using he s 0 1 |>.congr_deriv (by simp [dark_action_exact])
  have hw (s : ℝ) : HasDerivAt (fun r => f r 1 0)
      (star (source x y) * f s 0 0 - star (complexRate x y ω) * f s 1 0) s := by
    simpa using he s 1 0 |>.congr_deriv (by simp [dark_action_exact])
  have htr (s : ℝ) : HasDerivAt (fun r => f r 0 0 + f r 1 1) 0 s := by
    convert (he s 0 0).add (he s 1 1) using 1
    simp [dark_action_exact]
  have hconst := is_const_of_deriv_eq_zero (fun s => (htr s).differentiableAt)
    (fun s => (htr s).deriv) t 0
  have huu := scalar_decay_solution (decayRate y) (fun r => f r 0 0) hu t
  have hzz := scalar_forced_solution (decayRate y) (complexRate x y ω) (source x y)
    (fun r => f r 0 0) (fun r => f r 0 1) hu hz t
  have hww := scalar_forced_solution (decayRate y) (star (complexRate x y ω)) (star (source x y))
    (fun r => f r 0 0) (fun r => f r 1 0) hu hw t
  ext i j; fin_cases i <;> fin_cases j
  · exact huu
  · exact hzz
  · exact hww
  · change f t 1 1 = f 0 1 1 +
      (1 - Complex.exp (-(decayRate y : ℂ) * t)) * f 0 0 0
    linear_combination hconst - huu

theorem actual_dark_flow {n : ℕ} (x y : Fin n → ℂ) (ω : ℝ) (X : QubitMatrix) (t : ℝ) :
    actualState (diagonalHamiltonian ω) (darkJumps x y) X t = darkFlow x y ω X t := by
  simpa only [actualState_zero] using triangular_flow_solution x y ω
    (actualState (diagonalHamiltonian ω) (darkJumps x y) X)
    (actualState_hasDerivAt (diagonalHamiltonian ω) (darkJumps x y) X) t

def conjugateCLM (U : QubitMatrix) : QubitMatrix →L[ℝ] QubitMatrix :=
  (show QubitMatrix →ₗ[ℝ] QubitMatrix from
    { toFun := conjugate U
      map_add' := by intros X Y; simp [conjugate, mul_add, add_mul]
      map_smul' := by intros c X; simp [conjugate] }).toContinuousLinearMap

theorem actual_flow_of_normal_form {n : ℕ} (H : QubitMatrix) (J : Fin n → QubitMatrix)
    (U : QubitMatrix) (ω : ℝ) (x y : Fin n → ℂ)
    (hU : Uᴴ * U = 1) (hUU : U * Uᴴ = 1)
    (hL : ∀ X, gkslAction H J (conjugate U X) =
      conjugate U (gkslAction (diagonalHamiltonian ω) (darkJumps x y) X))
    (X : QubitMatrix) (t : ℝ) :
    actualState H J (conjugate U X) t = conjugate U (darkFlow x y ω X t) := by
  let f := fun s => conjugate Uᴴ (actualState H J (conjugate U X) s)
  have hback (Z : QubitMatrix) : conjugate U (conjugate Uᴴ Z) = Z := by
    simpa using conjugate_inverse Uᴴ Z (by simpa using hUU)
  have hderiv (s : ℝ) : HasDerivAt f
      (gkslAction (diagonalHamiltonian ω) (darkJumps x y) (f s)) s := by
    have hd := (conjugateCLM Uᴴ).hasFDerivAt.comp_hasDerivAt s
      (actualState_hasDerivAt H J (conjugate U X) s)
    have hl := hL (f s)
    rw [show conjugate U (f s) = actualState H J (conjugate U X) s from hback _] at hl
    change HasDerivAt f (conjugate Uᴴ (gkslAction H J (actualState H J (conjugate U X) s))) s at hd
    rw [hl, conjugate_inverse U _ hU] at hd
    exact hd
  have hzero : f 0 = X := by simp only [f, actualState_zero, conjugate_inverse U X hU]
  have hsol := triangular_flow_solution x y ω f hderiv t
  rw [hzero] at hsol
  have hconj := congrArg (conjugate U) hsol
  simpa only [f, hback] using hconj

/-- 从原始任意纯稳态条件得到实际 GKSL 指数的完整三角解。 -/
theorem pure_stationary_actual_flow {n : ℕ} (H : QubitMatrix) (hH : H.IsHermitian)
    (J : Fin n → QubitMatrix) (g : Fin 2 → ℂ)
    (hg : normSq (g 0) + normSq (g 1) = 1)
    (hs : gkslAction H J (pureProjector g) = 0) :
    ∃ U : QubitMatrix, ∃ ω : ℝ, ∃ x y : Fin n → ℂ,
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ pureProjector g = conjugate U ground ∧
      ∀ (X : QubitMatrix) (t : ℝ),
        actualState H J X t = conjugate U (darkFlow x y ω (conjugate Uᴴ X) t) := by
  obtain ⟨U, ω, x, y, hU, hUU, hgU, hL⟩ := pure_stationary_normal_form H hH J g hg hs
  refine ⟨U, ω, x, y, hU, hUU, hgU, ?_⟩
  intro X t
  have h := actual_flow_of_normal_form H J U ω x y hU hUU hL (conjugate Uᴴ X) t
  have hback : conjugate U (conjugate Uᴴ X) = X := by
    simpa using conjugate_inverse Uᴴ X (by simpa using hUU)
  simpa only [hback] using h

end TwoStateQuantumEmbedding.PureStationary

#print axioms TwoStateQuantumEmbedding.PureStationary.dark_action_exact
#print axioms TwoStateQuantumEmbedding.PureStationary.actual_dark_flow
#print axioms TwoStateQuantumEmbedding.PureStationary.pure_stationary_actual_flow
#print axioms TwoStateQuantumEmbedding.PureStationary.source_normSq_le
#print axioms TwoStateQuantumEmbedding.PureStationary.interferenceKernel_norm_le

