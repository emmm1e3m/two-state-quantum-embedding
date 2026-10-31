import TwoStateQuantumEmbedding.PureDynamics
import TwoStateQuantumEmbedding.CPTP

/-! 有限跳跃的混合稳态坐标：实际 GKSL 作用、稳态约束及测量。 -/
noncomputable section
open Matrix Complex
open scoped BigOperators ComplexOrder
namespace TwoStateQuantumEmbedding.ResetMixed
open GKSLAlgebra
set_option maxRecDepth 3000
set_option maxHeartbeats 1800000

def jump (x y z : ℂ) : QubitMatrix := !![x, y; z, 0]
def jumps {n : ℕ} (x y z : Fin n → ℂ) : Fin n → QubitMatrix :=
  fun μ => jump (x μ) (y μ) (z μ)
def hamiltonian (ω : ℝ) (h : ℂ) : QubitMatrix := !![(ω / 2 : ℂ), h; star h, -(ω / 2)]
def state (t u : ℝ) (c : ℂ) : QubitMatrix := !![(u : ℂ), c; star c, ((t-u : ℝ) : ℂ)]
def rate {n : ℕ} (x : Fin n → ℂ) : ℝ := ∑ μ, normSq (x μ)
def coeffC {n : ℕ} (x z : Fin n → ℂ) : ℂ := ∑ μ, x μ * star (z μ)
def coeffD {n : ℕ} (x y : Fin n → ℂ) : ℂ := ∑ μ, star (x μ) * y μ
def coeffE {n : ℕ} (y z : Fin n → ℂ) : ℂ := ∑ μ, y μ * star (z μ)
def gamma {n : ℕ} (x y z : Fin n → ℂ) : ℝ := (rate z + rate x + rate y) / 2

theorem dissipator_00 (x y z : ℂ) (X : QubitMatrix) :
    dissipator (jump x y z) X 0 0 =
      -(normSq z : ℂ) * X 0 0 + (normSq y : ℂ) * X 1 1 +
      (star x * y * X 1 0 + x * star y * X 0 1) / 2 := by
  apply Complex.ext <;>
    simp [dissipator, jump, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im, normSq_apply] <;> ring

theorem dissipator_01 (x y z : ℂ) (X : QubitMatrix) :
    dissipator (jump x y z) X 0 1 =
      x * star z * X 0 0 - (star x * y) / 2 * (X 0 0 + X 1 1) +
      y * star z * X 1 0 - ((normSq z + normSq x + normSq y : ℝ) : ℂ) / 2 * X 0 1 := by
  apply Complex.ext <;>
    simp [dissipator, jump, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im, normSq_apply] <;> ring

theorem action_00 {n : ℕ} (x y z : Fin n → ℂ) (ω : ℝ) (h : ℂ) (X : QubitMatrix) :
    gkslAction (hamiltonian ω h) (jumps x y z) X 0 0 =
      -(rate z : ℂ) * X 0 0 + (rate y : ℂ) * X 1 1 +
      (coeffD x y * X 1 0 + star (coeffD x y) * X 0 1) / 2 -
      I * (h * X 1 0 - star h * X 0 1) := by
  simp only [gkslAction, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.sum_apply, jumps, dissipator_00]
  simp [hamiltonian, rate, coeffD, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_div,
    ← Finset.sum_mul, star_sum, star_mul]
  simp only [add_mul, div_mul_eq_mul_div, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul]
  simp only [mul_comm]
  ring

theorem action_01 {n : ℕ} (x y z : Fin n → ℂ) (ω : ℝ) (h : ℂ) (X : QubitMatrix) :
    gkslAction (hamiltonian ω h) (jumps x y z) X 0 1 =
      (coeffC x z + 2 * I * h) * X 0 0 -
      (coeffD x y / 2 + I * h) * (X 0 0 + X 1 1) + coeffE y z * X 1 0 -
      ((gamma x y z : ℂ) + I * ω) * X 0 1 := by
  simp only [gkslAction, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.sum_apply, jumps, dissipator_01]
  simp [hamiltonian, rate, coeffC, coeffD, coeffE, gamma, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Fin.sum_univ_two, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_div, ← Finset.sum_mul]
  simp only [add_mul, div_mul_eq_mul_div, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul]
  simp only [mul_comm]
  ring





theorem action_population_raw {n : ℕ} (x y z : Fin n → ℂ) (ω t u : ℝ) (h c : ℂ) :
    (gkslAction (hamiltonian ω h) (jumps x y z) (state t u c) 0 0).re =
      -rate z * u + rate y * (t-u) + ((coeffD x y - 2*I*h) * star c).re := by
  rw [action_00]
  simp [state, Complex.mul_re, Complex.mul_im]
  ring

theorem action_coherence_raw {n : ℕ} (x y z : Fin n → ℂ) (ω t u : ℝ) (h c : ℂ) :
    gkslAction (hamiltonian ω h) (jumps x y z) (state t u c) 0 1 =
      (coeffC x z + 2*I*h) * u - (coeffD x y / 2 + I*h) * t +
      coeffE y z * star c - ((gamma x y z : ℂ) + I*ω) * c := by
  rw [action_01]
  simp [state]

theorem stationary_population {n : ℕ} (x y z : Fin n → ℂ) (ω ν : ℝ) (h : ℂ)
    (hs : gkslAction (hamiltonian ω h) (jumps x y z) (state 1 ν 0) = 0) :
    rate y * (1-ν) = rate z * ν := by
  have he := congrArg (fun X : QubitMatrix => (X 0 0).re) hs
  rw [action_population_raw] at he
  simp at he
  linarith

theorem stationary_coherence {n : ℕ} (x y z : Fin n → ℂ) (ω ν : ℝ) (h : ℂ)
    (hs : gkslAction (hamiltonian ω h) (jumps x y z) (state 1 ν 0) = 0) :
    I*h * (1-2*(ν : ℂ)) = (ν : ℂ)*coeffC x z - coeffD x y / 2 := by
  have he := congrArg (fun X : QubitMatrix => X 0 1) hs
  rw [action_coherence_raw] at he
  simp at he
  linear_combination -he

theorem stationary_U {n : ℕ} (x y z : Fin n → ℂ) (ω ν : ℝ) (h : ℂ)
    (hs : gkslAction (hamiltonian ω h) (jumps x y z) (state 1 ν 0) = 0)
    (hν : ν ≠ 1) : rate y = rate z * ν / (1-ν) := by
  apply (eq_div_iff (sub_ne_zero.mpr (Ne.symm hν))).mpr
  exact stationary_population x y z ω ν h hs

theorem stationary_h {n : ℕ} (x y z : Fin n → ℂ) (ω ν : ℝ) (h : ℂ)
    (hs : gkslAction (hamiltonian ω h) (jumps x y z) (state 1 ν 0) = 0)
    (hν : 1-2*ν ≠ 0) :
    h = -I*((ν : ℂ)*coeffC x z - coeffD x y / 2) / (1-2*(ν : ℂ)) := by
  have hd : (1-2*(ν : ℂ)) ≠ 0 := by exact_mod_cast hν
  apply (eq_div_iff hd).mpr
  rw [← stationary_coherence x y z ω ν h hs]
  ring_nf
  simp [I_sq] <;> ring

def cTilde {n : ℕ} (x y z : Fin n → ℂ) (ν : ℝ) : ℂ :=
  (coeffC x z - coeffD x y) / (1-2*(ν : ℂ))
def feedback {n : ℕ} (x y z : Fin n → ℂ) (ν : ℝ) : ℂ :=
  2*((1-(ν : ℂ))*coeffD x y - (ν : ℂ)*coeffC x z) / (1-2*(ν : ℂ))

theorem stationary_coefficients {n : ℕ} (x y z : Fin n → ℂ) (ω ν : ℝ) (h : ℂ)
    (hs : gkslAction (hamiltonian ω h) (jumps x y z) (state 1 ν 0) = 0)
    (hν : 1-2*ν ≠ 0) :
    coeffC x z + 2*I*h = cTilde x y z ν ∧
    coeffD x y - 2*I*h = feedback x y z ν := by
  have hd : (1-2*(ν : ℂ)) ≠ 0 := by exact_mod_cast hν
  have he := stationary_coherence x y z ω ν h hs
  constructor <;> dsimp only [cTilde, feedback] <;> apply (eq_div_iff hd).mpr
  · linear_combination 2*he
  · linear_combination -2*he

theorem action_population {n : ℕ} (x y z : Fin n → ℂ) (ω ν u : ℝ) (h c : ℂ)
    (hs : gkslAction (hamiltonian ω h) (jumps x y z) (state 1 ν 0) = 0)
    (hν : 1-2*ν ≠ 0) :
    (gkslAction (hamiltonian ω h) (jumps x y z) (state 0 u c) 0 0).re =
      -(rate z + rate y)*u + (feedback x y z ν * star c).re := by
  rw [action_population_raw, (stationary_coefficients x y z ω ν h hs hν).2]
  ring

theorem action_coherence {n : ℕ} (x y z : Fin n → ℂ) (ω ν u : ℝ) (h c : ℂ)
    (hs : gkslAction (hamiltonian ω h) (jumps x y z) (state 1 ν 0) = 0)
    (hν : 1-2*ν ≠ 0) :
    gkslAction (hamiltonian ω h) (jumps x y z) (state 0 u c) 0 1 =
      cTilde x y z ν * u + coeffE y z * star c - ((gamma x y z : ℂ) + I*ω)*c := by
  rw [action_coherence_raw, (stationary_coefficients x y z ω ν h hs hν).1]
  simp

theorem rate_nonneg {n : ℕ} (x : Fin n → ℂ) : 0 ≤ rate x :=
  Finset.sum_nonneg (fun μ _ => normSq_nonneg (x μ))

theorem coeffC_bound {n : ℕ} (x z : Fin n → ℂ) :
    ‖coeffC x z‖ ≤ Real.sqrt (rate x * rate z) := by
  calc
    ‖coeffC x z‖ ≤ Real.sqrt (rate x) * Real.sqrt (rate z) := by
      exact PureStationary.source_norm_le x z
    _ = Real.sqrt (rate x * rate z) := (Real.sqrt_mul (rate_nonneg x) _).symm

theorem coeffD_bound {n : ℕ} (x y : Fin n → ℂ) :
    ‖coeffD x y‖ ≤ Real.sqrt (rate x * rate y) := by
  have he : coeffD x y = coeffC y x := by simp [coeffD, coeffC, mul_comm]
  rw [he, mul_comm (rate x)]
  exact coeffC_bound y x

theorem coeffE_bound {n : ℕ} (y z : Fin n → ℂ) :
    ‖coeffE y z‖ ≤ Real.sqrt (rate z * rate y) := by
  simpa only [coeffE, coeffC, mul_comm (rate y)] using coeffC_bound y z

def measurement (p w : ℝ) : QubitMatrix := !![((1-p : ℝ) : ℂ), (w/2 : ℂ); (w/2 : ℂ), (p : ℂ)]

theorem preparation_difference (p w : ℝ) :
    measurement p w - (1 - measurement p w) = state 0 (1-2*p) w := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [measurement, state] <;> ring

theorem readout (p w u : ℝ) (c : ℂ) :
    ((measurement p w * state 0 u c).trace).re = (1-2*p)*u + w*c.re := by
  simp [measurement, state, Matrix.trace, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Fin.sum_univ_two, Complex.mul_re]
  ring


theorem shifted_jump_form {n : ℕ} (J : Fin n → QubitMatrix) :
    PureStationary.shiftedJumps J =
      jumps (fun μ => J μ 0 0 - J μ 1 1) (fun μ => J μ 0 1) (fun μ => J μ 1 0) := by
  funext μ
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [PureStationary.shiftedJumps, jumps, jump]

theorem hamiltonian_decomposition (H : QubitMatrix) (hH : H.IsHermitian) :
    (((H 0 0).re + (H 1 1).re) / 2 : ℂ) • (1 : QubitMatrix) +
      hamiltonian ((H 0 0).re - (H 1 1).re) (H 0 1) = H := by
  have h00 := congrArg Complex.im (hH.apply 0 0)
  have h11 := congrArg Complex.im (hH.apply 1 1)
  have h10 := hH.apply 1 0
  simp only [Complex.star_def, Complex.conj_im] at h00 h11
  have hi00 : (H 0 0).im = 0 := by linarith
  have hi11 : (H 1 1).im = 0 := by linarith
  have hz10 : H 1 0 = star (H 0 1) := h10.symm
  ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [hamiltonian, Matrix.smul_apply, smul_eq_mul, hi00, hi11, hz10] <;> ring

/-- 对任意有限原跳跃的固定基规范，等式对所有矩阵输入成立。 -/
theorem normal_form {n : ℕ} (H : QubitMatrix) (hH : H.IsHermitian)
    (J : Fin n → QubitMatrix) :
    ∃ (ω : ℝ) (h : ℂ) (x y z : Fin n → ℂ), ∀ X : QubitMatrix,
      gkslAction H J X = gkslAction (hamiltonian ω h) (jumps x y z) X := by
  let H' := PureStationary.shiftedHamiltonian H J
  have hH' : H'.IsHermitian := PureStationary.shifted_hermitian H hH J
  refine ⟨(H' 0 0).re - (H' 1 1).re, H' 0 1,
    (fun μ => J μ 0 0 - J μ 1 1), (fun μ => J μ 0 1), (fun μ => J μ 1 0), ?_⟩
  intro X
  rw [PureStationary.shifted_action, shifted_jump_form]
  change gkslAction H' _ X = _
  conv_lhs => rw [← hamiltonian_decomposition H' hH']
  exact GKSLAlgebra.scalar_hamiltonian_irrelevant _ _ _ _

/-- 固定基对角稳态随规范严格保留。 -/
theorem stationary_normal_form {n : ℕ} (H : QubitMatrix) (hH : H.IsHermitian)
    (J : Fin n → QubitMatrix) (ν : ℝ) (hs : gkslAction H J (state 1 ν 0) = 0) :
    ∃ (ω : ℝ) (h : ℂ) (x y z : Fin n → ℂ),
      (∀ X : QubitMatrix, gkslAction H J X = gkslAction (hamiltonian ω h) (jumps x y z) X) ∧
      gkslAction (hamiltonian ω h) (jumps x y z) (state 1 ν 0) = 0 := by
  obtain ⟨ω, h, x, y, z, he⟩ := normal_form H hH J
  exact ⟨ω,h,x,y,z,he, by rw [← he]; exact hs⟩

/-- 无需选择联合可达的最坏相位，逐项 Cauchy 界即足够。 -/
theorem scaled_gram_bounds {n : ℕ} (x y z : Fin n → ℂ) (χ : ℝ) (hχ : 0 ≤ χ)
    (hU : rate y = rate z * χ^2) :
    ‖coeffC x z‖ ≤ Real.sqrt (rate z * rate x) ∧
    ‖coeffD x y‖ ≤ χ * Real.sqrt (rate z * rate x) ∧
    ‖coeffE y z‖ ≤ rate z * χ := by
  have hA := rate_nonneg z
  have hB := rate_nonneg x
  refine ⟨?_, ?_, ?_⟩
  · simpa [mul_comm (rate z)] using coeffC_bound x z
  · have hD := coeffD_bound x y
    rw [hU] at hD
    have he : rate x * (rate z * χ^2) = (rate z * rate x) * χ^2 := by ring
    rw [he, Real.sqrt_mul (mul_nonneg hA hB), Real.sqrt_sq hχ] at hD
    simpa [mul_comm] using hD
  · have hE := coeffE_bound y z
    rw [hU] at hE
    have he : rate z * (rate z * χ^2) = (rate z * χ)^2 := by ring
    rw [he, Real.sqrt_sq (mul_nonneg hA hχ)] at hE
    exact hE

def chi (ν : ℝ) : ℝ := Real.sqrt (ν/(1-ν))
def alpha {n : ℕ} (z : Fin n → ℂ) (χ : ℝ) : ℝ := rate z*(1+χ^2)
def lam {n : ℕ} (x z : Fin n → ℂ) (χ : ℝ) : ℝ := (rate z*(1-χ)^2+rate x)/2
def cBound {n : ℕ} (x z : Fin n → ℂ) (χ : ℝ) : ℝ :=
  Real.sqrt (rate z*rate x)*(1+χ^2)/(1-χ)
def rBound {n : ℕ} (x z : Fin n → ℂ) (χ : ℝ) : ℝ :=
  2*χ*Real.sqrt (rate z*rate x)/(1-χ)

theorem chi_properties (ν : ℝ) (hν0 : 0 ≤ ν) (hν : ν < 1/2) :
    0 ≤ chi ν ∧ chi ν < 1 ∧ (chi ν)^2 = ν/(1-ν) ∧
    ν = (chi ν)^2/(1+(chi ν)^2) := by
  have hden : 0 < 1-ν := by linarith
  have hn := div_nonneg hν0 (le_of_lt hden)
  have hs : (chi ν)^2 = ν/(1-ν) := Real.sq_sqrt hn
  have hc0 : 0 ≤ chi ν := Real.sqrt_nonneg _
  have hc1 : chi ν < 1 := by
    have hfrac : ν/(1-ν) < 1 := (div_lt_one hden).mpr (by linarith)
    nlinarith [sq_nonneg (chi ν - 1)]
  refine ⟨hc0,hc1,hs,?_⟩
  apply (eq_div_iff (by positivity : 1+(chi ν)^2 ≠ 0)).mpr
  rw [hs]
  field_simp [ne_of_gt hden]
  <;> ring

theorem stationary_scaled_U {n : ℕ} (x y z : Fin n → ℂ) (ω ν : ℝ) (h : ℂ)
    (hs : gkslAction (hamiltonian ω h) (jumps x y z) (state 1 ν 0) = 0)
    (hν0 : 0 ≤ ν) (hν : ν < 1/2) : rate y = rate z * (chi ν)^2 := by
  rw [(chi_properties ν hν0 hν).2.2.1]
  rw [stationary_U x y z ω ν h hs (by linarith)]
  ring
theorem feedback_alt {n : ℕ} (x y z : Fin n → ℂ) (ν : ℝ) (hd : 1-2*ν ≠ 0) :
    feedback x y z ν = 2*coeffD x y - 2*(ν : ℂ)*cTilde x y z ν := by
  have hd' : 1-2*(ν : ℂ) ≠ 0 := by exact_mod_cast hd
  unfold feedback cTilde
  field_simp [hd']
  <;> ring

theorem coefficient_bounds {n : ℕ} (x y z : Fin n → ℂ) (ν χ : ℝ)
    (hχ0 : 0 ≤ χ) (hχ1 : χ < 1) (hν : ν = χ^2/(1+χ^2))
    (hU : rate y = rate z*χ^2) :
    lam x z χ ≤ gamma x y z - ‖coeffE y z‖ ∧
    ‖cTilde x y z ν‖ ≤ cBound x z χ ∧
    ‖feedback x y z ν‖ ≤ rBound x z χ := by
  obtain ⟨hC,hD,hE⟩ := scaled_gram_bounds x y z χ hχ0 hU
  have hdχ : 0 < 1-χ := by linarith
  have hp : 0 < 1+χ^2 := by positivity
  have hden : 0 < 1-2*ν := by
    have he : 1-2*ν = (1-χ^2)/(1+χ^2) := by rw [hν]; field_simp; ring
    rw [he]
    apply div_pos _ hp
    nlinarith
  have hν0 : 0 ≤ ν := by rw [hν]; positivity
  have hc : ‖cTilde x y z ν‖ ≤ cBound x z χ := by
    unfold cTilde
    rw [norm_div]
    have he : 1-2*(ν : ℂ) = ((1-2*ν : ℝ) : ℂ) := by push_cast; ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden]
    apply (div_le_iff₀ hden).mpr
    calc
      ‖coeffC x z - coeffD x y‖ ≤ ‖coeffC x z‖ + ‖coeffD x y‖ := norm_sub_le _ _
      _ ≤ Real.sqrt (rate z*rate x) + χ*Real.sqrt (rate z*rate x) := add_le_add hC hD
      _ = cBound x z χ*(1-2*ν) := by
        unfold cBound
        rw [hν]
        field_simp
        <;> ring
  refine ⟨?_,hc,?_⟩
  · unfold lam gamma
    rw [hU]
    nlinarith
  · rw [feedback_alt x y z ν (ne_of_gt hden)]
    calc
      ‖2*coeffD x y - 2*(ν : ℂ)*cTilde x y z ν‖ ≤
          ‖2*coeffD x y‖ + ‖2*(ν : ℂ)*cTilde x y z ν‖ := norm_sub_le _ _
      _ = 2*‖coeffD x y‖ + 2*ν*‖cTilde x y z ν‖ := by
        simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hν0]
      _ ≤ 2*(χ*Real.sqrt (rate z*rate x)) + 2*ν*cBound x z χ := by
        gcongr
      _ = rBound x z χ := by
        unfold cBound rBound
        rw [hν]
        field_simp
        <;> ring

theorem stationary_coefficient_bounds {n : ℕ} (x y z : Fin n → ℂ) (ω ν : ℝ) (h : ℂ)
    (hs : gkslAction (hamiltonian ω h) (jumps x y z) (state 1 ν 0) = 0)
    (hν0 : 0 ≤ ν) (hν : ν < 1/2) :
    lam x z (chi ν) ≤ gamma x y z - ‖coeffE y z‖ ∧
    ‖cTilde x y z ν‖ ≤ cBound x z (chi ν) ∧
    ‖feedback x y z ν‖ ≤ rBound x z (chi ν) := by
  obtain ⟨hc0,hc1,_,hv⟩ := chi_properties ν hν0 hν
  exact coefficient_bounds x y z ν (chi ν) hc0 hc1 hv
    (stationary_scaled_U x y z ω ν h hs hν0 hν)



theorem normSq_coe (c : ℂ) : (normSq c : ℂ) = c*star c := by
  apply Complex.ext <;> simp [normSq_apply, Complex.mul_re, Complex.mul_im] <;> ring

def gram {n : ℕ} (x y z : Fin n → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  ∑ μ, Matrix.vecMulVec ![x μ,y μ,z μ] (star ![x μ,y μ,z μ])

theorem gram_posSemidef {n : ℕ} (x y z : Fin n → ℂ) : (gram x y z).PosSemidef :=
  Matrix.posSemidef_sum _ (fun μ _ => Matrix.posSemidef_vecMulVec_self_star _)

theorem gram_eq {n : ℕ} (x y z : Fin n → ℂ) : gram x y z =
    !![(rate x : ℂ), star (coeffD x y), coeffC x z;
       coeffD x y, (rate y : ℂ), coeffE y z;
       star (coeffC x z), star (coeffE y z), (rate z : ℂ)] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [gram, Matrix.vecMulVec, Matrix.sum_apply, rate, coeffC, coeffD, coeffE,
      normSq_coe, star_sum, star_mul, mul_comm]

theorem state_of_hermitian_trace_zero (X : QubitMatrix) (hX : X.IsHermitian)
    (ht : X.trace = 0) : X = state 0 (X 0 0).re (X 0 1) := by
  have h00 := congrArg Complex.im (hX.apply 0 0)
  simp only [Complex.star_def, Complex.conj_im] at h00
  have hi00 : (X 0 0).im = 0 := by linarith
  have hr00 : X 0 0 = ((X 0 0).re : ℂ) := by apply Complex.ext <;> simp [hi00]
  have h10 : X 1 0 = star (X 0 1) := (hX.apply 1 0).symm
  have htr : X 0 0 + X 1 1 = 0 := by simpa [Matrix.trace, Fin.sum_univ_two] using ht
  have h11 : X 1 1 = -((X 0 0).re : ℂ) := by rw [hr00] at htr; linear_combination htr
  ext i j; fin_cases i <;> fin_cases j <;> simp [state, h10, h11]
  exact hr00

theorem hamiltonian_isHermitian (ω : ℝ) (h : ℂ) : (hamiltonian ω h).IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [hamiltonian, Matrix.conjTranspose_apply]

def population {n : ℕ} (H : QubitMatrix) (J : Fin n → QubitMatrix) (X : QubitMatrix)
    (t : ℝ) : ℝ := (PureStationary.actualState H J X t 0 0).re
def coherence {n : ℕ} (H : QubitMatrix) (J : Fin n → QubitMatrix) (X : QubitMatrix)
    (t : ℝ) : ℂ := PureStationary.actualState H J X t 0 1

theorem actual_state_shape {n : ℕ} (H : QubitMatrix) (J : Fin n → QubitMatrix)
    (hH : H.IsHermitian) (X : QubitMatrix) (hX : X.IsHermitian) (htr : X.trace = 0)
    (t : ℝ) (ht : 0 ≤ t) :
    PureStationary.actualState H J X t = state 0 (population H J X t) (coherence H J X t) := by
  apply state_of_hermitian_trace_zero
  · exact (gkslSuperoperatorEvolution_isChannel H J t hH ht).pos.map_isHermitian hX
  · change (gkslSuperoperatorEvolution H J t X).trace = 0
    rw [gkslSuperoperatorEvolution_trace H J t hH ht, htr]

theorem actual_population_hasDerivAt {n : ℕ} (x y z : Fin n → ℂ) (ω ν : ℝ) (h : ℂ)
    (hs : gkslAction (hamiltonian ω h) (jumps x y z) (state 1 ν 0) = 0)
    (hν : 1-2*ν ≠ 0) (X : QubitMatrix) (hX : X.IsHermitian) (htr : X.trace = 0)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (population (hamiltonian ω h) (jumps x y z) X)
      (-(rate z+rate y)*population (hamiltonian ω h) (jumps x y z) X t +
        (feedback x y z ν * star (coherence (hamiltonian ω h) (jumps x y z) X t)).re) t := by
  have hd := PureStationary.actualState_entry_hasDerivAt (hamiltonian ω h) (jumps x y z) X t 0 0
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd
  change HasDerivAt (population (hamiltonian ω h) (jumps x y z) X)
    (gkslAction (hamiltonian ω h) (jumps x y z)
      (PureStationary.actualState (hamiltonian ω h) (jumps x y z) X t) 0 0).re t at hr
  rw [actual_state_shape _ _ (hamiltonian_isHermitian ω h) X hX htr t ht,
    action_population x y z ω ν _ h _ hs hν] at hr
  exact hr

theorem actual_coherence_hasDerivAt {n : ℕ} (x y z : Fin n → ℂ) (ω ν : ℝ) (h : ℂ)
    (hs : gkslAction (hamiltonian ω h) (jumps x y z) (state 1 ν 0) = 0)
    (hν : 1-2*ν ≠ 0) (X : QubitMatrix) (hX : X.IsHermitian) (htr : X.trace = 0)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (coherence (hamiltonian ω h) (jumps x y z) X)
      (cTilde x y z ν * (population (hamiltonian ω h) (jumps x y z) X t : ℂ) +
        coeffE y z * star (coherence (hamiltonian ω h) (jumps x y z) X t) -
        ((gamma x y z : ℂ)+I*ω)*coherence (hamiltonian ω h) (jumps x y z) X t) t := by
  have hd := PureStationary.actualState_entry_hasDerivAt (hamiltonian ω h) (jumps x y z) X t 0 1
  rw [actual_state_shape _ _ (hamiltonian_isHermitian ω h) X hX htr t ht,
    action_coherence x y z ω ν _ h _ hs hν] at hd
  exact hd




/-- 生成元规范等式传递至真实矩阵指数，对任意实时间成立。 -/
theorem actualState_congr {n m : ℕ} (H H' : QubitMatrix)
    (J : Fin n → QubitMatrix) (J' : Fin m → QubitMatrix)
    (he : ∀ X : QubitMatrix, gkslAction H J X = gkslAction H' J' X)
    (X : QubitMatrix) (t : ℝ) :
    PureStationary.actualState H J X t = PureStationary.actualState H' J' X t := by
  have hL : gkslContinuousLinearMap H J = gkslContinuousLinearMap H' J' := by
    ext1 Y
    exact he Y
  unfold PureStationary.actualState gkslSuperoperatorEvolution
  rw [hL]

theorem actual_readout {n : ℕ} (H : QubitMatrix) (J : Fin n → QubitMatrix)
    (hH : H.IsHermitian) (X : QubitMatrix) (hX : X.IsHermitian) (htr : X.trace = 0)
    (t p w : ℝ) (ht : 0 ≤ t) :
    ((measurement p w * PureStationary.actualState H J X t).trace).re =
      (1-2*p)*population H J X t + w*(coherence H J X t).re := by
  rw [actual_state_shape H J hH X hX htr t ht]
  exact readout p w _ _

#check @stationary_U
#check @stationary_h
#check @stationary_coefficient_bounds
#check @normal_form
#check @actual_population_hasDerivAt
#check @actual_coherence_hasDerivAt
#print axioms normal_form
#print axioms stationary_U
#print axioms stationary_h
#print axioms gram_eq
#print axioms gram_posSemidef
#print axioms stationary_coefficient_bounds
#print axioms actual_population_hasDerivAt
#print axioms actual_coherence_hasDerivAt
#print axioms actual_readout
#print axioms actualState_congr

end TwoStateQuantumEmbedding.ResetMixed
