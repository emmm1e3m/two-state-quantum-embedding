import TwoStateQuantumEmbedding.ExponentialRepresentation
import TwoStateQuantumEmbedding.ResetCore
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-! 显式单跳跃重置族：原始 GKSL 的谱分解。 -/
noncomputable section
open Matrix Complex Filter Topology
open scoped Matrix.Norms.Operator

namespace TwoStateQuantumEmbedding.ResetFamily

/-- 矩阵指数在本征向量上的作用，由指数级数推出。 -/
theorem matrix_exp_eigen {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (v : ι → ℂ) (z : ℂ) (hv : M *ᵥ v = z • v) :
    NormedSpace.exp M *ᵥ v = Complex.exp z • v := by
  let ev : Matrix ι ι ℂ →L[ℂ] (ι → ℂ) :=
    ((Matrix.mulVecBilin ℂ ℂ).flip v).toContinuousLinearMap
  have hp (n : ℕ) : M ^ n *ᵥ v = z ^ n • v := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hv]
      simp [smul_smul, pow_succ', mul_comm]
  have h₁ := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) M).mapL ev
  change HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹ • M ^ n) *ᵥ v)
    (NormedSpace.exp M *ᵥ v) at h₁
  have h₂ := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) z).smul_const v
  have hs : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹ * z ^ n) • v)
      (NormedSpace.exp M *ᵥ v) := by
    simpa only [Matrix.smul_mulVec, hp, smul_smul] using h₁
  simpa only [smul_eq_mul, ← Complex.exp_eq_exp_ℂ] using hs.unique h₂

def rotation (c s : ℝ) : QubitMatrix := !![(c : ℂ), s; -s, c]
def triangularJump (m n : ℝ) : QubitMatrix := !![-(m : ℂ), 0; n, 0]
def excited : QubitMatrix := !![1, 0; 0, 0]
def ground : QubitMatrix := !![0, 0; 0, 1]
def coherence : QubitMatrix := !![0, 1; 1, 0]
def conjugate (U X : QubitMatrix) : QubitMatrix := U * X * U.conjTranspose
def jump (c s m n : ℝ) : QubitMatrix :=
  conjugate (rotation c s) (triangularJump m n)

theorem rotation_unitary (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    (rotation c s).conjTranspose * rotation c s = 1 ∧
      rotation c s * (rotation c s).conjTranspose = 1 := by
  have hC : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast h
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [rotation, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      ] <;> solve | ring | linear_combination hC

theorem dissipator_conjugate (U J X : QubitMatrix)
    (hU : U.conjTranspose * U = 1) :
    dissipator (conjugate U J) (conjugate U X) = conjugate U (dissipator J X) := by
  simp only [dissipator, conjugate, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc U.conjTranspose U, hU,
    Matrix.one_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul]

theorem triangular_ground (m n : ℝ) :
    dissipator (triangularJump m n) ground = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [dissipator, triangularJump, ground, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Matrix.vecMul, dotProduct]

theorem triangular_coherence (m n : ℝ) (h : m ^ 2 + n ^ 2 = 1) :
    dissipator (triangularJump m n) coherence = (- (1 / 2 : ℂ)) • coherence := by
  have hC : (m : ℂ) ^ 2 + (n : ℂ) ^ 2 = 1 := by exact_mod_cast h
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [dissipator, triangularJump, coherence, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Matrix.vecMul, dotProduct] <;> solve | ring | linear_combination hC

theorem triangular_fast (m n k : ℝ) (h : m ^ 2 + n ^ 2 = 1)
    (hk : k = n ^ 2 - m ^ 2) :
    dissipator (triangularJump m n)
        ((k : ℂ) • (excited - ground) + (2 * m * n : ℂ) • coherence) =
      (- ((1 + k) / 2 : ℂ)) •
        ((k : ℂ) • (excited - ground) + (2 * m * n : ℂ) • coherence) := by
  have hC : (m : ℂ) ^ 2 + (n : ℂ) ^ 2 = 1 := by exact_mod_cast h
  have hkC : (k : ℂ) = (n : ℂ) ^ 2 - (m : ℂ) ^ 2 := by exact_mod_cast hk
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [dissipator, triangularJump, excited, ground, coherence, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.vecMul, dotProduct] <;>
    rw [hkC] <;> solve
    | ring
    | linear_combination -(n ^ 2 - m ^ 2 : ℂ) * hC / 2
    | linear_combination (n ^ 2 - m ^ 2 : ℂ) * hC / 2
    | linear_combination -(m * n : ℂ) * hC

/-- 原始 GKSL 本征算子的实际有限时间演化。 -/
theorem evolution_eigen {N : ℕ} (H : QubitMatrix) (J : Fin N → QubitMatrix)
    (t : ℝ) (X : QubitMatrix) (z : ℂ) (hX : gkslAction H J X = z • X) :
    gkslSuperoperatorEvolution H J t X = Complex.exp ((t : ℂ) * z) • X := by
  have hg : (t • gkslMatrix H J) *ᵥ (fun ij => X ij.1 ij.2) =
      ((t : ℂ) * z) • (fun ij => X ij.1 ij.2) := by
    rw [Matrix.smul_mulVec, gkslMatrix_mulVec, hX]
    ext ij
    simp [smul_eq_mul, mul_assoc]
  have he := matrix_exp_eigen (t • gkslMatrix H J)
    (fun ij => X ij.1 ij.2) ((t : ℂ) * z) hg
  change finiteEvolution H J t *ᵥ (fun ij => X ij.1 ij.2) = _ at he
  rw [finiteEvolution_mulVec_eq_superoperator] at he
  ext i j
  exact congrFun he (i, j)

def jumps (c s m n : ℝ) : Fin 1 → QubitMatrix := fun _ => jump c s m n
def groundMode (c s : ℝ) := conjugate (rotation c s) ground
def coherenceMode (c s : ℝ) := conjugate (rotation c s) coherence
def fastMode (c s m n k : ℝ) := conjugate (rotation c s)
  ((k : ℂ) • (excited - ground) + (2 * m * n : ℂ) • coherence)

theorem ground_eigen (c s m n : ℝ) (hc : c ^ 2 + s ^ 2 = 1) :
    gkslAction 0 (jumps c s m n) (groundMode c s) = 0 := by
  simp only [gkslAction, zero_mul, mul_zero, sub_self, smul_zero,
    zero_add, jumps, Fin.sum_univ_one, jump, groundMode]
  rw [dissipator_conjugate _ _ _ (rotation_unitary c s hc).1, triangular_ground]
  simp [conjugate]

theorem coherence_eigen (c s m n : ℝ) (hc : c ^ 2 + s ^ 2 = 1)
    (hm : m ^ 2 + n ^ 2 = 1) :
    gkslAction 0 (jumps c s m n) (coherenceMode c s) =
      (-(1 / 2 : ℂ)) • coherenceMode c s := by
  simp only [gkslAction, zero_mul, mul_zero, sub_self, smul_zero,
    zero_add, jumps, Fin.sum_univ_one, jump, coherenceMode]
  rw [dissipator_conjugate _ _ _ (rotation_unitary c s hc).1,
    triangular_coherence m n hm]
  simp only [conjugate, Matrix.mul_smul, Matrix.smul_mul]

theorem fast_eigen (c s m n k : ℝ) (hc : c ^ 2 + s ^ 2 = 1)
    (hm : m ^ 2 + n ^ 2 = 1) (hk : k = n ^ 2 - m ^ 2) :
    gkslAction 0 (jumps c s m n) (fastMode c s m n k) =
      (-((1 + k) / 2 : ℂ)) • fastMode c s m n k := by
  simp only [gkslAction, zero_mul, mul_zero, sub_self, smul_zero,
    zero_add, jumps, Fin.sum_univ_one, jump, fastMode]
  rw [dissipator_conjugate _ _ _ (rotation_unitary c s hc).1,
    triangular_fast m n k hm hk]
  simp only [conjugate, Matrix.mul_smul, Matrix.smul_mul]

theorem conjugate_inverse (U X : QubitMatrix)
    (hU : U * U.conjTranspose = 1) :
    conjugate U (U.conjTranspose * X * U) = X := by
  simp only [conjugate, Matrix.mul_assoc, ← Matrix.mul_assoc U U.conjTranspose,
    hU, Matrix.one_mul, Matrix.mul_one]

theorem input_zero_decomposition (c s m n k : ℝ) (hc : c ^ 2 + s ^ 2 = 1)
    (hk : k ≠ 0) :
    Matrix.single 0 0 (1 : ℂ) = groundMode c s +
      ((c ^ 2 / k : ℝ) : ℂ) • fastMode c s m n k +
      ((c * s - c ^ 2 * (2 * m * n) / k : ℝ) : ℂ) • coherenceMode c s := by
  rw [← conjugate_inverse (rotation c s) (Matrix.single 0 0 1)
    (rotation_unitary c s hc).2]
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hcC : (c : ℂ)^2 + (s : ℂ)^2 = 1 := by exact_mod_cast hc
  have hi : (rotation c s).conjTranspose * Matrix.single 0 0 1 * rotation c s =
      ground + ((c ^ 2 / k : ℝ) : ℂ) •
        ((k : ℂ) • (excited - ground) + (2 * m * n : ℂ) • coherence) +
      ((c * s - c ^ 2 * (2 * m * n) / k : ℝ) : ℂ) • coherence := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [rotation, ground, excited, coherence, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.conjTranspose_apply,
        Matrix.single_apply] <;> field_simp <;>
      solve | ring | linear_combination hcC
  have hh := congrArg (conjugate (rotation c s)) hi
  simpa only [groundMode, fastMode, coherenceMode, conjugate, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul] using hh

theorem input_one_decomposition (c s m n k : ℝ) (hc : c ^ 2 + s ^ 2 = 1)
    (hk : k ≠ 0) :
    Matrix.single 1 1 (1 : ℂ) = groundMode c s +
      ((s ^ 2 / k : ℝ) : ℂ) • fastMode c s m n k +
      ((-c * s - s ^ 2 * (2 * m * n) / k : ℝ) : ℂ) • coherenceMode c s := by
  rw [← conjugate_inverse (rotation c s) (Matrix.single 1 1 1)
    (rotation_unitary c s hc).2]
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hcC : (c : ℂ)^2 + (s : ℂ)^2 = 1 := by exact_mod_cast hc
  have hi : (rotation c s).conjTranspose * Matrix.single 1 1 1 * rotation c s =
      ground + ((s ^ 2 / k : ℝ) : ℂ) •
        ((k : ℂ) • (excited - ground) + (2 * m * n : ℂ) • coherence) +
      ((-c * s - s ^ 2 * (2 * m * n) / k : ℝ) : ℂ) • coherence := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [rotation, ground, excited, coherence, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose_apply, Matrix.single_apply] <;> field_simp <;>
      solve | ring | linear_combination hcC
  have hh := congrArg (conjugate (rotation c s)) hi
  simpa only [groundMode, fastMode, coherenceMode, conjugate, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul] using hh

theorem evolution_modes (c s m n k t : ℝ) (hc : c ^ 2 + s ^ 2 = 1)
    (hm : m ^ 2 + n ^ 2 = 1) (hk : k = n ^ 2 - m ^ 2) :
    gkslSuperoperatorEvolution 0 (jumps c s m n) t (groundMode c s) = groundMode c s ∧
    gkslSuperoperatorEvolution 0 (jumps c s m n) t (coherenceMode c s) =
      (Real.exp (-t / 2) : ℂ) • coherenceMode c s ∧
    gkslSuperoperatorEvolution 0 (jumps c s m n) t (fastMode c s m n k) =
      (Real.exp (-(1 + k) * t / 2) : ℂ) • fastMode c s m n k := by
  constructor
  · have h := evolution_eigen 0 (jumps c s m n) t (groundMode c s) 0
      (by simpa using ground_eigen c s m n hc)
    simpa using h
  constructor
  · have h := evolution_eigen 0 (jumps c s m n) t (coherenceMode c s) (-(1 / 2 : ℂ))
      (coherence_eigen c s m n hc hm)
    convert h using 1
    congr 1
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  · have h := evolution_eigen 0 (jumps c s m n) t (fastMode c s m n k)
      (-((1 + k) / 2 : ℂ)) (fast_eigen c s m n k hc hm hk)
    convert h using 1
    congr 1
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring

def bCoefficient (c s m n k : ℝ) : ℝ := c ^ 2 - s ^ 2 + 4 * m * n * c * s / k
def epsilon (c s m n k t : ℝ) : ℝ :=
  s ^ 2 * (1 - (1 + bCoefficient c s m n k) * Real.exp (-t / 2) +
    bCoefficient c s m n k * Real.exp (-(1 + k) * t / 2))
def aProbability (c s m n k t : ℝ) : ℝ :=
  epsilon c s m n k t + (c ^ 2 - s ^ 2) * bCoefficient c s m n k *
    Real.exp (-(1 + k) * t / 2) -
    ((c ^ 2 - s ^ 2) * bCoefficient c s m n k - 1) * Real.exp (-t / 2)

theorem finiteOutput_exact (c s m n k t : ℝ) (hc : c ^ 2 + s ^ 2 = 1)
    (hm : m ^ 2 + n ^ 2 = 1) (hk : k = n ^ 2 - m ^ 2) (hk0 : k ≠ 0) :
    finiteOutput 0 (jumps c s m n) t =
      (aProbability c s m n k t, 1 - epsilon c s m n k t) := by
  obtain ⟨hG, hW, hF⟩ := evolution_modes c s m n k t hc hm hk
  rw [finiteOutput_eq_superoperator_probabilities,
    input_zero_decomposition c s m n k hc hk0, input_one_decomposition c s m n k hc hk0]
  simp only [map_add, map_smul, hG, hW, hF]
  unfold aProbability epsilon
  generalize Real.exp (-t / 2) = S
  generalize Real.exp (-(1 + k) * t / 2) = F
  apply Prod.ext <;>
    simp [bCoefficient, groundMode, coherenceMode, fastMode,
      conjugate, rotation, ground, excited, coherence,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Complex.mul_re, Complex.mul_im, pow_two] <;> field_simp
  · linear_combination k * S * (c ^ 2 + 1) * hc
  · linear_combination (k + S * k * s ^ 2) * hc

def aCoefficient (c s m n k : ℝ) : ℝ :=
  (c ^ 2 - s ^ 2) * bCoefficient c s m n k
def optimalTime (A k : ℝ) : ℝ := -2 * Real.log (Reset.optimalScale A (A - 1) k)

theorem optimalTime_pos (A k : ℝ) (hA : 1 < A) (hk : 0 < k) :
    0 < optimalTime A k := by
  have hP : 0 < A := by linarith
  have hQ : 0 < A - 1 := by linarith
  have hS := Reset.optimal_scale_pos A (A - 1) k hP hQ hk
  have hS1 := Reset.optimal_scale_lt_one A (A - 1) k hP hQ (by linarith) hk
  have hl := Real.log_neg hS hS1
  unfold optimalTime
  linarith

theorem optimalTime_slow (A k : ℝ) (hA : 1 < A) (hk : 0 < k) :
    Real.exp (-optimalTime A k / 2) = Reset.optimalScale A (A - 1) k := by
  have hS := Reset.optimal_scale_pos A (A - 1) k (by linarith) (by linarith) hk
  convert Real.exp_log hS using 1
  congr 1
  unfold optimalTime
  ring

theorem optimalTime_fast (A k : ℝ) (hA : 1 < A) (hk : 0 < k) :
    Real.exp (-(1 + k) * optimalTime A k / 2) =
      Reset.optimalScale A (A - 1) k ^ (1 + k) := by
  have hS := Reset.optimal_scale_pos A (A - 1) k (by linarith) (by linarith) hk
  rw [Real.rpow_def_of_pos hS]
  congr 1
  unfold optimalTime
  ring

/-- 最优双模时间给出真实 Q₂ 点，而不是仅给出标量候选。 -/
theorem optimal_curve_mem_Q2 (c s m n k : ℝ) (hc : c ^ 2 + s ^ 2 = 1)
    (hm : m ^ 2 + n ^ 2 = 1) (hk : k = n ^ 2 - m ^ 2) (hk0 : 0 < k)
    (hA : 1 < aCoefficient c s m n k) :
    let A := aCoefficient c s m n k
    let S := Reset.optimalScale A (A - 1) k
    let e := epsilon c s m n k (optimalTime A k)
    (e - k * A * S ^ (1 + k), 1 - e) ∈ Q2 := by
  dsimp only
  have h := finiteOutput_mem_Q2 (0 : QubitMatrix) (jumps c s m n)
    (optimalTime (aCoefficient c s m n k) k) (by simp)
    (optimalTime_pos _ _ hA hk0).le
  rw [finiteOutput_exact c s m n k _ hc hm hk hk0.ne'] at h
  have hop := Reset.reset_two_modes_at_optimum (aCoefficient c s m n k) k hA hk0
  have ha : aProbability c s m n k (optimalTime (aCoefficient c s m n k) k) =
      epsilon c s m n k (optimalTime (aCoefficient c s m n k) k) -
      k * aCoefficient c s m n k *
        Reset.optimalScale (aCoefficient c s m n k) (aCoefficient c s m n k - 1) k ^
          (1 + k) := by
    unfold aProbability
    change epsilon c s m n k (optimalTime (aCoefficient c s m n k) k) +
      aCoefficient c s m n k * Real.exp (-(1 + k) * optimalTime _ k / 2) -
      (aCoefficient c s m n k - 1) * Real.exp (-optimalTime _ k / 2) = _
    rw [optimalTime_slow _ _ hA hk0, optimalTime_fast _ _ hA hk0]
    linarith
  rwa [ha] at h

def paperM (k : ℝ) : ℝ := Real.sqrt ((1 - k) / 2)
def paperN (k : ℝ) : ℝ := Real.sqrt ((1 + k) / 2)
def paperJumps (r k : ℝ) : Fin 1 → QubitMatrix :=
  jumps (Real.cos r) (Real.sin r) (paperM k) (paperN k)

theorem paper_parameters (r k : ℝ) (hk : -1 ≤ k) (hk1 : k ≤ 1) :
    Real.cos r ^ 2 + Real.sin r ^ 2 = 1 ∧
    paperM k ^ 2 + paperN k ^ 2 = 1 ∧
    k = paperN k ^ 2 - paperM k ^ 2 := by
  have hm : paperM k ^ 2 = (1 - k) / 2 :=
    Real.sq_sqrt (by linarith)
  have hn : paperN k ^ 2 = (1 + k) / 2 :=
    Real.sq_sqrt (by linarith)
  exact ⟨Real.cos_sq_add_sin_sq r, by rw [hm, hn]; ring, by rw [hm, hn]; ring⟩

theorem paper_sigma (k : ℝ) (hk : -1 ≤ k) (hk1 : k ≤ 1) :
    2 * paperM k * paperN k = Real.sqrt (1 - k ^ 2) := by
  obtain ⟨_, hm, hn⟩ := paper_parameters 0 k hk hk1
  have hp : 0 ≤ 2 * paperM k * paperN k := by
    unfold paperM paperN
    positivity
  have hs := Real.sq_sqrt (by nlinarith : 0 ≤ 1 - k ^ 2)
  have hs0 := Real.sqrt_nonneg (1 - k ^ 2)
  nlinarith [sq_nonneg (paperM k ^ 2 - paperN k ^ 2)]

theorem paper_B (r k : ℝ) (hk : -1 ≤ k) (hk1 : k ≤ 1) :
    bCoefficient (Real.cos r) (Real.sin r) (paperM k) (paperN k) k =
      Real.cos (2 * r) + Real.sqrt (1 - k ^ 2) / k * Real.sin (2 * r) := by
  rw [← paper_sigma k hk hk1, Real.cos_two_mul, Real.sin_two_mul]
  unfold bCoefficient
  have h := Real.cos_sq_add_sin_sq r
  field_simp
  linear_combination -h

def radius (L : ℝ) : ℝ := Real.exp (-L / 2)
def rateRatio (L : ℝ) : ℝ := 1 - 2 / L
def sigma (L : ℝ) : ℝ := Real.sqrt (1 - rateRatio L ^ 2)
def curveB (L : ℝ) : ℝ :=
  Real.cos (2 * radius L) + sigma L / rateRatio L * Real.sin (2 * radius L)
def curveA (L : ℝ) : ℝ := Real.cos (2 * radius L) * curveB L
def correction (L : ℝ) : ℝ := Real.sinc (2 * radius L) *
  (Real.cos (2 * radius L) - rateRatio L * Real.sin (2 * radius L) / sigma L)

theorem radius_pos (L : ℝ) : 0 < radius L := Real.exp_pos _
theorem rateRatio_bounds (L : ℝ) (hL : 2 < L) :
    0 < rateRatio L ∧ rateRatio L < 1 := by
  unfold rateRatio
  have h0 : 0 < L := by linarith
  constructor
  · have : 2 / L < 1 := (div_lt_one h0).mpr hL
    linarith
  · have : 0 < 2 / L := by positivity
    linarith

theorem sigma_pos (L : ℝ) (hL : 2 < L) : 0 < sigma L := by
  obtain ⟨hk0, hk1⟩ := rateRatio_bounds L hL
  exact Real.sqrt_pos.mpr (by nlinarith)

theorem radius_limit : Tendsto radius atTop (𝓝 0) := by
  change Tendsto (fun L : ℝ => Real.exp (-L / 2)) atTop (𝓝 0)
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (1 / 2) (by norm_num)
  simpa [radius, neg_div, div_eq_mul_inv, mul_comm] using h

theorem rateRatio_limit : Tendsto rateRatio atTop (𝓝 1) := by
  change Tendsto (fun L : ℝ => 1 - 2 / L) atTop (𝓝 1)
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_id.const_div_atTop (2 : ℝ))
  simpa [rateRatio] using h

theorem sigma_limit : Tendsto sigma atTop (𝓝 0) := by
  change Tendsto (fun L : ℝ => Real.sqrt (1 - rateRatio L ^ 2)) atTop (𝓝 0)
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub (rateRatio_limit.pow 2)).sqrt
  simpa [sigma] using h

theorem radius_times_L_limit : Tendsto (fun L => radius L * L) atTop (𝓝 0) := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1 / 2) (by norm_num)
  simpa [radius, neg_div, div_eq_mul_inv, mul_comm] using h

theorem sigma_lower (L : ℝ) (hL : 4 ≤ L) : 1 / L ≤ sigma L := by
  have h0 : 0 < L := by linarith
  have hi : 0 ≤ 1 / L := by positivity
  have hb : (1 / L) ^ 2 ≤ 1 - rateRatio L ^ 2 := by
    unfold rateRatio
    field_simp
    nlinarith
  calc
    1 / L = Real.sqrt ((1 / L) ^ 2) := (Real.sqrt_sq hi).symm
    _ ≤ sigma L := Real.sqrt_le_sqrt hb

theorem radius_div_sigma_limit : Tendsto (fun L => radius L / sigma L) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ radius_times_L_limit
  · filter_upwards with L
    exact div_nonneg (radius_pos L).le (Real.sqrt_nonneg _)
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with L hL
    have hL0 : 0 < L := by linarith
    have hσ := sigma_pos L (by linarith)
    have hbound := (div_le_iff₀ hL0).mp (sigma_lower L hL)
    apply (div_le_iff₀ hσ).mpr
    nlinarith [mul_le_mul_of_nonneg_left hbound (radius_pos L).le]

theorem sin_div_sigma_limit :
    Tendsto (fun L => Real.sin (2 * radius L) / sigma L) atTop (𝓝 0) := by
  have hs : Tendsto (fun L => Real.sinc (2 * radius L)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, mul_zero, Real.sinc_zero] using
      Real.continuous_sinc.continuousAt.tendsto.comp (radius_limit.const_mul 2)
  have h := hs.mul (radius_div_sigma_limit.const_mul 2)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards with L
  rw [Real.sinc_of_ne_zero (by exact mul_ne_zero (by norm_num) (radius_pos L).ne' : 2 * radius L ≠ 0)]
  field_simp [ne_of_gt (radius_pos L)]

theorem correction_limit : Tendsto correction atTop (𝓝 1) := by
  change Tendsto (fun L => Real.sinc (2 * radius L) *
    (Real.cos (2 * radius L) - rateRatio L * Real.sin (2 * radius L) / sigma L)) atTop (𝓝 1)
  have hs : Tendsto (fun L => Real.sinc (2 * radius L)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, mul_zero, Real.sinc_zero] using
      Real.continuous_sinc.continuousAt.tendsto.comp (radius_limit.const_mul 2)
  have hc : Tendsto (fun L => Real.cos (2 * radius L)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, mul_zero, Real.cos_zero] using
      Real.continuous_cos.continuousAt.tendsto.comp (radius_limit.const_mul 2)
  have h := hs.mul (hc.sub (rateRatio_limit.mul sin_div_sigma_limit))
  simpa only [correction, mul_div_assoc, mul_zero, sub_zero, mul_one] using h

theorem curveB_limit : Tendsto curveB atTop (𝓝 1) := by
  change Tendsto (fun L => Real.cos (2 * radius L) +
    sigma L / rateRatio L * Real.sin (2 * radius L)) atTop (𝓝 1)
  have h := (Real.continuous_cos.continuousAt.tendsto.comp (radius_limit.const_mul 2)).add
    ((sigma_limit.div rateRatio_limit (by norm_num)).mul (Real.continuous_sin.continuousAt.tendsto.comp (radius_limit.const_mul 2)))
  simpa [curveB, Function.comp_def] using h

theorem curveA_limit : Tendsto curveA atTop (𝓝 1) := by
  change Tendsto (fun L => Real.cos (2 * radius L) * curveB L) atTop (𝓝 1)
  have h := (Real.continuous_cos.continuousAt.tendsto.comp (radius_limit.const_mul 2)).mul curveB_limit
  simpa [curveA, Function.comp_def] using h

theorem curveA_sub_one (L : ℝ) (hL : 2 < L) :
    curveA L - 1 = 2 * sigma L * radius L / rateRatio L * correction L := by
  have hr := (radius_pos L).ne'
  have hk := (rateRatio_bounds L hL).1.ne'
  have hσ := (sigma_pos L hL).ne'
  unfold curveA curveB correction
  rw [Real.sinc_of_ne_zero (by exact mul_ne_zero (by norm_num) (radius_pos L).ne' : 2 * radius L ≠ 0)]
  field_simp
  have htrig := Real.sin_sq_add_cos_sq (2 * radius L)
  linear_combination rateRatio L * htrig

theorem curveA_eventually_gt_one : ∀ᶠ L : ℝ in atTop, 1 < curveA L := by
  have hp := correction_limit.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_gt_atTop (2 : ℝ), hp] with L hL hD
  have hfactor : 0 < 2 * sigma L * radius L / rateRatio L * correction L := by
    exact mul_pos (div_pos (mul_pos (mul_pos (by norm_num) (sigma_pos L hL))
      (radius_pos L)) (rateRatio_bounds L hL).1) hD
  rw [← curveA_sub_one L hL] at hfactor
  linarith

def curveScale (L : ℝ) : ℝ := Reset.optimalScale (curveA L) (curveA L - 1) (rateRatio L)
def curveFast (L : ℝ) : ℝ := curveScale L ^ (1 + rateRatio L)
def curveTime (L : ℝ) : ℝ := optimalTime (curveA L) (rateRatio L)
def curveEpsilon (L : ℝ) : ℝ := Real.sin (radius L) ^ 2 *
  (1 - (1 + curveB L) * curveScale L + curveB L * curveFast L)
def curveGain (L : ℝ) : ℝ := rateRatio L * curveA L * curveFast L
def curvePoint (L : ℝ) : ℝ × ℝ := (curveEpsilon L - curveGain L, 1 - curveEpsilon L)
def gainCorrection (L : ℝ) : ℝ := curveA L *
  (correction L / curveA L) ^ ((1 + rateRatio L) / rateRatio L)

theorem curveScale_limit : Tendsto curveScale atTop (𝓝 0) := by
  change Tendsto (fun L => ((curveA L - 1) / ((1 + rateRatio L) * curveA L)) ^
    (rateRatio L)⁻¹) atTop (𝓝 0)
  have hb := (curveA_limit.sub_const 1).div
    ((rateRatio_limit.const_add 1).mul curveA_limit) (by norm_num : (1 + 1) * (1 : ℝ) ≠ 0)
  have he := rateRatio_limit.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have h := hb.rpow he (Or.inr (by norm_num))
  simpa only [Pi.div_apply, sub_self, mul_one, zero_div, inv_one, Real.rpow_one] using h

theorem curveFast_limit : Tendsto curveFast atTop (𝓝 0) := by
  change Tendsto (fun L => curveScale L ^ (1 + rateRatio L)) atTop (𝓝 0)
  have h := curveScale_limit.rpow (rateRatio_limit.const_add 1) (Or.inr (by norm_num))
  simpa using h

theorem gainCorrection_limit : Tendsto gainCorrection atTop (𝓝 1) := by
  change Tendsto (fun L => curveA L *
    (correction L / curveA L) ^ ((1 + rateRatio L) / rateRatio L)) atTop (𝓝 1)
  have hb := correction_limit.div curveA_limit (by norm_num : (1 : ℝ) ≠ 0)
  have he := (rateRatio_limit.const_add 1).div rateRatio_limit (by norm_num : (1 : ℝ) ≠ 0)
  have h := curveA_limit.mul (hb.rpow he (Or.inl (by norm_num)))
  simpa using h

theorem curveEpsilon_scaled_limit :
    Tendsto (fun L => curveEpsilon L / radius L ^ 2) atTop (𝓝 1) := by
  have hs : Tendsto (fun L => Real.sinc (radius L)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.sinc_zero] using
      Real.continuous_sinc.continuousAt.tendsto.comp radius_limit
  have hb := ((curveB_limit.const_add 1).mul curveScale_limit).const_sub 1
  have h := (hs.pow 2).mul (hb.add (curveB_limit.mul curveFast_limit))
  simp only [mul_zero, sub_zero, add_zero, one_pow, one_mul] at h
  apply h.congr'
  filter_upwards with L
  rw [Real.sinc_of_ne_zero (radius_pos L).ne']
  unfold curveEpsilon
  field_simp

theorem curveEpsilon_limit : Tendsto curveEpsilon atTop (𝓝 0) := by
  have h := curveEpsilon_scaled_limit.mul (radius_limit.pow 2)
  simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero] at h
  apply h.congr'
  filter_upwards with L
  field_simp [ne_of_gt (radius_pos L)]

theorem curveGain_limit : Tendsto curveGain atTop (𝓝 0) := by
  change Tendsto (fun L => rateRatio L * curveA L * curveFast L) atTop (𝓝 0)
  simpa using (rateRatio_limit.mul curveA_limit).mul curveFast_limit

theorem curvePoint_limit : Tendsto curvePoint atTop (𝓝 ((0, 1) : ℝ × ℝ)) := by
  have h := (curveEpsilon_limit.sub curveGain_limit).prodMk_nhds
    (curveEpsilon_limit.const_sub 1)
  change Tendsto (fun L => (curveEpsilon L - curveGain L, 1 - curveEpsilon L)) atTop _
  simpa using h

theorem radius_rpow_quotient (L : ℝ) (hL : 2 < L) :
    radius L ^ ((1 + rateRatio L) / rateRatio L) / radius L ^ 2 =
      Real.exp (-1 / rateRatio L) := by
  have hL0 : L ≠ 0 := by linarith
  have hk0 := (rateRatio_bounds L hL).1.ne'
  unfold radius
  rw [← Real.rpow_natCast (Real.exp (-L / 2)) 2, ← Real.exp_mul, ← Real.exp_mul,
    ← Real.exp_sub]
  congr 1
  unfold rateRatio at *
  field_simp
  ring

theorem curveGain_scaled_exact (L : ℝ) (hL : 2 < L) (hA : 1 < curveA L) :
    curveGain L / radius L ^ 2 = Reset.resetGain L * gainCorrection L := by
  have hk := (rateRatio_bounds L hL).1
  have hσ := sigma_pos L hL
  have hr := radius_pos L
  have hAp : 0 < curveA L := by linarith
  have hQ : 0 < curveA L - 1 := by linarith
  have hD : 0 < correction L := by
    have hf : 0 < 2 * sigma L * radius L / rateRatio L := by positivity
    rw [curveA_sub_one L hL] at hQ
    exact (mul_pos_iff_of_pos_left hf).mp hQ
  have hbase : (curveA L - 1) / ((1 + rateRatio L) * curveA L) =
      (2 * sigma L / (rateRatio L * (1 + rateRatio L))) *
      radius L * (correction L / curveA L) := by
    rw [curveA_sub_one L hL]
    field_simp
  unfold curveGain curveFast curveScale
  rw [Reset.optimal_scale_power_add _ _ _ hAp (by linarith) hk, hbase]
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) hr.le]
  rw [Reset.reset_gain_eq_prefactor L hL]
  change rateRatio L * curveA L *
    ((2 * sigma L / (rateRatio L * (1 + rateRatio L))) ^
      ((1 + rateRatio L) / rateRatio L) *
      radius L ^ ((1 + rateRatio L) / rateRatio L) *
      (correction L / curveA L) ^ ((1 + rateRatio L) / rateRatio L)) / radius L ^ 2 = _
  unfold Reset.purePrefactor gainCorrection
  change _ = rateRatio L *
    (2 * sigma L / (rateRatio L * (1 + rateRatio L))) ^
      ((1 + rateRatio L) / rateRatio L) * Real.exp (-1 / rateRatio L) *
    (curveA L * (correction L / curveA L) ^ ((1 + rateRatio L) / rateRatio L))
  rw [← radius_rpow_quotient L hL]
  ring

theorem curveGain_scaled_limit :
    Tendsto (fun L => L * (curveGain L / radius L ^ 2)) atTop (𝓝 (4 / Real.exp 1)) := by
  have h := Reset.scaled_reset_gain_limit.mul gainCorrection_limit
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (2 : ℝ), curveA_eventually_gt_one] with L hL hA
  rw [curveGain_scaled_exact L hL hA]
  ring

theorem curve_relative_gain_limit :
    Tendsto (fun L => L * (curveGain L / curveEpsilon L)) atTop
      (𝓝 (4 / Real.exp 1)) := by
  have h := curveGain_scaled_limit.div curveEpsilon_scaled_limit (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at h
  apply h.congr'
  filter_upwards with L
  change (L * (curveGain L / radius L ^ 2)) / (curveEpsilon L / radius L ^ 2) =
    L * (curveGain L / curveEpsilon L)
  field_simp [ne_of_gt (radius_pos L)]

theorem paper_A (r k : ℝ) (hk : -1 ≤ k) (hk1 : k ≤ 1) :
    aCoefficient (Real.cos r) (Real.sin r) (paperM k) (paperN k) k =
      Real.cos (2 * r) *
        (Real.cos (2 * r) + Real.sqrt (1 - k ^ 2) / k * Real.sin (2 * r)) := by
  unfold aCoefficient
  rw [paper_B r k hk hk1]
  congr 1
  rw [Real.cos_two_mul]
  linear_combination -(Real.cos_sq_add_sin_sq r)

/-- 论文指定随 L 变化的跳跃与时间，确实产生给定标量曲线。 -/
theorem actual_curve_output (L : ℝ) (hL : 2 < L) (hA : 1 < curveA L) :
    finiteOutput 0 (paperJumps (radius L) (rateRatio L)) (curveTime L) = curvePoint L := by
  obtain ⟨hk0, hk1⟩ := rateRatio_bounds L hL
  obtain ⟨hc, hm, hk⟩ := paper_parameters (radius L) (rateRatio L) (by linarith) hk1.le
  have hB : bCoefficient (Real.cos (radius L)) (Real.sin (radius L))
      (paperM (rateRatio L)) (paperN (rateRatio L)) (rateRatio L) = curveB L :=
    paper_B _ _ (by linarith) hk1.le
  have hAc : aCoefficient (Real.cos (radius L)) (Real.sin (radius L))
      (paperM (rateRatio L)) (paperN (rateRatio L)) (rateRatio L) = curveA L :=
    paper_A _ _ (by linarith) hk1.le
  have hE : epsilon (Real.cos (radius L)) (Real.sin (radius L))
      (paperM (rateRatio L)) (paperN (rateRatio L)) (rateRatio L) (curveTime L) =
        curveEpsilon L := by
    unfold epsilon curveTime
    rw [hB, optimalTime_slow _ _ hA hk0, optimalTime_fast _ _ hA hk0]
    rfl
  have hop := Reset.reset_two_modes_at_optimum (curveA L) (rateRatio L) hA hk0
  have ha : aProbability (Real.cos (radius L)) (Real.sin (radius L))
      (paperM (rateRatio L)) (paperN (rateRatio L)) (rateRatio L) (curveTime L) =
        curveEpsilon L - curveGain L := by
    unfold aProbability
    rw [hE]
    change curveEpsilon L + aCoefficient _ _ _ _ _ *
      Real.exp (-(1 + rateRatio L) * curveTime L / 2) -
      (aCoefficient _ _ _ _ _ - 1) * Real.exp (-curveTime L / 2) = _
    rw [hAc]
    unfold curveTime
    rw [optimalTime_slow _ _ hA hk0, optimalTime_fast _ _ hA hk0]
    unfold curveGain curveFast curveScale
    linarith
  rw [paperJumps, finiteOutput_exact _ _ _ _ _ _ hc hm hk hk0.ne', ha, hE]
  rfl

def unitJumps (L : ℝ) : Fin 1 → QubitMatrix :=
  fun μ => Real.sqrt (curveTime L) • paperJumps (radius L) (rateRatio L) μ

theorem actual_unit_curve_output (L : ℝ) (hL : 2 < L) (hA : 1 < curveA L) :
    finiteOutput 0 (unitJumps L) 1 = curvePoint L := by
  have ht := (optimalTime_pos _ _ hA (rateRatio_bounds L hL).1).le
  have h := finiteOutput_time_normalization (0 : QubitMatrix)
    (paperJumps (radius L) (rateRatio L)) (curveTime L) ht
  simp only [smul_zero] at h
  exact h.trans (actual_curve_output L hL hA)

theorem curvePoint_eventually_mem_Q2 : ∀ᶠ L : ℝ in atTop, curvePoint L ∈ Q2 := by
  filter_upwards [eventually_gt_atTop (2 : ℝ), curveA_eventually_gt_one] with L hL hA
  rw [← actual_unit_curve_output L hL hA]
  exact finiteOutput_mem_Q2 0 (unitJumps L) 1 (by simp) (by norm_num)

theorem curveEpsilon_eventually_pos : ∀ᶠ L : ℝ in atTop, 0 < curveEpsilon L := by
  have h := curveEpsilon_scaled_limit.eventually
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [h] with L hL
  exact (div_pos_iff_of_pos_right (sq_pos_of_pos (radius_pos L))).mp hL

theorem curve_log_scale_limit :
    Tendsto (fun L => Real.log (1 / curveEpsilon L) / L) atTop (𝓝 1) := by
  have hl : Tendsto (fun L => Real.log (curveEpsilon L / radius L ^ 2)) atTop (𝓝 0) := by
    have h := Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)
    simpa only [Function.comp_def, Real.log_one] using h.tendsto.comp curveEpsilon_scaled_limit
  have hd := hl.div_atTop tendsto_id
  have h := hd.const_sub 1
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (2 : ℝ), curveEpsilon_eventually_pos] with L hL he
  have hL0 : L ≠ 0 := by linarith
  have hr : radius L ^ 2 ≠ 0 := pow_ne_zero _ (radius_pos L).ne'
  have hlogr : Real.log (radius L ^ 2) = -L := by
    rw [Real.log_pow, radius, Real.log_exp]
    ring
  rw [Real.log_div he.ne' hr, hlogr, one_div, Real.log_inv]
  simp only [id_eq]
  field_simp
  ring

/-- 实际重置概率的对数领先系数为 4/e。 -/
theorem curve_log_gain_limit :
    Tendsto (fun L => Real.log (1 / curveEpsilon L) * (curveGain L / curveEpsilon L))
      atTop (𝓝 (4 / Real.exp 1)) := by
  have h := curve_log_scale_limit.mul curve_relative_gain_limit
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with L hL
  have hL0 : L ≠ 0 := by linarith
  field_simp

/-- 直接以正式有限输出写出的 4/e 端点构造。 -/
theorem finiteOutput_log_gain_limit :
    Tendsto (fun L =>
      Real.log (1 / (1 - (finiteOutput 0 (unitJumps L) 1).2)) *
        (1 - (finiteOutput 0 (unitJumps L) 1).1 /
          (1 - (finiteOutput 0 (unitJumps L) 1).2))) atTop (𝓝 (4 / Real.exp 1)) := by
  apply curve_log_gain_limit.congr'
  filter_upwards [eventually_gt_atTop (2 : ℝ), curveA_eventually_gt_one,
    curveEpsilon_eventually_pos] with L hL hA he
  rw [actual_unit_curve_output L hL hA]
  simp only [curvePoint, sub_sub_cancel]
  field_simp
  ring

theorem finiteOutput_endpoint_limit :
    Tendsto (fun L => finiteOutput 0 (unitJumps L) 1) atTop (𝓝 ((0, 1) : ℝ × ℝ)) := by
  apply curvePoint_limit.congr'
  filter_upwards [eventually_gt_atTop (2 : ℝ), curveA_eventually_gt_one] with L hL hA
  exact (actual_unit_curve_output L hL hA).symm

end TwoStateQuantumEmbedding.ResetFamily

#print axioms TwoStateQuantumEmbedding.ResetFamily.matrix_exp_eigen
#print axioms TwoStateQuantumEmbedding.ResetFamily.finiteOutput_exact
#print axioms TwoStateQuantumEmbedding.ResetFamily.optimal_curve_mem_Q2
#print axioms TwoStateQuantumEmbedding.ResetFamily.actual_unit_curve_output
#print axioms TwoStateQuantumEmbedding.ResetFamily.curvePoint_eventually_mem_Q2
#print axioms TwoStateQuantumEmbedding.ResetFamily.finiteOutput_log_gain_limit
#print axioms TwoStateQuantumEmbedding.ResetFamily.finiteOutput_endpoint_limit









