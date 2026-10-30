import TwoStateQuantumEmbedding.UnitaryBoundary
import TwoStateQuantumEmbedding.SwapCore
import TwoStateQuantumEmbedding.GKSLNormBounds
import TwoStateQuantumEmbedding.FirstOrderBridge
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Topology.Order.IntermediateValue

/-! B4 的真实候选族、精确参数填充和二次上界。 -/
noncomputable section
open Matrix Complex
open scoped Matrix.Norms.Operator ComplexOrder
namespace TwoStateQuantumEmbedding.SwapMatching
open GKSLAlgebra CanonicalBloch

/-- 无迹版本，保留原文尖锐首阶而避免标量跳跃的 Hamiltonian 规范修正。 -/
def matchingVector : PauliVec := ![-((Swap.rootTwo / 4 : ℝ) : ℂ) * Complex.I, 0, ((1 / 2 : ℝ) : ℂ)]
def matchingHamiltonian : BlochVec := ![Real.pi, 0, 0]
def matchingK (ε : ℝ) : Matrix (Fin 3) (Fin 3) ℂ := ε • singleK matchingVector
def matchingOutput (ε : ℝ) : ℝ × ℝ := canonicalOutput matchingHamiltonian (matchingK ε) 1

def alpha0 : ℝ := (1 - 2 * Swap.rootTwo / Real.pi) / 4
def beta0 : ℝ := (1 + 2 * Swap.rootTwo / Real.pi) / 4

lemma singleK_posSemidef (v : PauliVec) : (singleK v).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star v

lemma matchingK_posSemidef {ε : ℝ} (hε : 0 ≤ ε) : (matchingK ε).PosSemidef := by
  exact (singleK_posSemidef matchingVector).smul hε

lemma matchingOutput_mem_Q2 {ε : ℝ} (hε : 0 ≤ ε) : matchingOutput ε ∈ Q2 :=
  canonicalOutput_mem_Q2 _ _ (matchingK_posSemidef hε) 1 (by norm_num)

lemma matchingOutput_zero : matchingOutput 0 = (0, 0) := by
  simp [matchingOutput, matchingK, matchingHamiltonian, canonicalOutput_x_zero]

lemma continuous_matchingOutput : Continuous matchingOutput := by
  unfold matchingOutput canonicalOutput canonicalEvolution matchingK
  unfold augmentedGenerator blochMatrix drift
  fun_prop

lemma matchingVector_energy : Swap.energy matchingVector = 1 / 4 := by
  simp [Swap.energy, matchingVector, Complex.normSq_apply]
  nlinarith [Swap.rootTwo_sq]

lemma matchingVector_cross : Swap.cross matchingVector = Swap.rootTwo / 8 := by
  change (((starRingEnd ℂ) (-((Swap.rootTwo / 4 : ℝ) : ℂ) * Complex.I)) *
    ((1 / 2 : ℝ) : ℂ)).im = Swap.rootTwo / 8
  rw [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
  simp only [Complex.mul_im, Complex.mul_re, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

lemma matchingVector_qa : Swap.qa 0 matchingVector = alpha0 := by
  rw [Swap.qa, matchingVector_energy, matchingVector_cross, Swap.frequency_zero]
  unfold alpha0
  ring

lemma matchingVector_qb : Swap.qb 0 matchingVector = beta0 := by
  rw [Swap.qb, matchingVector_energy, matchingVector_cross, Swap.frequency_zero]
  unfold beta0
  ring

lemma matchingK_trace (ε : ℝ) : Matrix.trace ((matchingK ε).map Complex.re) = 3 * ε / 8 := by
  simp [matchingK, singleK, matchingVector, Matrix.trace, Matrix.diag,
    Fin.sum_univ_three, Complex.mul_re, Complex.mul_im, Matrix.smul_apply]
  ring_nf
  rw [Swap.rootTwo_sq]
  ring

lemma beta0_pos : 0 < beta0 := by
  have hr := Swap.rootTwo_pos
  unfold beta0
  positivity

lemma beta0_lt_half : beta0 < 1 / 2 := by
  have hq : 2 * Swap.rootTwo / Real.pi < 1 :=
    (div_lt_one Real.pi_pos).2 Swap.twice_rootTwo_lt_pi
  unfold beta0
  linarith

lemma alpha0_eq_slope_mul_beta0 : alpha0 = Swap.slope * beta0 := by
  have hp := ne_of_gt Real.pi_pos
  have hd : Real.pi + 2 * Swap.rootTwo ≠ 0 := ne_of_gt (by linarith [Swap.rootTwo_pos, Real.pi_pos])
  unfold alpha0 beta0 Swap.slope
  field_simp

lemma beta0_times_one_add_slope : beta0 * (1 + Swap.slope) = 1 / 2 := by
  have hp := ne_of_gt Real.pi_pos
  have hd : Real.pi + 2 * Swap.rootTwo ≠ 0 := ne_of_gt (by linarith [Swap.rootTwo_pos, Real.pi_pos])
  unfold beta0 Swap.slope
  field_simp
  ring

lemma slope_lt_one_sixteenth : Swap.slope < 1 / 16 := by
  have hr : (7 : ℝ) / 5 < Swap.rootTwo := by
    nlinarith [Swap.rootTwo_sq, Swap.rootTwo_pos]
  have hp := Real.pi_lt_d2
  unfold Swap.slope
  apply (div_lt_iff₀ (by positivity : 0 < Real.pi + 2 * Swap.rootTwo)).2
  norm_num at hp ⊢
  linarith

lemma matching_constant_eq : 8 * (1 + Swap.slope) / beta0 ^ 2 =
    32 * (1 + Swap.slope) ^ 3 := by
  have hb := ne_of_gt beta0_pos
  apply (div_eq_iff (pow_ne_zero 2 hb)).2
  calc
    8 * (1 + Swap.slope) = 32 * (1 + Swap.slope) * (beta0 * (1 + Swap.slope)) ^ 2 := by
      rw [beta0_times_one_add_slope]
      ring
    _ = 32 * (1 + Swap.slope) ^ 3 * beta0 ^ 2 := by ring

lemma matching_constant_lt_forty : 8 * (1 + Swap.slope) / beta0 ^ 2 < 40 := by
  have hs := Swap.slope_pos
  rw [matching_constant_eq]
  calc
    32 * (1 + Swap.slope) ^ 3 < 32 * ((17 : ℝ) / 16) ^ 3 := by
      gcongr
      linarith [slope_lt_one_sixteenth]
    _ < 40 := by norm_num

/-- 单纯连续性和已证明的二次误差足以逐点精确填充，无需单调性。 -/
lemma exact_second_from_remainder (B : ℝ → ℝ) (hB : Continuous B) (hB0 : B 0 = 0)
    (hrem : ∀ ε, 0 ≤ ε → |B ε - beta0 * ε| ≤ 2 * ε ^ 2)
    {b : ℝ} (hb : 0 < b) (hbsmall : b ≤ beta0 ^ 2 / 8) :
    ∃ ε, 0 < ε ∧ ε ≤ 2 * b / beta0 ∧ B ε = b := by
  have hbeta := beta0_pos
  let ε0 := 2 * b / beta0
  have he0 : 0 < ε0 := by dsimp [ε0]; positivity
  have heq : beta0 * ε0 = 2 * b := by dsimp [ε0]; field_simp [ne_of_gt beta0_pos]
  have hemax : ε0 ≤ beta0 / 4 := by
    dsimp [ε0]
    apply (div_le_iff₀ beta0_pos).2
    nlinarith
  have hcover : b ≤ B ε0 := by
    have hlow := (abs_le.mp (hrem ε0 he0.le)).1
    have hm : 0 ≤ ε0 * (beta0 - 4 * ε0) := mul_nonneg he0.le (by linarith)
    nlinarith
  have htarget : b ∈ Set.Icc (B 0) (B ε0) := by rw [hB0]; exact ⟨hb.le, hcover⟩
  obtain ⟨ε, hε, hmatch⟩ := intermediate_value_Icc he0.le hB.continuousOn htarget
  refine ⟨ε, ?_, hε.2, hmatch⟩
  by_contra hn
  have hz : ε = 0 := le_antisymm (le_of_not_gt hn) hε.1
  rw [hz, hB0] at hmatch
  linarith

lemma exact_match_quadratic_bound (A B : ℝ → ℝ)
    (hremA : ∀ ε, 0 ≤ ε → |A ε - alpha0 * ε| ≤ 2 * ε ^ 2)
    (hremB : ∀ ε, 0 ≤ ε → |B ε - beta0 * ε| ≤ 2 * ε ^ 2)
    {b ε : ℝ} (hb : 0 < b) (hε : 0 ≤ ε) (hemax : ε ≤ 2 * b / beta0)
    (hmatch : B ε = b) : A ε < Swap.slope * b + 40 * b ^ 2 := by
  have hbeta := beta0_pos
  have hslope := Swap.slope_pos
  have ha := (abs_le.mp (hremA ε hε)).2
  have hbrem := (abs_le.mp (hremB ε hε)).1
  rw [hmatch] at hbrem
  rw [alpha0_eq_slope_mul_beta0] at ha
  have hs := mul_le_mul_of_nonneg_left (show beta0 * ε ≤ b + 2 * ε ^ 2 by linarith)
    Swap.slope_pos.le
  have hmain : A ε ≤ Swap.slope * b + 2 * (1 + Swap.slope) * ε ^ 2 := by nlinarith
  have hemax0 : 0 ≤ 2 * b / beta0 := by positivity
  have hesq := (sq_le_sq₀ hε hemax0).2 hemax
  have hecoef := mul_le_mul_of_nonneg_left hesq (show 0 ≤ 2 * (1 + Swap.slope) by positivity)
  have healg : 2 * (1 + Swap.slope) * (2 * b / beta0) ^ 2 =
      (8 * (1 + Swap.slope) / beta0 ^ 2) * b ^ 2 := by ring
  rw [healg] at hecoef
  have hc := mul_lt_mul_of_pos_right matching_constant_lt_forty (sq_pos_of_pos hb)
  linarith

#print axioms matchingOutput_mem_Q2
#print axioms matchingVector_qa
#print axioms matchingK_trace
#print axioms matching_constant_lt_forty
#print axioms exact_second_from_remainder
#print axioms exact_match_quadratic_bound


/-- 反向尖锐跳跃交换两个首阶系数。 -/
def oppositeVector : PauliVec := star matchingVector

lemma energy_star (v : PauliVec) : Swap.energy (star v) = Swap.energy v := by
  simp [Swap.energy]

lemma cross_star (v : PauliVec) : Swap.cross (star v) = -Swap.cross v := by
  simp [Swap.cross, Complex.mul_im]
  ring

lemma oppositeVector_qa : Swap.qa 0 oppositeVector = beta0 := by
  unfold Swap.qa oppositeVector
  rw [energy_star, cross_star]
  simpa [Swap.qb] using matchingVector_qb

lemma oppositeVector_qb : Swap.qb 0 oppositeVector = alpha0 := by
  unfold Swap.qb oppositeVector
  rw [energy_star, cross_star]
  simpa [Swap.qa, sub_eq_add_neg] using matchingVector_qa

lemma alpha0_pos : 0 < alpha0 := by
  rw [alpha0_eq_slope_mul_beta0]
  exact mul_pos Swap.slope_pos beta0_pos

lemma alpha0_lt_beta0 : alpha0 < beta0 := by
  rw [alpha0_eq_slope_mul_beta0]
  nlinarith [mul_lt_mul_of_pos_right Swap.slope_lt_one beta0_pos]

lemma coefficient_determinant_pos : 0 < beta0 ^ 2 - alpha0 ^ 2 := by
  nlinarith [alpha0_pos, beta0_pos, alpha0_lt_beta0]

def directionLambda (u v : ℝ) : ℝ := (beta0 * v - alpha0 * u) / (beta0 ^ 2 - alpha0 ^ 2)
def directionNu (u v : ℝ) : ℝ := (beta0 * u - alpha0 * v) / (beta0 ^ 2 - alpha0 ^ 2)

lemma directionLambda_nonneg {u v : ℝ} (hv : Swap.slope * u ≤ v) : 0 ≤ directionLambda u v := by
  unfold directionLambda
  apply div_nonneg _ coefficient_determinant_pos.le
  rw [alpha0_eq_slope_mul_beta0]
  nlinarith [mul_le_mul_of_nonneg_left hv beta0_pos.le]

lemma directionNu_nonneg {u v : ℝ} (hu : Swap.slope * v ≤ u) : 0 ≤ directionNu u v := by
  unfold directionNu
  apply div_nonneg _ coefficient_determinant_pos.le
  rw [alpha0_eq_slope_mul_beta0]
  nlinarith [mul_le_mul_of_nonneg_left hu beta0_pos.le]

lemma direction_coefficients_a (u v : ℝ) :
    directionLambda u v * alpha0 + directionNu u v * beta0 = u := by
  have hd := ne_of_gt coefficient_determinant_pos
  unfold directionLambda directionNu
  field_simp
  ring

lemma direction_coefficients_b (u v : ℝ) :
    directionLambda u v * beta0 + directionNu u v * alpha0 = v := by
  have hd := ne_of_gt coefficient_determinant_pos
  unfold directionLambda directionNu
  field_simp
  ring

/-- 凸锥中两个固定 rank-one K 的组合，所有 ε≥0 仍是同一个合法时间不变生成元。 -/
def directionK (u v ε : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  ε • (directionLambda u v • singleK matchingVector + directionNu u v • singleK oppositeVector)

def directionOutput (u v ε : ℝ) : ℝ × ℝ := canonicalOutput matchingHamiltonian (directionK u v ε) 1

lemma directionK_posSemidef {u v ε : ℝ} (hu : Swap.slope * v ≤ u)
    (hv : Swap.slope * u ≤ v) (hε : 0 ≤ ε) : (directionK u v ε).PosSemidef := by
  apply Matrix.PosSemidef.smul
  · exact ((singleK_posSemidef matchingVector).smul (directionLambda_nonneg hv)).add
      ((singleK_posSemidef oppositeVector).smul (directionNu_nonneg hu))
  · exact hε

lemma directionOutput_mem_Q2 {u v ε : ℝ} (hu : Swap.slope * v ≤ u)
    (hv : Swap.slope * u ≤ v) (hε : 0 ≤ ε) : directionOutput u v ε ∈ Q2 :=
  canonicalOutput_mem_Q2 _ _ (directionK_posSemidef hu hv hε) 1 (by norm_num)

lemma directionOutput_zero (u v : ℝ) : directionOutput u v 0 = (0, 0) := by
  simp [directionOutput, directionK, matchingHamiltonian, canonicalOutput_x_zero]

lemma continuous_directionOutput (u v : ℝ) : Continuous (directionOutput u v) := by
  unfold directionOutput canonicalOutput canonicalEvolution directionK
  unfold augmentedGenerator blochMatrix drift
  fun_prop

#print axioms oppositeVector_qa
#print axioms directionOutput_mem_Q2
#print axioms direction_coefficients_a


lemma singleK_real_smul (v : PauliVec) (a : ℝ) :
    singleK (a • v) = (a * a) • singleK v := by
  ext i j
  simp [singleK, Complex.real_smul]
  ring

lemma matchingK_eq_single_jump {ε : ℝ} (hε : 0 ≤ ε) :
    kossakowski (fun _ : Fin 1 => Real.sqrt ε • matchingVector) = matchingK ε := by
  have hk : kossakowski (fun _ : Fin 1 => Real.sqrt ε • matchingVector) =
      singleK (Real.sqrt ε • matchingVector) := by
    ext i j
    simp [kossakowski, singleK]
  rw [hk, singleK_real_smul, Real.mul_self_sqrt hε]
  rfl

/-- 候选曲线由一个明确有限跳跃实现，不只通过闭包成员关系实现。 -/
theorem matchingOutput_eq_finiteOutput {ε : ℝ} (hε : 0 ≤ ε) :
    finiteOutput (hamiltonian matchingHamiltonian)
      (fun _ : Fin 1 => pauli (Real.sqrt ε • matchingVector)) 1 = matchingOutput ε := by
  rw [finiteOutput_canonical_pauli, matchingK_eq_single_jump hε]
  rfl

lemma matchingOutput_mem_finiteOutputs {ε : ℝ} (hε : 0 ≤ ε) : matchingOutput ε ∈ finiteOutputs :=
  ⟨1, hamiltonian matchingHamiltonian,
    (fun _ : Fin 1 => pauli (Real.sqrt ε • matchingVector)), 1,
    hamiltonian_hermitian _, by norm_num, matchingOutput_eq_finiteOutput hε⟩

#print axioms matchingOutput_eq_finiteOutput

open Filter
open scoped Topology

/-- 二次余项给出右侧归一化曲线极限。 -/
lemma normalized_tendsto_of_quadratic (f : ℝ → ℝ) (c C : ℝ)
    (hrem : ∀ ε, 0 < ε → |f ε - c * ε| ≤ C * ε ^ 2) :
    Tendsto (fun ε => f ε / ε) (nhdsWithin 0 (Set.Ioi 0)) (nhds c) := by
  have hlim : Tendsto (fun ε : ℝ => C * ε) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using tendsto_const_nhds.mul (show Tendsto (fun ε : ℝ => ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) from nhdsWithin_le_nhds)
  have hb : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0), ‖f ε / ε - c‖ ≤ C * ε := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hεp : 0 < ε := hε
    have he : f ε / ε - c = (f ε - c * ε) / ε := by field_simp
    rw [he, Real.norm_eq_abs, abs_div, abs_of_pos hεp]
    apply (div_le_iff₀ hεp).2
    simpa [pow_two, mul_assoc] using hrem ε hεp
  have hh := squeeze_zero_norm' hb hlim
  have hadd := hh.add_const c
  simpa using hadd

/-- 真正 Q2 中的连续二次匹配曲线产生 mathlib 正切锥中的方向。 -/
lemma quadratic_curve_mem_posTangent (P : ℝ → ℝ × ℝ) (u v C : ℝ)
    (hP : Continuous P) (hP0 : P 0 = (0, 0))
    (hmem : ∀ ε, 0 < ε → P ε ∈ Q2)
    (ha : ∀ ε, 0 < ε → |(P ε).1 - u * ε| ≤ C * ε ^ 2)
    (hb : ∀ ε, 0 < ε → |(P ε).2 - v * ε| ≤ C * ε ^ 2) :
    (u, v) ∈ posTangentConeAt Q2 (0, 0) := by
  have hpa := normalized_tendsto_of_quadratic (fun ε => (P ε).1) u C ha
  have hpb := normalized_tendsto_of_quadratic (fun ε => (P ε).2) v C hb
  apply mem_tangentConeAt_of_seq (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (fun ε => Real.toNNReal (ε⁻¹)) P
  · have hh : Tendsto P (nhds (0 : ℝ)) (nhds (P 0)) := hP.tendsto 0
    simpa only [hP0, Prod.mk_zero_zero] using hh.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    change (0 : ℝ × ℝ) + P ε ∈ Q2
    simpa using hmem ε hε
  · apply (hpa.prodMk_nhds hpb).congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hεp : 0 < ε := hε
    ext <;> simp [NNReal.smul_def, Real.toNNReal_of_nonneg (inv_nonneg.mpr hεp.le),
      div_eq_mul_inv, mul_comm]

open GKSLBounds DissipativeFlow

lemma dissipativeCLM_add (K L : Matrix (Fin 3) (Fin 3) ℂ) :
    dissipativeCLM (K + L) = dissipativeCLM K + dissipativeCLM L := by
  have hr : (K + L).map Complex.re = K.map Complex.re + L.map Complex.re := by
    ext i j
    simp
  have hc : drift (K + L) = drift K + drift L := by
    ext i
    fin_cases i <;> simp [drift] <;> ring
  have hD : canonicalD ((K + L).map Complex.re) =
      canonicalD (K.map Complex.re) + canonicalD (L.map Complex.re) := by
    rw [hr]
    simp only [canonicalD, Matrix.trace_add, add_smul, smul_sub]
    module
  apply ContinuousLinearMap.ext
  intro x
  simp only [dissipativeCLM, hD, hc, map_add, neg_add, augmentedCLM_apply,
    _root_.add_apply, _root_.neg_apply]
  apply Prod.ext
  · simp
  · ext i
    simp [euclid]
    ring

lemma firstOrderReturn_add (h : BlochVec) (K L : Matrix (Fin 3) (Fin 3) ℂ) (t s : ℝ) :
    firstOrderReturn h (K + L) t s = firstOrderReturn h K t s + firstOrderReturn h L t s := by
  rw [firstOrderReturn_eq_integral, firstOrderReturn_eq_integral, firstOrderReturn_eq_integral]
  simp only [dissipativeCLM_add, _root_.add_apply, map_add]
  have hc (J : Matrix (Fin 3) (Fin 3) ℂ) : Continuous (fun r : ℝ =>
      diagonalReadout s ((NormedSpace.exp ((t-r) • hamiltonianCLM h))
        (dissipativeCLM J ((NormedSpace.exp (r • hamiltonianCLM h)) (basisInitial s))))) := by
    let read : (AugmentedSpace →L[ℝ] AugmentedSpace) →L[ℝ] ℝ :=
      (diagonalReadout s).comp (ContinuousLinearMap.apply ℝ AugmentedSpace (basisInitial s))
    have hh := read.continuous.comp
      (continuous_duhamel_kernel (hamiltonianCLM h) (hamiltonianCLM h) (dissipativeCLM J) t)
    simpa only [read, Function.comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      mul_apply_eq_comp] using hh
  exact intervalIntegral.integral_add ((hc K).intervalIntegrable 0 t) ((hc L).intervalIntegrable 0 t)

#print axioms matchingVector_qa
#print axioms quadratic_curve_mem_posTangent
#print axioms firstOrderReturn_add

lemma matching_unitary_probability : unitaryProbability matchingHamiltonian 1 = 0 := by
  simp [unitaryProbability, matchingHamiltonian, canonicalEvolution,
    augmentedGenerator_x_zero, exp_rotationGenerator4, rotation4]

/-- 两个无迹跳跃直接实现整个方向族的同一个规范生成元。 -/
def directionJumps (u v ε : ℝ) : Fin 2 → PauliVec :=
  ![Real.sqrt (ε * directionLambda u v) • matchingVector,
    Real.sqrt (ε * directionNu u v) • oppositeVector]

lemma directionK_eq_two_jumps {u v ε : ℝ} (hu : Swap.slope * v ≤ u)
    (hv : Swap.slope * u ≤ v) (hε : 0 ≤ ε) :
    kossakowski (directionJumps u v ε) = directionK u v ε := by
  have hlambda := mul_nonneg hε (directionLambda_nonneg hv)
  have hnu := mul_nonneg hε (directionNu_nonneg hu)
  have he : kossakowski (directionJumps u v ε) =
      singleK (Real.sqrt (ε * directionLambda u v) • matchingVector) +
        singleK (Real.sqrt (ε * directionNu u v) • oppositeVector) := by
    ext i j
    simp [kossakowski, directionJumps, singleK, Fin.sum_univ_two]
  rw [he, singleK_real_smul, singleK_real_smul, Real.mul_self_sqrt hlambda, Real.mul_self_sqrt hnu]
  simp only [directionK, smul_add, smul_smul]

lemma directionOutput_eq_finiteOutput {u v ε : ℝ} (hu : Swap.slope * v ≤ u)
    (hv : Swap.slope * u ≤ v) (hε : 0 ≤ ε) :
    finiteOutput (hamiltonian matchingHamiltonian)
      (fun i : Fin 2 => pauli (directionJumps u v ε i)) 1 = directionOutput u v ε := by
  rw [finiteOutput_canonical_pauli, directionK_eq_two_jumps hu hv hε]
  rfl

#print axioms matching_unitary_probability
#print axioms directionOutput_eq_finiteOutput



/-- 实际增广首阶积分对尖锐无迹跳跃的精确取值。 -/
lemma matching_single_first_a :
    firstOrderReturn matchingHamiltonian (singleK matchingVector) 1 1 = alpha0 := by
  have hh := SwapComparison.firstOrderReturn_single_a 0 matchingVector
  simpa only [Swap.frequency_zero, matchingHamiltonian, matchingVector_qa] using hh

lemma matching_single_first_b :
    firstOrderReturn matchingHamiltonian (singleK matchingVector) 1 (-1) = beta0 := by
  have hh := SwapComparison.firstOrderReturn_single_b 0 matchingVector
  simpa only [Swap.frequency_zero, matchingHamiltonian, matchingVector_qb] using hh

lemma opposite_single_first_a :
    firstOrderReturn matchingHamiltonian (singleK oppositeVector) 1 1 = beta0 := by
  have hh := SwapComparison.firstOrderReturn_single_a 0 oppositeVector
  simpa only [Swap.frequency_zero, matchingHamiltonian, oppositeVector_qa] using hh

lemma opposite_single_first_b :
    firstOrderReturn matchingHamiltonian (singleK oppositeVector) 1 (-1) = alpha0 := by
  have hh := SwapComparison.firstOrderReturn_single_b 0 oppositeVector
  simpa only [Swap.frequency_zero, matchingHamiltonian, oppositeVector_qb] using hh

lemma matching_first_order_a (ε : ℝ) :
    firstOrderReturn matchingHamiltonian (matchingK ε) 1 1 = alpha0 * ε := by
  rw [matchingK, firstOrderReturn_real_smul, matching_single_first_a, mul_comm]

lemma matching_first_order_b (ε : ℝ) :
    firstOrderReturn matchingHamiltonian (matchingK ε) 1 (-1) = beta0 * ε := by
  rw [matchingK, firstOrderReturn_real_smul, matching_single_first_b, mul_comm]

/-- 真实候选输出的一阶展开；余项从一般 GKSL 收缩性推出。 -/
theorem matchingOutput_quadratic_remainder {ε : ℝ} (hε : 0 ≤ ε) :
    |(matchingOutput ε).1 - alpha0 * ε| ≤ 2 * ε ^ 2 ∧
    |(matchingOutput ε).2 - beta0 * ε| ≤ 2 * ε ^ 2 := by
  have hh := canonicalOutput_first_order_common_le matchingHamiltonian (matchingK ε)
    (matchingK_posSemidef hε) (t := 1) (by norm_num)
  have hd : dissipationSize (matchingK ε) = 3 * ε / 8 := matchingK_trace ε
  rw [matching_unitary_probability, matching_first_order_a, matching_first_order_b, hd] at hh
  simp only [sub_zero, one_pow, mul_one] at hh
  have hc : 8 * (3 * ε / 8) ^ 2 ≤ 2 * ε ^ 2 := by nlinarith [sq_nonneg ε]
  exact ⟨hh.1.trans hc, hh.2.trans hc⟩

/-- 每个小的正第二概率都有严格正有限参数精确实现，不只是一条逼近序列。 -/
theorem matchingOutput_exact_second {b : ℝ} (hb : 0 < b) (hbsmall : b ≤ beta0 ^ 2 / 8) :
    ∃ ε, 0 < ε ∧ ε ≤ 2 * b / beta0 ∧ (matchingOutput ε).2 = b ∧
      (matchingOutput ε).1 < Swap.slope * b + 40 * b ^ 2 := by
  obtain ⟨ε, he, hemax, hmatch⟩ := exact_second_from_remainder
    (fun ε => (matchingOutput ε).2) continuous_matchingOutput.snd
    (by rw [matchingOutput_zero])
    (fun ε he => (matchingOutput_quadratic_remainder he).2) hb hbsmall
  exact ⟨ε, he, hemax, hmatch,
    exact_match_quadratic_bound (fun ε => (matchingOutput ε).1) (fun ε => (matchingOutput ε).2)
      (fun ε he => (matchingOutput_quadratic_remainder he).1)
      (fun ε he => (matchingOutput_quadratic_remainder he).2) hb he.le hemax hmatch⟩

/-- 原始有限 GKSL 输出集合中的逐点存在定理。 -/
theorem every_small_b_finite_matching {b : ℝ} (hb : 0 < b) (hbsmall : b ≤ beta0 ^ 2 / 8) :
    ∃ a, (a, b) ∈ finiteOutputs ∧ a < Swap.slope * b + 40 * b ^ 2 := by
  obtain ⟨ε, he, hemax, hmatch, hbound⟩ := matchingOutput_exact_second hb hbsmall
  refine ⟨(matchingOutput ε).1, ?_, hbound⟩
  have hh := matchingOutput_mem_finiteOutputs he.le
  have hp : matchingOutput ε = ((matchingOutput ε).1, b) := Prod.ext rfl hmatch
  rwa [hp] at hh

lemma small_b_mem_unitInterval {b : ℝ} (hb : 0 < b) (hbsmall : b ≤ beta0 ^ 2 / 8) :
    b ∈ Set.Icc (0 : ℝ) 1 := by
  have hβ := (sq_le_sq₀ beta0_pos.le (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 beta0_lt_half.le
  exact ⟨hb.le, by nlinarith⟩

/-- 对真实 Q2 切片最小值的上界，不把候选曲线定义成边界。 -/
theorem lowerBoundary_small_upper_strict {b : ℝ} (hb : 0 < b) (hbsmall : b ≤ beta0 ^ 2 / 8) :
    lowerBoundary b < Swap.slope * b + 40 * b ^ 2 := by
  obtain ⟨a, ha, habound⟩ := every_small_b_finite_matching hb hbsmall
  exact (lowerBoundary_le_of_mem (small_b_mem_unitInterval hb hbsmall)
    (subset_closure ha)).trans_lt habound

theorem lowerBoundary_small_upper {b : ℝ} (hb : 0 < b) (hbsmall : b ≤ beta0 ^ 2 / 8) :
    lowerBoundary b ≤ Swap.slope * b + 40 * b ^ 2 :=
  (lowerBoundary_small_upper_strict hb hbsmall).le

lemma direction_first_order_a (u v ε : ℝ) :
    firstOrderReturn matchingHamiltonian (directionK u v ε) 1 1 = u * ε := by
  simp only [directionK, firstOrderReturn_real_smul, firstOrderReturn_add,
    matching_single_first_a, opposite_single_first_a]
  rw [direction_coefficients_a, mul_comm]

lemma direction_first_order_b (u v ε : ℝ) :
    firstOrderReturn matchingHamiltonian (directionK u v ε) 1 (-1) = v * ε := by
  simp only [directionK, firstOrderReturn_real_smul, firstOrderReturn_add,
    matching_single_first_b, opposite_single_first_b]
  rw [direction_coefficients_b, mul_comm]

/-- 方向族的常数可以依赖方向，但不依赖 ε 或 Hamiltonian 范数。 -/
def directionRemainderConstant (u v : ℝ) : ℝ :=
  8 * dissipationSize
    (directionLambda u v • singleK matchingVector + directionNu u v • singleK oppositeVector) ^ 2

theorem directionOutput_quadratic_remainder {u v ε : ℝ} (hu : Swap.slope * v ≤ u)
    (hv : Swap.slope * u ≤ v) (hε : 0 ≤ ε) :
    |(directionOutput u v ε).1 - u * ε| ≤ directionRemainderConstant u v * ε ^ 2 ∧
    |(directionOutput u v ε).2 - v * ε| ≤ directionRemainderConstant u v * ε ^ 2 := by
  have hh := canonicalOutput_first_order_common_le matchingHamiltonian (directionK u v ε)
    (directionK_posSemidef hu hv hε) (t := 1) (by norm_num)
  rw [matching_unitary_probability, direction_first_order_a, direction_first_order_b] at hh
  have hd : 8 * dissipationSize (directionK u v ε) ^ 2 * (1 : ℝ) ^ 2 =
      directionRemainderConstant u v * ε ^ 2 := by
    simp only [directionK, dissipationSize_real_smul, directionRemainderConstant]
    ring
  rw [hd] at hh
  simpa only [directionOutput, sub_zero] using hh

/-- 每个允许方向由两个明确合法跳跃实现为真实 Q2 的正切方向。 -/
theorem all_allowed_directions_mem_posTangent {u v : ℝ} (hu : Swap.slope * v ≤ u)
    (hv : Swap.slope * u ≤ v) : (u, v) ∈ posTangentConeAt Q2 (0, 0) := by
  apply quadratic_curve_mem_posTangent (directionOutput u v) u v
    (directionRemainderConstant u v) (continuous_directionOutput u v) (directionOutput_zero u v)
  · exact fun ε he => directionOutput_mem_Q2 hu hv he.le
  · exact fun ε he => (directionOutput_quadratic_remainder hu hv he.le).1
  · exact fun ε he => (directionOutput_quadratic_remainder hu hv he.le).2

#print axioms matching_single_first_a
#print axioms matchingOutput_quadratic_remainder
#print axioms matchingOutput_exact_second
#print axioms every_small_b_finite_matching
#print axioms lowerBoundary_small_upper
#print axioms directionOutput_quadratic_remainder
#print axioms all_allowed_directions_mem_posTangent
/-- 实际有限 GKSL 匹配族在交换点的归一化输出极限。 -/
theorem matchingOutput_scaled_tendsto :
    Tendsto (fun ε => ((matchingOutput ε).1 / ε, (matchingOutput ε).2 / ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (alpha0, beta0)) := by
  exact (normalized_tendsto_of_quadratic (fun ε => (matchingOutput ε).1) alpha0 2
    (fun ε he => (matchingOutput_quadratic_remainder he.le).1)).prodMk_nhds
      (normalized_tendsto_of_quadratic (fun ε => (matchingOutput ε).2) beta0 2
        (fun ε he => (matchingOutput_quadratic_remainder he.le).2))

/-- 尖锐斜率是实际输出比的极限，非仅形式二次型的比值。 -/
theorem matchingOutput_ratio_tendsto :
    Tendsto (fun ε => (matchingOutput ε).1 / (matchingOutput ε).2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds Swap.slope) := by
  have ha := normalized_tendsto_of_quadratic (fun ε => (matchingOutput ε).1) alpha0 2
    (fun ε he => (matchingOutput_quadratic_remainder he.le).1)
  have hb := normalized_tendsto_of_quadratic (fun ε => (matchingOutput ε).2) beta0 2
    (fun ε he => (matchingOutput_quadratic_remainder he.le).2)
  have hh := ha.div hb (ne_of_gt beta0_pos)
  have hab : alpha0 / beta0 = Swap.slope := by
    rw [alpha0_eq_slope_mul_beta0, mul_div_cancel_right₀ _ (ne_of_gt beta0_pos)]
  rw [hab] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact div_div_div_cancel_right₀ (ne_of_gt hε) _ _

#print axioms matchingOutput_scaled_tendsto
#print axioms matchingOutput_ratio_tendsto

end TwoStateQuantumEmbedding.SwapMatching
