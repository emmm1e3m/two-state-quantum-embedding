import TwoStateQuantumEmbedding.FirstOrderBridge
import TwoStateQuantumEmbedding.CanonicalGradient
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! 首交换参考点的实际梯度识别与连续性。 -/
noncomputable section
open Matrix Complex NormedSpace Filter Set
open scoped BigOperators Topology ContDiff ComplexOrder Matrix.Norms.Operator

namespace TwoStateQuantumEmbedding.SwapRankOne
open GKSLAlgebra CanonicalBloch GKSLBounds SwapComparison
open ExponentialGradient CanonicalGradient TraceGradient
set_option maxRecDepth 2500
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

def referenceH : BlochVec := ![Real.pi, 0, 0]
def referenceParameters : Parameters := (referenceH, 0)

def operatorReadout (s : ℝ) :
    (AugmentedSpace →L[ℝ] AugmentedSpace) →L[ℝ] ℝ :=
  (diagonalReadout s).comp (ContinuousLinearMap.apply ℝ AugmentedSpace (basisInitial s))

/-- 真实增广指数沿耗散方向的导数恰为正式 firstOrderReturn。 -/
theorem hasDerivAt_readout_radial (h : BlochVec) (K : KMatrix) (s : ℝ) :
    HasDerivAt (fun t : ℝ => operatorReadout s
      (exp (hamiltonianCLM h + t • dissipativeCLM K)))
      (firstOrderReturn h K 1 s) 0 := by
  have hp : HasDerivAt (fun t : ℝ => hamiltonianCLM h + t • dissipativeCLM K)
      (dissipativeCLM K) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (dissipativeCLM K)).const_add
      (hamiltonianCLM h)
  have he := (hasFDerivAt_exp_integral
    (hamiltonianCLM h + (0 : ℝ) • dissipativeCLM K)).comp_hasDerivAt (0 : ℝ) hp
  have hbase : hamiltonianCLM h + (0 : ℝ) • dissipativeCLM K = hamiltonianCLM h := by
    module
  rw [hbase] at he
  have hr := (operatorReadout s).hasFDerivAt.comp_hasDerivAt (0 : ℝ) he
  convert hr using 1 <;> rfl

theorem radial_a_eq_readout (h : BlochVec) (K : KMatrix) :
    (fun t : ℝ => (canonicalOutput h (t • K) 1).1) =
      (fun t => operatorReadout 1 (exp (hamiltonianCLM h + t • dissipativeCLM K))) := by
  funext t
  rw [canonicalOutput_fst_eq_readout, one_smul, canonicalCLM_eq_add,
    dissipativeCLM_real_smul]
  rfl

theorem radial_b_eq_readout (h : BlochVec) (K : KMatrix) :
    (fun t : ℝ => (canonicalOutput h (t • K) 1).2) =
      (fun t => operatorReadout (-1) (exp (hamiltonianCLM h + t • dissipativeCLM K))) := by
  funext t
  rw [canonicalOutput_snd_eq_readout, one_smul, canonicalCLM_eq_add,
    dissipativeCLM_real_smul]
  rfl

theorem kDerivative_zero_a (h : BlochVec) (K : KMatrix) :
    kDerivative (1/2) (1/2) (h, 0) K = firstOrderReturn h K 1 1 := by
  have ha : HasDerivAt (fun t : ℝ => (canonicalOutput h (t • K) 1).1)
      (kDerivative (1/2) (1/2) (h, 0) K) 0 := by
    simpa [Function.comp_def] using (hasStrictFDerivAt_a_K h ((0 : ℝ) • K)).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).smul_const K)
  rw [radial_a_eq_readout] at ha
  exact ha.unique (hasDerivAt_readout_radial h K 1)

theorem kDerivative_zero_b (h : BlochVec) (K : KMatrix) :
    kDerivative (1/2) (-1/2) (h, 0) K = firstOrderReturn h K 1 (-1) := by
  have hb : HasDerivAt (fun t : ℝ => (canonicalOutput h (t • K) 1).2)
      (kDerivative (1/2) (-1/2) (h, 0) K) 0 := by
    simpa [Function.comp_def] using (hasStrictFDerivAt_b_K h ((0 : ℝ) • K)).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).smul_const K)
  rw [radial_b_eq_readout] at hb
  exact hb.unique (hasDerivAt_readout_radial h K (-1))

theorem reference_derivative_single_a (v : PauliVec) :
    kDerivative (1/2) (1/2) referenceParameters (singleK v) = Swap.qa 0 v := by
  rw [referenceParameters, kDerivative_zero_a]
  simpa [referenceH, Swap.frequency_zero] using firstOrderReturn_single_a 0 v

theorem reference_derivative_single_b (v : PauliVec) :
    kDerivative (1/2) (-1/2) referenceParameters (singleK v) = Swap.qb 0 v := by
  rw [referenceParameters, kDerivative_zero_b]
  simpa [referenceH, Swap.frequency_zero] using firstOrderReturn_single_b 0 v

/-- Hermitian 梯度由所有秩一 PSD 测试唯一确定。 -/
theorem hermitian_eq_of_single_pairing (A B : KMatrix)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (ht : ∀ v : PauliVec, (A * singleK v).trace.re = (B * singleK v).trace.re) :
    A = B := by
  let S := A - B
  have hS : S.IsHermitian := hA.sub hB
  have hz : ∀ v : PauliVec, star v ⬝ᵥ (S *ᵥ v) = 0 := by
    intro v
    apply Complex.ext
    · have ht' := ht v
      have htr : (S * singleK v).trace.re = 0 := by
        simp [S, Matrix.sub_mul, Matrix.trace_sub, ht']
      change (S * Matrix.vecMulVec v (star v)).trace.re = 0 at htr
      rw [Swap.trace_matrix_outer] at htr
      exact htr
    · have hc := congrArg Complex.im (hS.star_dotProduct_mulVec_comm v v)
      simp only [Complex.star_def, Complex.conj_im] at hc
      change (star v ⬝ᵥ S *ᵥ v).im = 0
      linarith
  have hpos : S.PosSemidef := Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hS
    (fun v => by rw [hz])
  have hzero : S = 0 := by
    ext i j
    have hv := hpos.dotProduct_mulVec_zero_iff.mp (hz (Pi.single j 1))
    have hij := congrFun hv i
    simpa using hij
  exact sub_eq_zero.mp hzero

theorem reference_kGradient_a :
    kGradient (1/2) (1/2) referenceParameters = Swap.matrixQa 0 := by
  apply hermitian_eq_of_single_pairing _ _ (kGradient_isHermitian _ _ _)
    (Swap.referenceMatrix_hermitian _)
  intro v
  rw [← kGradient_pairing _ _ _ _
    (show (singleK v).IsHermitian from (Matrix.posSemidef_vecMulVec_self_star v).isHermitian)]
  rw [reference_derivative_single_a]
  change Swap.qa 0 v = (Swap.matrixQa 0 * Matrix.vecMulVec v (star v)).trace.re
  rw [Swap.trace_matrix_outer, Swap.matrixQa_form]
  rfl

theorem reference_kGradient_b :
    kGradient (1/2) (-1/2) referenceParameters = Swap.matrixQb 0 := by
  apply hermitian_eq_of_single_pairing _ _ (kGradient_isHermitian _ _ _)
    (Swap.referenceMatrix_hermitian _)
  intro v
  rw [← kGradient_pairing _ _ _ _
    (show (singleK v).IsHermitian from (Matrix.posSemidef_vecMulVec_self_star v).isHermitian)]
  rw [reference_derivative_single_b]
  change Swap.qb 0 v = (Swap.matrixQb 0 * Matrix.vecMulVec v (star v)).trace.re
  rw [Swap.trace_matrix_outer, Swap.matrixQb_form]
  rfl

/-- 迹一参考投影；与 normalized kernelVector 外积完全相同。 -/
def referenceW : KMatrix := (2/3 : ℝ) • singleK Swap.kernelVector

theorem kernelVector_mass : Swap.mass Swap.kernelVector = 3/2 := by
  simp [Swap.mass, Swap.kernelVector, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  nlinarith [Swap.rootTwo_sq]

theorem referenceW_eq_normalized : referenceW =
    (Swap.mass Swap.kernelVector)⁻¹ • singleK Swap.kernelVector := by
  rw [kernelVector_mass]
  norm_num [referenceW]

theorem referenceW_eq_outer : referenceW =
    ((2/3 : ℝ) : ℂ) • Matrix.vecMulVec Swap.kernelVector (star Swap.kernelVector) := by
  ext i j
  simp [referenceW, singleK, Matrix.vecMulVec, Matrix.smul_apply, smul_eq_mul]

theorem referenceW_posSemidef : referenceW.PosSemidef :=
  (show (singleK Swap.kernelVector).PosSemidef from
    Matrix.posSemidef_vecMulVec_self_star _).smul (by norm_num)

theorem kernel_qb_value : Swap.qb 0 Swap.kernelVector = 1 + 2*Swap.rootTwo/Real.pi := by
  simp [Swap.qb, Swap.energy, Swap.cross, Swap.kernelVector, Swap.frequency_zero,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring_nf
  rw [Swap.rootTwo_sq]
  norm_num [Complex.mul_re]
  ring

theorem kernel_qa_value : Swap.qa 0 Swap.kernelVector = Swap.slope * Swap.qb 0 Swap.kernelVector := by
  apply (Swap.first_swap_equality_iff _).mpr
  simp [Swap.kernelVector]

def referenceRadial : ℝ := (2/3 : ℝ) * (1 + 2*Swap.rootTwo/Real.pi)

theorem referenceRadial_pos : 0 < referenceRadial := by
  unfold referenceRadial
  positivity [Swap.rootTwo_pos, Real.pi_pos]

theorem reference_radial_b :
    kDerivative (1/2) (-1/2) referenceParameters referenceW = referenceRadial := by
  rw [referenceW, map_smul, reference_derivative_single_b, kernel_qb_value]
  rfl

theorem reference_radial_a :
    kDerivative (1/2) (1/2) referenceParameters referenceW = Swap.slope * referenceRadial := by
  rw [referenceW, map_smul, reference_derivative_single_a, kernel_qa_value, kernel_qb_value]
  change (2/3 : ℝ) * (Swap.slope * _) = Swap.slope * ((2/3 : ℝ) * _)
  ring

theorem analyticAt_canonicalScalar (α β : ℝ) (p : Parameters) :
    AnalyticAt ℝ (canonicalScalar α β) p := by
  rw [show canonicalScalar α β = (fun q => measurementCLM α β
    (exp (canonicalGeneratorCLM q))) from funext (canonicalScalar_eq α β)]
  exact ((measurementCLM α β).analyticAt _).comp
    ((exp_analytic (𝕂 := ℝ) (canonicalGeneratorCLM p)).comp (canonicalGeneratorCLM.analyticAt p))

theorem continuous_canonicalScalarDerivative (α β : ℝ) :
    Continuous (canonicalScalarDerivative α β) := by
  have hd : ContDiff ℝ ω (canonicalScalar α β) :=
    contDiff_iff_contDiffAt.mpr (fun p => (analyticAt_canonicalScalar α β p).contDiffAt)
  have hc := hd.continuous_fderiv (by simp)
  have he : fderiv ℝ (canonicalScalar α β) = canonicalScalarDerivative α β := by
    funext p
    exact (hasStrictFDerivAt_canonicalScalar α β p).hasFDerivAt.fderiv
  rwa [he] at hc

theorem continuous_kDerivative (α β : ℝ) : Continuous (kDerivative α β) := by
  exact (continuous_canonicalScalarDerivative α β).clm_comp continuous_const

theorem continuous_hermitianGradient :
    Continuous (hermitianGradient : (KMatrix →L[ℝ] ℝ) → KMatrix) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [hermitianGradient, rawGradient, Matrix.smul_apply, Matrix.add_apply,
    Matrix.conjTranspose_apply]
  fun_prop

theorem continuous_kGradient (α β : ℝ) : Continuous (kGradient α β) :=
  continuous_hermitianGradient.comp (continuous_kDerivative α β)

abbrev NormalizedParameters := Parameters × KMatrix
def referenceNormalized : NormalizedParameters := (referenceParameters, referenceW)
def radialA (q : NormalizedParameters) : ℝ := kDerivative (1/2) (1/2) q.1 q.2
def radialB (q : NormalizedParameters) : ℝ := kDerivative (1/2) (-1/2) q.1 q.2
def multiplier (q : NormalizedParameters) : ℝ := radialA q / radialB q
def dualNormal (q : NormalizedParameters) : KMatrix :=
  kGradient (1/2) (1/2) q.1 - multiplier q • kGradient (1/2) (-1/2) q.1
def referenceDual : KMatrix := Swap.matrixQa 0 - Swap.slope • Swap.matrixQb 0

theorem continuous_radialA : Continuous radialA :=
  ((continuous_kDerivative (1/2) (1/2)).comp continuous_fst).clm_apply continuous_snd
theorem continuous_radialB : Continuous radialB :=
  ((continuous_kDerivative (1/2) (-1/2)).comp continuous_fst).clm_apply continuous_snd

theorem radialB_reference : radialB referenceNormalized = referenceRadial := reference_radial_b
theorem radialA_reference : radialA referenceNormalized = Swap.slope * referenceRadial := reference_radial_a

theorem multiplier_reference : multiplier referenceNormalized = Swap.slope := by
  rw [multiplier, radialA_reference, radialB_reference]
  exact mul_div_cancel_right₀ _ referenceRadial_pos.ne'

theorem dualNormal_reference : dualNormal referenceNormalized = referenceDual := by
  rw [dualNormal, multiplier_reference]
  exact congrArg₂ (· - ·) reference_kGradient_a
    (congrArg (fun A : KMatrix => Swap.slope • A) reference_kGradient_b)

theorem continuousAt_multiplier : ContinuousAt multiplier referenceNormalized := by
  exact continuous_radialA.continuousAt.div continuous_radialB.continuousAt
    (by rw [radialB_reference]; exact referenceRadial_pos.ne')

theorem continuousAt_dualNormal : ContinuousAt dualNormal referenceNormalized := by
  exact ((continuous_kGradient (1/2) (1/2)).comp continuous_fst).continuousAt.sub
    (continuousAt_multiplier.smul
      ((continuous_kGradient (1/2) (-1/2)).comp continuous_fst).continuousAt)

/-- 取第三坐标为零的固定二维复子空间即可获得严格谱隙。 -/
def positiveEmbedding : (Fin 2 → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin 3) where
  toFun v := WithLp.toLp 2 ![v 0, v 1, 0]
  map_add' v w := by
    ext i
    fin_cases i <;> simp
  map_smul' z v := by
    ext i
    fin_cases i <;> simp

def positivePlane : Submodule ℂ (EuclideanSpace ℂ (Fin 3)) := LinearMap.range positiveEmbedding

theorem positiveEmbedding_injective : Function.Injective positiveEmbedding := by
  intro v w h
  funext i
  fin_cases i
  · exact congrArg (fun x : EuclideanSpace ℂ (Fin 3) => x 0) h
  · exact congrArg (fun x : EuclideanSpace ℂ (Fin 3) => x 1) h

theorem positivePlane_finrank : Module.finrank ℂ positivePlane = 2 := by
  unfold positivePlane
  rw [LinearMap.finrank_range_of_inj positiveEmbedding_injective]
  simp

theorem positiveEmbedding_norm_sq (v : Fin 2 → ℂ) :
    ‖positiveEmbedding v‖^2 = Complex.normSq (v 0) + Complex.normSq (v 1) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [positiveEmbedding, Fin.sum_univ_three, Complex.sq_norm]

theorem referenceDual_positive_form (v : Fin 2 → ℂ) :
    (inner ℂ (positiveEmbedding v)
      (PSDNormal.euclideanOperator referenceDual (positiveEmbedding v))).re =
        Swap.gap * Complex.normSq (v 0) + (Swap.gap/2) * Complex.normSq (v 1) := by
  change ((referenceDual *ᵥ ![v 0, v 1, 0]) ⬝ᵥ star ![v 0, v 1, 0]).re = _
  simp [referenceDual, Swap.matrixQa, Swap.matrixQb, Swap.referenceMatrix,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    Complex.mul_re, Complex.mul_im, Complex.normSq_apply, Swap.gap]
  ring

/-- 显式参考矩阵在固定二维子空间上的真实二次型间隙。 -/
theorem referenceDual_quadratic_gap : ∀ v ∈ positivePlane,
    (Swap.gap/2) * ‖v‖^2 ≤ (inner ℂ v (PSDNormal.euclideanOperator referenceDual v)).re := by
  rintro v ⟨w, rfl⟩
  rw [positiveEmbedding_norm_sq, referenceDual_positive_form]
  have h := mul_nonneg Swap.gap_pos.le (Complex.normSq_nonneg (w 0))
  nlinarith

theorem continuous_euclideanOperator :
    Continuous (PSDNormal.euclideanOperator : KMatrix →
      (EuclideanSpace ℂ (Fin 3) →L[ℂ] EuclideanSpace ℂ (Fin 3))) :=
  (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional

theorem continuousAt_dualDistance : ContinuousAt
    (fun q : NormalizedParameters => ‖PSDNormal.euclideanOperator (dualNormal q - referenceDual)‖)
    referenceNormalized :=
  (continuous_euclideanOperator.continuousAt.comp
    (continuousAt_dualNormal.sub continuousAt_const)).norm

/-- 邻域由实际导数、实际对偶范数与指定乘子精度直接定义。 -/
def rankOneNeighborhood (ε : ℝ) : Set NormalizedParameters :=
  interior {q | referenceRadial / 2 < radialB q ∧
    ‖PSDNormal.euclideanOperator (dualNormal q - referenceDual)‖ < Swap.gap/2 ∧
    |multiplier q - Swap.slope| < ε}

theorem rankOneNeighborhood_isOpen (ε : ℝ) : IsOpen (rankOneNeighborhood ε) := isOpen_interior

/-- 该固定开集确实包含实际首交换归一化参考点。 -/
theorem reference_mem_rankOneNeighborhood {ε : ℝ} (hε : 0 < ε) :
    referenceNormalized ∈ rankOneNeighborhood ε := by
  apply mem_interior_iff_mem_nhds.mpr
  have hb : ∀ᶠ q in 𝓝 referenceNormalized, referenceRadial/2 < radialB q :=
    continuousAt_const.eventually_lt continuous_radialB.continuousAt
      (by rw [radialB_reference]; linarith [referenceRadial_pos])
  have hs : ∀ᶠ q in 𝓝 referenceNormalized,
      ‖PSDNormal.euclideanOperator (dualNormal q - referenceDual)‖ < Swap.gap/2 :=
    continuousAt_dualDistance.eventually_lt continuousAt_const
      (by simp only [dualNormal_reference, sub_self, map_zero, norm_zero]; linarith [Swap.gap_pos])
  have hm : ∀ᶠ q in 𝓝 referenceNormalized, |multiplier q - Swap.slope| < ε :=
    (continuousAt_multiplier.sub continuousAt_const).abs.eventually_lt continuousAt_const
      (by
        change |multiplier referenceNormalized - Swap.slope| < ε
        rw [multiplier_reference, sub_self, abs_zero]
        exact hε)
  exact hb.and (hs.and hm)

theorem rankOneNeighborhood_conditions {ε : ℝ} {q : NormalizedParameters}
    (hq : q ∈ rankOneNeighborhood ε) :
    referenceRadial/2 < radialB q ∧
    ‖PSDNormal.euclideanOperator (dualNormal q - referenceDual)‖ < Swap.gap/2 ∧
    |multiplier q - Swap.slope| < ε := by
  have hs : rankOneNeighborhood ε ⊆ {q : NormalizedParameters |
      referenceRadial/2 < radialB q ∧
      ‖PSDNormal.euclideanOperator (dualNormal q - referenceDual)‖ < Swap.gap/2 ∧
      |multiplier q - Swap.slope| < ε} := interior_subset
  exact hs hq

theorem actual_multiplier_of_scale (q : NormalizedParameters) {d : ℝ} (hd : d ≠ 0)
    (hscale : q.1.2 = d • q.2) :
    kDerivative (1/2) (1/2) q.1 q.1.2 /
      kDerivative (1/2) (-1/2) q.1 q.1.2 = multiplier q := by
  unfold multiplier radialA radialB
  rw [hscale, map_smul, map_smul]
  change d * _ / (d * _) = _
  exact mul_div_mul_left _ _ hd

theorem radial_lower_bound_of_mem_neighborhood {ε : ℝ} (q : NormalizedParameters)
    (hq : q ∈ rankOneNeighborhood ε) {d : ℝ} (hd : 0 < d)
    (hscale : q.1.2 = d • q.2) :
    d * (referenceRadial/2) < kDerivative (1/2) (-1/2) q.1 q.1.2 := by
  rw [hscale, map_smul]
  exact mul_lt_mul_of_pos_left (rankOneNeighborhood_conditions hq).1 hd

/-- 实际固定 b 的局部极小，在该固定邻域中径向严格正、对偶 PSD 且 K 精确秩一。 -/
theorem rank_one_of_mem_neighborhood {ε : ℝ} (q : NormalizedParameters)
    (hq : q ∈ rankOneNeighborhood ε) {d : ℝ} (hd : 0 < d)
    (hscale : q.1.2 = d • q.2) (hK : q.1.2.PosSemidef)
    (hmin : IsLocalMinOn (fun W => (canonicalOutput q.1.1 W 1).1)
      {W | W.PosSemidef ∧ (canonicalOutput q.1.1 W 1).2 =
        (canonicalOutput q.1.1 q.1.2 1).2} q.1.2) :
    0 < kDerivative (1/2) (-1/2) q.1 q.1.2 ∧
    (dualNormal q).PosSemidef ∧
    (dualNormal q * q.1.2).trace.re = 0 ∧
    dualNormal q * q.1.2 = 0 ∧ q.1.2.rank = 1 ∧
    |multiplier q - Swap.slope| < ε := by
  obtain ⟨hb, hs, hm⟩ := rankOneNeighborhood_conditions hq
  have hbW : 0 < radialB q := by linarith [referenceRadial_pos]
  have hbK : 0 < kDerivative (1/2) (-1/2) q.1 q.1.2 := by
    rw [hscale, map_smul]
    exact mul_pos hd hbW
  have hK0 : q.1.2 ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hbK
    exact (lt_irrefl 0) hbK
  have hmu := actual_multiplier_of_scale q hd.ne' hscale
  have hn := canonical_psd_normal_of_localMin q.1.1 q.1.2 hK hbK.ne' hmin
  dsimp only at hn
  rw [hmu] at hn
  change (dualNormal q).PosSemidef ∧ (dualNormal q * q.1.2).trace.re = 0 ∧
    dualNormal q * q.1.2 = 0 at hn
  have hr : q.1.2.rank = 1 :=
    PSDNormal.rank_one_of_psd_trace_and_quadratic_gap positivePlane
      (by rw [positivePlane_finrank]) referenceDual_quadratic_gap hs hn.1 hK hK0 hn.2.1
  exact ⟨hbK, hn.1, hn.2.1, hn.2.2, hr, hm⟩

/-- 形式化 B7 的定性固定邻域版本；邻域不依赖单个极小值或耗散尺度 d。 -/
theorem exists_actual_rank_one_neighborhood (ε : ℝ) (hε : 0 < ε) :
    ∃ V : Set NormalizedParameters, IsOpen V ∧ referenceNormalized ∈ V ∧
      ∀ q ∈ V, ∀ d : ℝ, 0 < d → q.1.2 = d • q.2 → q.1.2.PosSemidef →
        IsLocalMinOn (fun W => (canonicalOutput q.1.1 W 1).1)
          {W | W.PosSemidef ∧ (canonicalOutput q.1.1 W 1).2 =
            (canonicalOutput q.1.1 q.1.2 1).2} q.1.2 →
        0 < kDerivative (1/2) (-1/2) q.1 q.1.2 ∧
        (dualNormal q).PosSemidef ∧ dualNormal q * q.1.2 = 0 ∧
        q.1.2.rank = 1 ∧ |multiplier q - Swap.slope| < ε := by
  refine ⟨rankOneNeighborhood ε, rankOneNeighborhood_isOpen ε,
    reference_mem_rankOneNeighborhood hε, ?_⟩
  intro q hq d hd hscale hK hmin
  obtain ⟨hb, hS, _, hSK, hr, hm⟩ := rank_one_of_mem_neighborhood q hq hd hscale hK hmin
  exact ⟨hb, hS, hSK, hr, hm⟩

/-- 归一化生成元的真实收敛自动把全部最终极小值送入同一秩一邻域。 -/
theorem eventually_rank_one_of_tendsto {ι : Type*} {F : Filter ι}
    (q : ι → NormalizedParameters) (d : ι → ℝ)
    (hconv : Tendsto q F (𝓝 referenceNormalized))
    (hmin : ∀ᶠ i in F, 0 < d i ∧ (q i).1.2 = d i • (q i).2 ∧
      (q i).1.2.PosSemidef ∧
      IsLocalMinOn (fun W => (canonicalOutput (q i).1.1 W 1).1)
        {W | W.PosSemidef ∧ (canonicalOutput (q i).1.1 W 1).2 =
          (canonicalOutput (q i).1.1 (q i).1.2 1).2} (q i).1.2) :
    ∀ᶠ i in F, 0 < kDerivative (1/2) (-1/2) (q i).1 (q i).1.2 ∧
      (dualNormal (q i)).PosSemidef ∧ dualNormal (q i) * (q i).1.2 = 0 ∧
      (q i).1.2.rank = 1 := by
  have hV := hconv.eventually ((rankOneNeighborhood_isOpen 1).mem_nhds
    (reference_mem_rankOneNeighborhood (by norm_num : (0 : ℝ) < 1)))
  filter_upwards [hV, hmin] with i hi hmi
  obtain ⟨hd, hscale, hK, hm⟩ := hmi
  obtain ⟨hb, hS, _, hSK, hr, _⟩ := rank_one_of_mem_neighborhood (q i) hi hd hscale hK hm
  exact ⟨hb, hS, hSK, hr⟩

theorem multiplier_tendsto_slope {ι : Type*} {F : Filter ι}
    (q : ι → NormalizedParameters) (hconv : Tendsto q F (𝓝 referenceNormalized)) :
    Tendsto (fun i => multiplier (q i)) F (𝓝 Swap.slope) := by
  simpa only [multiplier_reference, Function.comp_def] using continuousAt_multiplier.tendsto.comp hconv

#print axioms reference_kGradient_a
#print axioms reference_kGradient_b
#print axioms continuousAt_dualNormal
#print axioms reference_radial_b
#print axioms referenceDual_quadratic_gap
#print axioms reference_mem_rankOneNeighborhood
#print axioms exists_actual_rank_one_neighborhood
#print axioms eventually_rank_one_of_tendsto
#print axioms multiplier_tendsto_slope
end TwoStateQuantumEmbedding.SwapRankOne
