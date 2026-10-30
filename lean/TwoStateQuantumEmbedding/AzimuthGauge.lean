import TwoStateQuantumEmbedding.CanonicalBloch
import TwoStateQuantumEmbedding.GeneralGeometry

/-! 同一测量轴下的 Hamiltonian 方位规范，保留真实增广矩阵指数。 -/
noncomputable section
open Matrix Complex
open scoped Matrix.Norms.Operator ComplexOrder

namespace TwoStateQuantumEmbedding.AzimuthGauge
open GKSLAlgebra CanonicalBloch TwoState.GeneralGeometry

set_option maxRecDepth 3000
set_option maxHeartbeats 1600000

def rotateNoise (R : M3) (K : C3) : C3 :=
  complexify R * K * (complexify R).conjTranspose

theorem rotateNoise_posSemidef (R : M3) (K : C3) (hK : K.PosSemidef) :
    (rotateNoise R K).PosSemidef := hK.mul_mul_conjTranspose_same (complexify R)

theorem rotateNoise_trace (R : M3) (hR : Orthogonal R) (K : C3) :
    (rotateNoise R K).trace = K.trace := by
  unfold rotateNoise
  rw [Matrix.trace_mul_cycle, ← complexify_transpose, ← complexify_mul, hR.1,
    complexify_one, Matrix.one_mul]

theorem rotateNoise_re (R : M3) (K : C3) :
    (rotateNoise R K).map Complex.re = R * K.map Complex.re * Rᵀ := by
  ext i j
  simp [rotateNoise, complexify, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_three, Complex.mul_re]

theorem real_trace_congruence (R S : M3) (hR : Orthogonal R) :
    (R * S * Rᵀ).trace = S.trace := by
  rw [Matrix.trace_mul_cycle, hR.1, Matrix.one_mul]

theorem physicalCanonical_reconstruct (K : C3) (hK : K.IsHermitian) :
    physicalCanonical (K.map Complex.re) (drift K) = K := by
  rw [physicalCanonical_eq]
  exact (hermitian_drift_reconstruction K hK).symm

theorem drift_physicalCanonical (S : M3) (c : V3) :
    drift (physicalCanonical S c) = c := by
  rw [physicalCanonical_eq]
  ext i
  fin_cases i <;>
    simp [drift, complexify, crossMat, Complex.mul_im]

theorem rotateNoise_drift (R : M3) (hR : Orthogonal R) (hdet : R.det = 1)
    (K : C3) (hK : K.IsHermitian) :
    drift (rotateNoise R K) = R *ᵥ drift K := by
  have hcan : rotateNoise R K =
      physicalCanonical (R * K.map Complex.re * Rᵀ) (R *ᵥ drift K) := by
    calc
      rotateNoise R K = rotateNoise R (physicalCanonical (K.map Complex.re) (drift K)) := by
        rw [physicalCanonical_reconstruct K hK]
      _ = physicalCanonical (R * K.map Complex.re * Rᵀ) (R *ᵥ drift K) := by
        unfold rotateNoise physicalCanonical
        rw [canonical_congruence R _ hR, hdet, one_smul, Matrix.mulVec_smul]
  rw [hcan, drift_physicalCanonical]

theorem rotate_blochMatrix (R : M3) (hR : Orthogonal R) (hdet : R.det = 1)
    (h : BlochVec) (K : C3) :
    blochMatrix (R *ᵥ h) (rotateNoise R K) = R * blochMatrix h K * Rᵀ := by
  have hc : crossMatrix (R *ᵥ h) = R * crossMatrix h * Rᵀ := by
    simpa only [crossMatrix, crossMat, hdet, one_smul] using
      (orthogonal_crossMat R hR h).symm
  unfold blochMatrix
  rw [rotateNoise_re, real_trace_congruence R _ hR, hc]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hR.2]

/-- 保持 z 测量轴的显式取向保持旋转。 -/
def azimuthRotation (c s : ℝ) : M3 := !![c, s, 0; -s, c, 0; 0, 0, 1]

def augmentedAzimuth (c s : ℝ) : AugmentedMatrix :=
  !![1, 0, 0, 0; 0, c, s, 0; 0, -s, c, 0; 0, 0, 0, 1]

theorem azimuthRotation_orthogonal (c s : ℝ) (hcs : c^2 + s^2 = 1) :
    Orthogonal (azimuthRotation c s) := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [azimuthRotation, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.transpose_apply] <;> nlinarith

theorem azimuthRotation_det (c s : ℝ) (hcs : c^2 + s^2 = 1) :
    (azimuthRotation c s).det = 1 := by
  simp [azimuthRotation, Matrix.det_fin_three]
  nlinarith

theorem azimuthRotation_fixes_ez (c s : ℝ) :
    azimuthRotation c s *ᵥ ![0, 0, 1] = ![0, 0, 1] := by
  ext i
  fin_cases i <;> simp [azimuthRotation, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem augmentedAzimuth_orthogonal (c s : ℝ) (hcs : c^2 + s^2 = 1) :
    (augmentedAzimuth c s)ᵀ * augmentedAzimuth c s = 1 ∧
      augmentedAzimuth c s * (augmentedAzimuth c s)ᵀ = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [augmentedAzimuth, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.transpose_apply] <;> nlinarith

/-- 同一保测量轴旋转作用于完整漂移与线性动力学。 -/
theorem augmentedGenerator_azimuth (c s : ℝ) (hcs : c^2 + s^2 = 1)
    (h : BlochVec) (K : C3) (hK : K.IsHermitian) :
    augmentedGenerator (azimuthRotation c s *ᵥ h) (rotateNoise (azimuthRotation c s) K) =
      augmentedAzimuth c s * augmentedGenerator h K * (augmentedAzimuth c s)ᵀ := by
  have hR := azimuthRotation_orthogonal c s hcs
  have hd := azimuthRotation_det c s hcs
  unfold augmentedGenerator
  rw [rotate_blochMatrix _ hR hd, rotateNoise_drift _ hR hd K hK]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [augmentedAzimuth, azimuthRotation, Matrix.mul_apply, Matrix.mulVec,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Matrix.transpose_apply]

/-- 指数的相似协变对所有实时间成立，未以输出不变作假设。 -/
theorem canonicalEvolution_azimuth (c s : ℝ) (hcs : c^2 + s^2 = 1)
    (h : BlochVec) (K : C3) (hK : K.IsHermitian) (t : ℝ) :
    canonicalEvolution (azimuthRotation c s *ᵥ h)
        (rotateNoise (azimuthRotation c s) K) t =
      augmentedAzimuth c s * canonicalEvolution h K t * (augmentedAzimuth c s)ᵀ := by
  have hU := augmentedAzimuth_orthogonal c s hcs
  let U : AugmentedMatrixˣ :=
    ⟨augmentedAzimuth c s, (augmentedAzimuth c s)ᵀ, hU.2, hU.1⟩
  have he := Matrix.exp_units_conj U (t • augmentedGenerator h K)
  change NormedSpace.exp (augmentedAzimuth c s * (t • augmentedGenerator h K) *
      (augmentedAzimuth c s)ᵀ) = augmentedAzimuth c s *
      NormedSpace.exp (t • augmentedGenerator h K) * (augmentedAzimuth c s)ᵀ at he
  unfold canonicalEvolution
  rw [augmentedGenerator_azimuth c s hcs h K hK]
  simpa only [Matrix.mul_smul, Matrix.smul_mul] using he

/-- z 轴制备及 z 轴读出均保持，两个原始概率在所有时刻完全相同。 -/
theorem canonicalOutput_azimuth (c s : ℝ) (hcs : c^2 + s^2 = 1)
    (h : BlochVec) (K : C3) (hK : K.IsHermitian) (t : ℝ) :
    canonicalOutput (azimuthRotation c s *ᵥ h)
        (rotateNoise (azimuthRotation c s) K) t = canonicalOutput h K t := by
  unfold canonicalOutput
  rw [canonicalEvolution_azimuth c s hcs h K hK t]
  simp [augmentedAzimuth, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Fin.sum_univ_succ, Matrix.transpose_apply]

def transverseRadius (h : BlochVec) : ℝ := Real.sqrt (h 0 ^ 2 + h 1 ^ 2)

def azimuthCos (h : BlochVec) : ℝ :=
  if transverseRadius h = 0 then 1 else h 0 / transverseRadius h

def azimuthSin (h : BlochVec) : ℝ :=
  if transverseRadius h = 0 then 0 else h 1 / transverseRadius h

def gaugeRotation (h : BlochVec) : M3 := azimuthRotation (azimuthCos h) (azimuthSin h)

theorem transverseRadius_nonneg (h : BlochVec) : 0 ≤ transverseRadius h :=
  Real.sqrt_nonneg _

theorem transverseRadius_sq (h : BlochVec) :
    transverseRadius h ^ 2 = h 0 ^ 2 + h 1 ^ 2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem transverseRadius_eq_zero (h : BlochVec) (hr : transverseRadius h = 0) :
    h 0 = 0 ∧ h 1 = 0 := by
  have hs := transverseRadius_sq h
  rw [hr] at hs
  constructor <;> nlinarith [sq_nonneg (h 0), sq_nonneg (h 1)]

theorem azimuthCosSin_unit (h : BlochVec) : azimuthCos h ^ 2 + azimuthSin h ^ 2 = 1 := by
  by_cases hr : transverseRadius h = 0
  · simp [azimuthCos, azimuthSin, hr]
  · simp only [azimuthCos, azimuthSin, hr, ↓reduceIte]
    rw [div_pow, div_pow, ← add_div, ← transverseRadius_sq]
    exact div_self (pow_ne_zero _ hr)

theorem gaugeRotation_normalizes (h : BlochVec) :
    gaugeRotation h *ᵥ h = ![transverseRadius h, 0, h 2] := by
  by_cases hr : transverseRadius h = 0
  · obtain ⟨h0, h1⟩ := transverseRadius_eq_zero h hr
    ext i
    fin_cases i <;> simp [gaugeRotation, azimuthRotation, azimuthCos, azimuthSin, hr,
      h0, h1, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · ext i
    fin_cases i <;>
      simp [gaugeRotation, azimuthRotation, azimuthCos, azimuthSin, hr,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · field_simp
      nlinarith [transverseRadius_sq h]
    · ring

theorem gaugeRotation_orthogonal (h : BlochVec) : Orthogonal (gaugeRotation h) :=
  azimuthRotation_orthogonal _ _ (azimuthCosSin_unit h)

theorem gaugeRotation_det (h : BlochVec) : (gaugeRotation h).det = 1 :=
  azimuthRotation_det _ _ (azimuthCosSin_unit h)

theorem gaugeRotation_fixes_ez (h : BlochVec) :
    gaugeRotation h *ᵥ ![0, 0, 1] = ![0, 0, 1] := azimuthRotation_fixes_ez _ _

theorem canonicalOutput_normal_form (h : BlochVec) (K : C3) (hK : K.IsHermitian) (t : ℝ) :
    canonicalOutput ![transverseRadius h, 0, h 2] (rotateNoise (gaugeRotation h) K) t =
      canonicalOutput h K t := by
  rw [← gaugeRotation_normalizes h]
  exact canonicalOutput_azimuth _ _ (azimuthCosSin_unit h) h K hK t

/-- 任意合法生成元均有同一固定测量基下的非负横向 Hamiltonian 规范。 -/
theorem exists_azimuth_normal_form (h : BlochVec) (K : C3) (hK : K.PosSemidef) :
    ∃ (r : ℝ) (R : M3) (K' : C3), 0 ≤ r ∧ Orthogonal R ∧ R.det = 1 ∧
      R *ᵥ ![0, 0, 1] = ![0, 0, 1] ∧ R *ᵥ h = ![r, 0, h 2] ∧
      K' = rotateNoise R K ∧ K'.PosSemidef ∧ K'.trace = K.trace ∧
      ∀ t : ℝ, canonicalOutput ![r, 0, h 2] K' t = canonicalOutput h K t := by
  refine ⟨transverseRadius h, gaugeRotation h, rotateNoise (gaugeRotation h) K,
    transverseRadius_nonneg h, gaugeRotation_orthogonal h, gaugeRotation_det h,
    gaugeRotation_fixes_ez h, gaugeRotation_normalizes h, rfl,
    rotateNoise_posSemidef _ K hK, rotateNoise_trace _ (gaugeRotation_orthogonal h) K, ?_⟩
  exact fun t => canonicalOutput_normal_form h K hK.isHermitian t

#print axioms rotateNoise_drift
#print axioms rotate_blochMatrix
#print axioms canonicalEvolution_azimuth
#print axioms canonicalOutput_azimuth
#print axioms exists_azimuth_normal_form

end TwoStateQuantumEmbedding.AzimuthGauge
