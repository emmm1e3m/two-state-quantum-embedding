import TwoStateQuantumEmbedding.AffineExponential
import TwoStateQuantumEmbedding.CanonicalBloch

noncomputable section
open Matrix NormedSpace
open scoped Matrix.Norms.Operator ComplexOrder

namespace TwoStateQuantumEmbedding.CanonicalBias
open GKSLAlgebra CanonicalBloch
open AffineExponential hiding M3 V3
open TwoState.GeneralGeometry

set_option maxRecDepth 3000
set_option maxHeartbeats 1500000

/-- 增广定义与通用仿射指数的接口。 -/
theorem augmentedGenerator_eq_affine (h : BlochVec) (K : C3) :
    augmentedGenerator h K = affineGenerator (blochMatrix h K) (drift K) := rfl

theorem canonicalEvolution_spatial (h : BlochVec) (K : C3) (t : ℝ) (i j : Fin 3) :
    canonicalEvolution h K t i.succ j.succ = (exp (t • blochMatrix h K)) i j :=
  affine_evolution_spatial _ _ _ _ _

theorem canonicalEvolution_drift (h : BlochVec) (K : C3) (t : ℝ) (i : Fin 3) :
    canonicalEvolution h K t i.succ 0 =
      (integratedPropagator (blochMatrix h K) t *ᵥ drift K) i :=
  affine_drift_eq_integrated_mulVec _ _ _ _

theorem canonicalOutput_sum_eq (h : BlochVec) (K : C3) (t : ℝ) :
    (canonicalOutput h K t).1 + (canonicalOutput h K t).2 =
      1 + (exp (t • blochMatrix h K)) 2 2 := by
  have he := canonicalEvolution_spatial h K t 2 2
  dsimp [canonicalOutput]
  change canonicalEvolution h K t 3 3 = _ at he
  rw [he]
  ring

theorem canonicalOutput_bias_eq (h : BlochVec) (K : C3) :
    (canonicalOutput h K 1).1 - (canonicalOutput h K 1).2 =
      biasFunctional (blochMatrix h K) ⬝ᵥ drift K := by
  have he : canonicalEvolution h K 1 3 0 =
      biasFunctional (blochMatrix h K) ⬝ᵥ drift K := by
    simpa [canonicalEvolution, augmentedGenerator_eq_affine] using
      affine_terminal_bias (blochMatrix h K) (drift K)
  dsimp [canonicalOutput]
  rw [he]
  ring

/-- 积分矩阵的转置作用在观测轴上，等于实际偏置泛函。 -/
theorem biasFunctional_eq_transpose (M : M3) :
    biasFunctional M = (integratedPropagator M 1).transpose *ᵥ ![0, 0, 1] := by
  funext i
  simp [biasFunctional, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- 固定实部和 Hamiltonian 时的三维线性生成元。 -/
def fixedMatrix (h : BlochVec) (S : M3) : M3 :=
  crossMatrix h + (2 : ℝ) • (S - Matrix.trace S • (1 : M3))

theorem physicalCanonical_real (S : M3) (c : V3) :
    (physicalCanonical S c).map Complex.re = S := by
  rw [physicalCanonical_eq]
  ext i j
  simp [complexify, Matrix.map_apply, Matrix.smul_apply, Complex.mul_re]

theorem physicalCanonical_drift (S : M3) (c : V3) :
    drift (physicalCanonical S c) = c := by
  rw [physicalCanonical_eq]
  funext i
  fin_cases i <;>
    simp [drift, complexify, crossMat, Matrix.smul_apply, Complex.mul_im]

theorem blochMatrix_physical (h : BlochVec) (S : M3) (c : V3) :
    blochMatrix h (physicalCanonical S c) = fixedMatrix h S := by
  simp [blochMatrix, physicalCanonical_real, fixedMatrix]

def fixedX (h : BlochVec) (S : M3) : ℝ := (exp (fixedMatrix h S)) 2 2

def fixedZ (h : BlochVec) (S : M3) : ℝ :=
  4 * Real.sqrt (biasFunctional (fixedMatrix h S) ⬝ᵥ
    (S.adjugate *ᵥ biasFunctional (fixedMatrix h S)))

def outputFromXZ (x z : ℝ) : ℝ × ℝ := ((1+x+z)/2, (1+x-z)/2)

theorem canonicalOutput_physical (h : BlochVec) (S : M3) (c : V3) :
    canonicalOutput h (physicalCanonical S c) 1 =
      outputFromXZ (fixedX h S) (biasFunctional (fixedMatrix h S) ⬝ᵥ c) := by
  have hx := canonicalOutput_sum_eq h (physicalCanonical S c) 1
  have hz := canonicalOutput_bias_eq h (physicalCanonical S c)
  simp only [one_smul, blochMatrix_physical, physicalCanonical_drift] at hx hz
  apply Prod.ext <;> dsimp [outputFromXZ, fixedX] <;> linarith

/-- 包含退化实部的完整偏置区间，直接读取真实增广矩阵指数。 -/
theorem fixed_bias_interval (h : BlochVec) (S : M3) (hS : S.PosSemidef) (z : ℝ) :
    (∃ c : V3, (physicalCanonical S c).PosSemidef ∧
      canonicalOutput h (physicalCanonical S c) 1 = outputFromXZ (fixedX h S) z) ↔
    |z| ≤ fixedZ h S := by
  unfold fixedZ
  rw [← physicalCanonical_linear_image S hS (biasFunctional (fixedMatrix h S)) z]
  constructor
  · rintro ⟨c, hc, he⟩
    refine ⟨c, hc, ?_⟩
    rw [canonicalOutput_physical] at he
    have hp := congrArg Prod.fst he
    dsimp [outputFromXZ] at hp
    linarith
  · rintro ⟨c, hc, hz⟩
    exact ⟨c, hc, by rw [canonicalOutput_physical, ← hz]⟩

/-- 每个 Hermitian canonical 矩阵都属于上述实部与漂移参数化。 -/
theorem hermitian_eq_physical (K : C3) (hK : K.IsHermitian) :
    K = physicalCanonical (K.map Complex.re) (drift K) := by
  rw [physicalCanonical_eq]
  exact hermitian_drift_reconstruction K hK

theorem posSemidef_real_part (K : C3) (hK : K.PosSemidef) :
    (K.map Complex.re).PosSemidef := by
  obtain ⟨l, hl⟩ := exists_kossakowski_factor K hK
  rw [← hl]
  exact kossakowski_real_posSemidef l

/-- 固定真实实部的全部 canonical 输出，量词遍历全部 PSD 系数矩阵。 -/
theorem fixed_real_output_interval (h : BlochVec) (S : M3) (hS : S.PosSemidef)
    (z : ℝ) :
    (∃ K : C3, K.PosSemidef ∧ K.map Complex.re = S ∧
      canonicalOutput h K 1 = outputFromXZ (fixedX h S) z) ↔ |z| ≤ fixedZ h S := by
  rw [← fixed_bias_interval h S hS z]
  constructor
  · rintro ⟨K, hK, hreal, hout⟩
    have he : K = physicalCanonical S (drift K) := by
      simpa [hreal] using hermitian_eq_physical K hK.isHermitian
    exact ⟨drift K, he ▸ hK, by rw [← he]; exact hout⟩
  · rintro ⟨c, hc, hout⟩
    exact ⟨physicalCanonical S c, hc, physicalCanonical_real S c, hout⟩

theorem fixed_interval_mem_Q2 (h : BlochVec) (S : M3) (hS : S.PosSemidef)
    (z : ℝ) (hz : |z| ≤ fixedZ h S) : outputFromXZ (fixedX h S) z ∈ Q2 := by
  obtain ⟨c, hc, he⟩ := (fixed_bias_interval h S hS z).mpr hz
  rw [← he]
  exact canonicalOutput_mem_Q2 h _ hc 1 (by norm_num)

theorem fixed_max_attained (h : BlochVec) (S : M3) (hS : S.PosSemidef) :
    ∃ K : C3, K.PosSemidef ∧ K.map Complex.re = S ∧
      canonicalOutput h K 1 = outputFromXZ (fixedX h S) (fixedZ h S) := by
  apply (fixed_real_output_interval h S hS _).mpr
  exact (abs_of_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).le

/-- 区间的每一点已有原始有限跳跃 GKSL 实现，不只属于闭包。 -/
theorem fixed_interval_finite_attained (h : BlochVec) (S : M3) (hS : S.PosSemidef)
    (z : ℝ) (hz : |z| ≤ fixedZ h S) :
    ∃ A : Fin 3 → QubitMatrix,
      finiteOutput (hamiltonian h) A 1 = outputFromXZ (fixedX h S) z := by
  obtain ⟨K, hK, _, hout⟩ := (fixed_real_output_interval h S hS z).mpr hz
  obtain ⟨A, hA⟩ := exists_finiteOutput_for_canonical h K hK
  exact ⟨A, (hA 1).trans hout⟩

def fixedOutputs : Set (ℝ × ℝ) :=
  {p | ∃ (h : BlochVec) (S : M3), S.PosSemidef ∧
    ∃ z : ℝ, |z| ≤ fixedZ h S ∧ outputFromXZ (fixedX h S) z = p}

/-- 余子式支撑区间与全部 canonical 有限时输出完全相等。 -/
theorem canonicalOutputs_eq_fixedOutputs : canonicalOutputs = fixedOutputs := by
  ext p
  constructor
  · rintro ⟨h, K, hK, rfl⟩
    let S := K.map Complex.re
    let c := drift K
    have he : K = physicalCanonical S c := hermitian_eq_physical K hK.isHermitian
    have hS : S.PosSemidef := posSemidef_real_part K hK
    have hc : (physicalCanonical S c).PosSemidef := he ▸ hK
    refine ⟨h, S, hS, biasFunctional (fixedMatrix h S) ⬝ᵥ c, ?_, ?_⟩
    · exact (fixed_bias_interval h S hS _).mp
        ⟨c, hc, canonicalOutput_physical h S c⟩
    · rw [he, canonicalOutput_physical]
  · rintro ⟨h, S, hS, z, hz, rfl⟩
    obtain ⟨c, hc, he⟩ := (fixed_bias_interval h S hS z).mpr hz
    exact ⟨h, physicalCanonical S c, hc, he⟩

theorem Q2_eq_closure_fixedOutputs : Q2 = closure fixedOutputs := by
  rw [Q2_eq_closure_canonicalOutputs, canonicalOutputs_eq_fixedOutputs]

/-- 在共轭配对间作凸组合；实部保持，漂移按 η 缩放。 -/
def driftScale (K : C3) (η : ℝ) : C3 :=
  ((1+η)/2 : ℝ) • K + ((1-η)/2 : ℝ) • K.transpose

theorem driftScale_posSemidef (K : C3) (hK : K.PosSemidef) (η : ℝ)
    (hηlo : -1 ≤ η) (hηhi : η ≤ 1) : (driftScale K η).PosSemidef :=
  TwoState.Geometry.posSemidef_transpose_mix K hK η hηlo hηhi

theorem driftScale_real (K : C3) (hK : K.IsHermitian) (η : ℝ) :
    (driftScale K η).map Complex.re = K.map Complex.re := by
  ext i j
  exact (TwoState.Geometry.transpose_mix_coordinates K hK η i j).1

theorem driftScale_drift (K : C3) (hK : K.IsHermitian) (η : ℝ) :
    drift (driftScale K η) = η • drift K := by
  have hi (i j : Fin 3) : (driftScale K η i j).im = η * (K i j).im :=
    (TwoState.Geometry.transpose_mix_coordinates K hK η i j).2
  funext i
  fin_cases i <;> simp [drift, hi, Pi.smul_apply, smul_eq_mul] <;> ring

theorem driftScale_blochMatrix (h : BlochVec) (K : C3) (hK : K.IsHermitian) (η : ℝ) :
    blochMatrix h (driftScale K η) = blochMatrix h K := by
  simp [blochMatrix, driftScale_real K hK η]

def antidiagonalMix (η : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (((1+η)/2)*p.1 + ((1-η)/2)*p.2,
   ((1-η)/2)*p.1 + ((1+η)/2)*p.2)

theorem antidiagonalMix_continuous (η : ℝ) : Continuous (antidiagonalMix η) := by
  unfold antidiagonalMix
  fun_prop

theorem canonicalOutput_driftScale (h : BlochVec) (K : C3) (hK : K.IsHermitian)
    (η : ℝ) : canonicalOutput h (driftScale K η) 1 =
      antidiagonalMix η (canonicalOutput h K 1) := by
  have hx := canonicalOutput_sum_eq h K 1
  have hx' := canonicalOutput_sum_eq h (driftScale K η) 1
  have hz := canonicalOutput_bias_eq h K
  have hz' := canonicalOutput_bias_eq h (driftScale K η)
  rw [driftScale_blochMatrix h K hK η] at hx' hz'
  rw [driftScale_drift K hK η, dotProduct_smul] at hz'
  simp only [smul_eq_mul] at hz'
  rw [← hz] at hz'
  apply Prod.ext <;> dsimp [antidiagonalMix] <;> nlinarith

theorem canonicalOutputs_antidiagonalMix (η : ℝ) (hηlo : -1 ≤ η) (hηhi : η ≤ 1)
    {p : ℝ × ℝ} (hp : p ∈ canonicalOutputs) :
    antidiagonalMix η p ∈ canonicalOutputs := by
  obtain ⟨h, K, hK, rfl⟩ := hp
  exact ⟨h, driftScale K η, driftScale_posSemidef K hK η hηlo hηhi,
    canonicalOutput_driftScale h K hK.isHermitian η⟩

/-- 真实 Q2 的闭包也保留沿反对角线的完整填充。 -/
theorem Q2_antidiagonal_filling (η : ℝ) (hηlo : -1 ≤ η) (hηhi : η ≤ 1)
    {p : ℝ × ℝ} (hp : p ∈ Q2) : antidiagonalMix η p ∈ Q2 := by
  have hclosed : IsClosed ((antidiagonalMix η) ⁻¹' Q2) :=
    Q2_isClosed.preimage (antidiagonalMix_continuous η)
  have hsub : canonicalOutputs ⊆ (antidiagonalMix η) ⁻¹' Q2 := by
    intro q hq
    change antidiagonalMix η q ∈ Q2
    rw [Q2_eq_closure_canonicalOutputs]
    exact subset_closure (canonicalOutputs_antidiagonalMix η hηlo hηhi hq)
  rw [Q2_eq_closure_canonicalOutputs] at hp
  exact closure_minimal hsub hclosed hp

theorem Q2_swap {p : ℝ × ℝ} (hp : p ∈ Q2) : (p.2, p.1) ∈ Q2 := by
  simpa [antidiagonalMix] using Q2_antidiagonal_filling (-1) (by norm_num) (by norm_num) hp

theorem Q2_swap_iff (p : ℝ × ℝ) : (p.2, p.1) ∈ Q2 ↔ p ∈ Q2 :=
  ⟨fun hp => Q2_swap hp, Q2_swap⟩

#print axioms canonicalOutput_sum_eq
#print axioms canonicalEvolution_drift
#print axioms fixed_bias_interval
#print axioms fixed_real_output_interval
#print axioms fixed_interval_mem_Q2
#print axioms fixed_max_attained
#print axioms fixed_interval_finite_attained
#print axioms Q2_eq_closure_fixedOutputs
#print axioms Q2_antidiagonal_filling
#print axioms Q2_swap_iff

end TwoStateQuantumEmbedding.CanonicalBias


