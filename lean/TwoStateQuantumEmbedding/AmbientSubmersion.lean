import TwoStateQuantumEmbedding.DriftGradient
import TwoStateQuantumEmbedding.CanonicalGradient
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-! 实际全实环境参数与合法正定噪声的局部开放性。 -/
noncomputable section
open Matrix Complex NormedSpace Filter Set
open scoped Topology Matrix.Norms.Operator ComplexOrder

namespace TwoStateQuantumEmbedding.AmbientSubmersion
open GKSLAlgebra CanonicalBloch ExponentialGradient DriftGradient

set_option maxRecDepth 2500
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

abbrev RealMatrix := Matrix (Fin 3) (Fin 3) ℝ
abbrev KMatrix := Matrix (Fin 3) (Fin 3) ℂ
abbrev Ambient := RealMatrix × BlochVec

def inverseHamiltonian (M : RealMatrix) : BlochVec :=
  ![(M 2 1 - M 1 2)/2, (M 0 2 - M 2 0)/2, (M 1 0 - M 0 1)/2]

def inverseRealPart (M : RealMatrix) : RealMatrix :=
  (1/4:ℝ) • (M + M.transpose - Matrix.trace M • (1 : RealMatrix))

def inverseK (M : RealMatrix) (c : BlochVec) : KMatrix :=
  (inverseRealPart M).map Complex.ofReal +
    (Complex.I/4) • (crossMatrix c).map Complex.ofReal

theorem inverseK_hermitian (M : RealMatrix) (c : BlochVec) : (inverseK M c).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [inverseK, inverseRealPart, crossMatrix,
      Matrix.trace, Fin.sum_univ_three, Matrix.smul_apply, smul_eq_mul,
      Complex.mul_re, Complex.mul_im] <;> ring

theorem blochMatrix_inverse (M : RealMatrix) (c : BlochVec) :
    blochMatrix (inverseHamiltonian M) (inverseK M c) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blochMatrix, inverseHamiltonian, inverseK, inverseRealPart, crossMatrix,
      Matrix.trace, Fin.sum_univ_three, Matrix.smul_apply, smul_eq_mul,
      Complex.mul_re] <;> ring

theorem drift_inverse (M : RealMatrix) (c : BlochVec) : drift (inverseK M c) = c := by
  funext i
  fin_cases i <;>
    simp [drift, inverseK, inverseRealPart, crossMatrix, Matrix.trace,
      Fin.sum_univ_three, Matrix.smul_apply, smul_eq_mul, Complex.mul_im]

theorem inverseHamiltonian_bloch (h : BlochVec) (K : KMatrix) (hK : K.IsHermitian) :
    inverseHamiltonian (blochMatrix h K) = h := by
  have hr (i j : Fin 3) : (K i j).re = (K j i).re := by
    simpa only [Complex.star_def, Complex.conj_re] using
      (congrArg Complex.re (hK.apply i j)).symm
  funext i
  fin_cases i <;>
    simp [inverseHamiltonian, blochMatrix, crossMatrix, Matrix.smul_apply,
      smul_eq_mul] <;> linarith [hr 0 1, hr 0 2, hr 1 2]

theorem inverseRealPart_bloch (h : BlochVec) (K : KMatrix) (hK : K.IsHermitian) :
    inverseRealPart (blochMatrix h K) = K.map Complex.re := by
  have hr (i j : Fin 3) : (K i j).re = (K j i).re := by
    simpa only [Complex.star_def, Complex.conj_re] using
      (congrArg Complex.re (hK.apply i j)).symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inverseRealPart, blochMatrix, crossMatrix, Matrix.trace, Fin.sum_univ_three,
      Matrix.smul_apply, smul_eq_mul] <;> linarith [hr 0 1, hr 0 2, hr 1 2]

theorem inverseK_bloch (h : BlochVec) (K : KMatrix) (hK : K.IsHermitian) :
    inverseK (blochMatrix h K) (drift K) = K := by
  rw [inverseK, inverseRealPart_bloch h K hK]
  exact (hermitian_drift_reconstruction K hK).symm

def inverseParameters : Ambient →L[ℝ] ExponentialGradient.Parameters :=
  LinearMap.toContinuousLinearMap {
    toFun p := (inverseHamiltonian p.1, inverseK p.1 p.2)
    map_add' := by
      intro p q
      apply Prod.ext
      · funext i
        fin_cases i <;> simp [inverseHamiltonian] <;> ring
      · ext i j
        fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
          simp [inverseK, inverseRealPart, crossMatrix, Matrix.trace, Fin.sum_univ_three,
            Matrix.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im] <;> ring
    map_smul' := by
      intro r p
      apply Prod.ext
      · funext i
        fin_cases i <;> simp [inverseHamiltonian, Matrix.smul_apply, smul_eq_mul] <;> ring
      · ext i j
        fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
          simp [inverseK, inverseRealPart, crossMatrix, Matrix.trace, Fin.sum_univ_three,
            Matrix.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im] <;> ring
  }

def forwardParameters : ExponentialGradient.Parameters → Ambient :=
  fun p => (blochMatrix p.1 p.2, drift p.2)

theorem forward_inverse (p : Ambient) : forwardParameters (inverseParameters p) = p := by
  exact Prod.ext (blochMatrix_inverse p.1 p.2) (drift_inverse p.1 p.2)

theorem inverse_forward (p : ExponentialGradient.Parameters) (hp : p.2.IsHermitian) :
    inverseParameters (forwardParameters p) = p := by
  exact Prod.ext (inverseHamiltonian_bloch p.1 p.2 hp) (inverseK_bloch p.1 p.2 hp)

/-- 全部 Hermitian 规范参数构成真实实向量子空间。 -/
def canonicalHermitianSubmodule : Submodule ℝ ExponentialGradient.Parameters where
  carrier := {p | p.2.IsHermitian}
  zero_mem' := by exact Matrix.isHermitian_zero
  add_mem' := by intro p q hp hq; exact hp.add hq
  smul_mem' := by
    intro r p hp
    exact hp.smul (show IsSelfAdjoint r from IsSelfAdjoint.all _)

/-- 环境 (M,c) 与全部 h/Hermitian K 的实际实线性同构。 -/
def ambientCanonicalEquiv : Ambient ≃ₗ[ℝ] canonicalHermitianSubmodule where
  toFun p := ⟨inverseParameters p, inverseK_hermitian p.1 p.2⟩
  invFun p := forwardParameters p.val
  left_inv p := forward_inverse p
  right_inv p := Subtype.ext (inverse_forward p.val p.property)
  map_add' p q := Subtype.ext (map_add inverseParameters p q)
  map_smul' r p := Subtype.ext (map_smul inverseParameters r p)

def ambientGeneratorCLM : Ambient →L[ℝ] AugmentedMatrix :=
  canonicalGeneratorCLM.comp inverseParameters

theorem ambientGeneratorCLM_apply (p : Ambient) :
    ambientGeneratorCLM p = ambientGenerator p.1 p.2 := by
  change augmentedGenerator (inverseHamiltonian p.1) (inverseK p.1 p.2) = _
  rw [← ambientGenerator_canonical, blochMatrix_inverse, drift_inverse]

def ambientOutput (p : Ambient) : ℝ × ℝ := (ambientX p.1 p.2, ambientZ p.1 p.2)
def ambientXDerivative (p : Ambient) : Ambient →L[ℝ] ℝ :=
  ((matrixEntryCLM 2 2).comp (expDerivative p.1)).comp
    (ContinuousLinearMap.fst ℝ RealMatrix BlochVec)
def ambientFullZDerivative (p : Ambient) : Ambient →L[ℝ] ℝ :=
  (measurementCLM 0 1).comp ((expDerivative (ambientGenerator p.1 p.2)).comp ambientGeneratorCLM)
def ambientDerivative (p : Ambient) : Ambient →L[ℝ] (ℝ × ℝ) :=
  (ambientXDerivative p).prod (ambientFullZDerivative p)

theorem ambientOutput_hasStrictFDerivAt (p : Ambient) :
    HasStrictFDerivAt ambientOutput (ambientDerivative p) p := by
  have hx : HasStrictFDerivAt (fun q : Ambient => ambientX q.1 q.2) (ambientXDerivative p) p := by
    simp_rw [ambientX_eq]
    exact ((matrixEntryCLM 2 2).hasStrictFDerivAt.comp p.1
      (hasStrictFDerivAt_exp_integral p.1)).comp p hasStrictFDerivAt_fst
  have hz : HasStrictFDerivAt (fun q : Ambient => ambientZ q.1 q.2) (ambientFullZDerivative p) p := by
    have he : (fun q : Ambient => ambientZ q.1 q.2) =
        fun q => measurementCLM 0 1 (exp (ambientGeneratorCLM q)) := by
      funext q
      simp [ambientGeneratorCLM_apply, ambientZ, measurementCLM]
    rw [he]
    simpa only [ambientGeneratorCLM_apply, ambientFullZDerivative] using
      (measurementCLM 0 1).hasStrictFDerivAt.comp p
        ((hasStrictFDerivAt_exp_integral (ambientGeneratorCLM p)).comp p
          ambientGeneratorCLM.hasStrictFDerivAt)
  exact hx.prodMk hz

theorem ambientDerivative_first_direction (p : Ambient) :
    (ambientDerivative p (exp (-p.1), 0)).1 = 1 := by
  change expDerivative p.1 (exp (-p.1)) 2 2 = 1
  rw [expDerivative_exp_neg]
  simp

theorem ambientDerivative_drift_direction (p : Ambient) :
    ambientDerivative p (0, fun i => p.1 i 2) = (0, ambientX p.1 p.2 - 1) := by
  apply Prod.ext
  · change matrixEntryCLM 2 2 (expDerivative p.1 0) = 0
    simp
  · change measurementCLM 0 1
      (expDerivative (ambientGenerator p.1 p.2)
        (ambientGeneratorCLM (0, fun i => p.1 i 2))) = _
    rw [ambientGeneratorCLM_apply]
    exact ambientZDerivative_column p.1 p.2

/-- 两个实际方向构成满射；唯一非退化条件为真实 x≠1。 -/
theorem ambientDerivative_surjective (p : Ambient) (hx : ambientX p.1 p.2 ≠ 1) :
    Function.Surjective (ambientDerivative p) := by
  rintro ⟨a,b⟩
  let v : Ambient := (exp (-p.1), 0)
  let w : Ambient := (0, fun i => p.1 i 2)
  let η : ℝ := (ambientDerivative p v).2
  have hv : ambientDerivative p v = (1,η) :=
    Prod.ext (ambientDerivative_first_direction p) rfl
  have hw : ambientDerivative p w = (0,ambientX p.1 p.2-1) :=
    ambientDerivative_drift_direction p
  have hn : ambientX p.1 p.2-1 ≠ 0 := sub_ne_zero.mpr hx
  refine ⟨a • v + ((b-a*η)/(ambientX p.1 p.2-1)) • w, ?_⟩
  rw [map_add, map_smul, map_smul, hv, hw]
  apply Prod.ext <;> simp [smul_eq_mul]
  field_simp
  ring

/-- 真实严格导数的满射开放映射定理，而非假设存在局部输出逆。 -/
theorem ambientOutput_map_nhds (p : Ambient) (hx : ambientX p.1 p.2 ≠ 1) :
    Filter.map ambientOutput (𝓝 p) = 𝓝 (ambientOutput p) :=
  (ambientOutput_hasStrictFDerivAt p).map_nhds_eq_of_surj
    (LinearMap.range_eq_top.mpr (ambientDerivative_surjective p hx))

def canonicalXY (p : ExponentialGradient.Parameters) : ℝ × ℝ :=
  (canonicalScalar 1 0 p, canonicalScalar 0 1 p)
def canonicalXYDerivative (p : ExponentialGradient.Parameters) :
    ExponentialGradient.Parameters →L[ℝ] (ℝ × ℝ) :=
  (canonicalScalarDerivative 1 0 p).prod (canonicalScalarDerivative 0 1 p)

theorem canonicalXY_hasStrictFDerivAt (p : ExponentialGradient.Parameters) :
    HasStrictFDerivAt canonicalXY (canonicalXYDerivative p) p :=
  (hasStrictFDerivAt_canonicalScalar 1 0 p).prodMk (hasStrictFDerivAt_canonicalScalar 0 1 p)

theorem canonicalXY_forward (p : ExponentialGradient.Parameters) :
    canonicalXY p = ambientOutput (forwardParameters p) := by
  apply Prod.ext
  · simpa [canonicalXY, canonicalScalar, ambientOutput, forwardParameters] using
      (ambientX_canonical p.1 p.2).symm
  · simpa [canonicalXY, canonicalScalar, ambientOutput, forwardParameters] using
      (ambientZ_canonical p.1 p.2).symm

theorem canonicalXY_inverse (p : Ambient) :
    canonicalXY (inverseParameters p) = ambientOutput p := by
  rw [canonicalXY_forward, forward_inverse]

theorem canonicalXYDerivative_inverse (p : Ambient) :
    (canonicalXYDerivative (inverseParameters p)).comp inverseParameters = ambientDerivative p := by
  have hd := (canonicalXY_hasStrictFDerivAt (inverseParameters p)).comp p
    inverseParameters.hasStrictFDerivAt
  have hf : (canonicalXY ∘ inverseParameters) = ambientOutput := funext canonicalXY_inverse
  have ha := ambientOutput_hasStrictFDerivAt p
  rw [← hf] at ha
  exact hd.hasFDerivAt.unique ha.hasFDerivAt

/-- 实际 canonical 导数在 Hermitian 允许方向上满射。 -/
theorem canonicalXYDerivative_hermitian_surjective (h : BlochVec) (K : KMatrix)
    (hK : K.IsHermitian) (hx : ambientX (blochMatrix h K) (drift K) ≠ 1) :
    ∀ y : ℝ × ℝ, ∃ v : ExponentialGradient.Parameters,
      v.2.IsHermitian ∧ canonicalXYDerivative (h,K) v = y := by
  intro y
  let p : Ambient := forwardParameters (h,K)
  obtain ⟨u, hu⟩ := ambientDerivative_surjective p hx y
  refine ⟨inverseParameters u, inverseK_hermitian u.1 u.2, ?_⟩
  have he := congrArg (fun L : Ambient →L[ℝ] (ℝ × ℝ) => L u) (canonicalXYDerivative_inverse p)
  have hi : inverseParameters p = (h,K) := inverse_forward (h,K) hK
  simpa only [hi, ContinuousLinearMap.comp_apply, hu] using he

def adjointCLM : KMatrix →L[ℝ] KMatrix := LinearMap.toContinuousLinearMap {
  toFun := Matrix.conjTranspose
  map_add' := Matrix.conjTranspose_add
  map_smul' := by intro r K; simp
}

def legalParameters (K : KMatrix) (p : ExponentialGradient.Parameters) :
    ExponentialGradient.Parameters :=
  (p.1, (1+p.2) * K * (1+p.2).conjTranspose)

def legalDerivative (K : KMatrix) :
    ExponentialGradient.Parameters →L[ℝ] ExponentialGradient.Parameters :=
  LinearMap.toContinuousLinearMap {
    toFun v := (v.1, v.2*K+K*v.2.conjTranspose)
    map_add' := by
      intro v w
      simp [Matrix.add_mul, Matrix.mul_add, Matrix.conjTranspose_add]
      abel
    map_smul' := by
      intro r v
      simp [Matrix.conjTranspose_smul, smul_add]
  }

theorem legalParameters_base (h : BlochVec) (K : KMatrix) : legalParameters K (h,0) = (h,K) := by
  simp [legalParameters]

theorem legalParameters_hasStrictFDerivAt (h : BlochVec) (K : KMatrix) :
    HasStrictFDerivAt (legalParameters K) (legalDerivative K) (h,0) := by
  have hP : HasStrictFDerivAt (fun p : ExponentialGradient.Parameters => 1+p.2)
      (ContinuousLinearMap.snd ℝ BlochVec KMatrix) (h,0) :=
    hasStrictFDerivAt_snd.const_add 1
  have hd := (hP.mul_const' K).mul' (adjointCLM.hasStrictFDerivAt.comp (h,0) hP)
  convert hasStrictFDerivAt_fst.prodMk hd using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro v
    apply Prod.ext
    · rfl
    · simp [legalDerivative, adjointCLM]
      module

theorem legalParameters_psd (K : KMatrix) (hK : K.PosSemidef)
    (p : ExponentialGradient.Parameters) : (legalParameters K p).2.PosSemidef :=
  hK.mul_mul_conjTranspose_same (1+p.2)

/-- 正定 K 的同余参数微分覆盖每个 Hermitian 方向。 -/
theorem legalDerivative_surjective_hermitian (K : KMatrix) (hK : K.PosDef)
    (v : ExponentialGradient.Parameters) (hv : v.2.IsHermitian) :
    ∃ u : ExponentialGradient.Parameters, legalDerivative K u = v := by
  let W : KMatrix := (1/2:ℝ) • (v.2 * K⁻¹)
  refine ⟨(v.1,W), ?_⟩
  have hkdet : IsUnit K.det := (Matrix.isUnit_iff_isUnit_det K).mp hK.isUnit
  have hi : K⁻¹ * K = 1 := Matrix.nonsing_inv_mul K hkdet
  have ih : K * K⁻¹ = 1 := Matrix.mul_nonsing_inv K hkdet
  apply Prod.ext
  · rfl
  · change W*K+K*W.conjTranspose = v.2
    simp only [W, Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_mul,
      hv.eq, hK.inv.isHermitian.eq, Matrix.smul_mul, Matrix.mul_smul]
    rw [Matrix.mul_assoc, hi, Matrix.mul_one, ← Matrix.mul_assoc, ih, Matrix.one_mul]
    module

def legalOutput (K : KMatrix) : ExponentialGradient.Parameters → ℝ × ℝ :=
  canonicalXY ∘ legalParameters K

theorem legalOutput_hasStrictFDerivAt (h : BlochVec) (K : KMatrix) :
    HasStrictFDerivAt (legalOutput K)
      ((canonicalXYDerivative (h,K)).comp (legalDerivative K)) (h,0) := by
  have hd := (canonicalXY_hasStrictFDerivAt (legalParameters K (h,0))).comp (h,0)
    (legalParameters_hasStrictFDerivAt h K)
  simpa only [legalParameters_base, legalOutput, Function.comp_def] using hd

theorem legalOutputDerivative_surjective (h : BlochVec) (K : KMatrix) (hK : K.PosDef)
    (hx : ambientX (blochMatrix h K) (drift K) ≠ 1) :
    Function.Surjective ((canonicalXYDerivative (h,K)).comp (legalDerivative K)) := by
  intro y
  obtain ⟨v, hv, hy⟩ := canonicalXYDerivative_hermitian_surjective h K hK.isHermitian hx y
  obtain ⟨u, hu⟩ := legalDerivative_surjective_hermitian K hK v hv
  exact ⟨u, by simp [hu, hy]⟩

theorem legalOutput_map_nhds (h : BlochVec) (K : KMatrix) (hK : K.PosDef)
    (hx : ambientX (blochMatrix h K) (drift K) ≠ 1) :
    Filter.map (legalOutput K) (𝓝 (h,0)) = 𝓝 (canonicalXY (h,K)) := by
  have hh := (legalOutput_hasStrictFDerivAt h K).map_nhds_eq_of_surj
    (LinearMap.range_eq_top.mpr (legalOutputDerivative_surjective h K hK hx))
  simpa [legalOutput, legalParameters_base] using hh

/-- 论文 (x,z) 与原始 (a,b) 概率平面的实际仿射同胚。 -/
def probabilityHomeomorph : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun p := ((1+p.1+p.2)/2, (1+p.1-p.2)/2)
  invFun p := (p.1+p.2-1, p.1-p.2)
  left_inv p := by ext <;> dsimp <;> ring
  right_inv p := by ext <;> dsimp <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem probabilityHomeomorph_canonicalXY (p : ExponentialGradient.Parameters) :
    probabilityHomeomorph (canonicalXY p) = canonicalOutput p.1 p.2 1 := by
  apply Prod.ext <;> simp [probabilityHomeomorph, canonicalXY, canonicalScalar]

def legalProbabilityOutput (K : KMatrix) : ExponentialGradient.Parameters → ℝ × ℝ :=
  probabilityHomeomorph ∘ legalOutput K

theorem legalProbabilityOutput_eq (K : KMatrix) (p : ExponentialGradient.Parameters) :
    legalProbabilityOutput K p =
      canonicalOutput (legalParameters K p).1 (legalParameters K p).2 1 :=
  probabilityHomeomorph_canonicalXY _

theorem legalProbabilityOutput_mem_finiteOutputs (K : KMatrix) (hK : K.PosSemidef)
    (p : ExponentialGradient.Parameters) : legalProbabilityOutput K p ∈ finiteOutputs := by
  rw [legalProbabilityOutput_eq, finiteOutputs_eq_canonicalOutputs]
  exact ⟨(legalParameters K p).1, (legalParameters K p).2,
    legalParameters_psd K hK p, rfl⟩

theorem legalProbabilityOutput_map_nhds (h : BlochVec) (K : KMatrix) (hK : K.PosDef)
    (hx : ambientX (blochMatrix h K) (drift K) ≠ 1) :
    Filter.map (legalProbabilityOutput K) (𝓝 (h,0)) = 𝓝 (canonicalOutput h K 1) := by
  rw [legalProbabilityOutput, ← Filter.map_map, legalOutput_map_nhds h K hK hx,
    probabilityHomeomorph.map_nhds_eq, probabilityHomeomorph_canonicalXY]

/-- 正定噪声且 x≠1 时，有限可达集合已经包含原概率点的完整开邻域。 -/
theorem posDef_output_mem_interior_finiteOutputs (h : BlochVec) (K : KMatrix) (hK : K.PosDef)
    (hx : (canonicalOutput h K 1).1 + (canonicalOutput h K 1).2 - 1 ≠ 1) :
    canonicalOutput h K 1 ∈ interior finiteOutputs := by
  have hxa : ambientX (blochMatrix h K) (drift K) ≠ 1 := by
    rwa [ambientX_canonical]
  have hm : finiteOutputs ∈ Filter.map (legalProbabilityOutput K) (𝓝 (h,0)) := by
    exact Filter.mem_map.mpr (Filter.Eventually.of_forall
      (legalProbabilityOutput_mem_finiteOutputs K hK.posSemidef))
  rw [legalProbabilityOutput_map_nhds h K hK hxa] at hm
  exact mem_interior_iff_mem_nhds.mpr hm

theorem posDef_output_mem_interior_Q2 (h : BlochVec) (K : KMatrix) (hK : K.PosDef)
    (hx : (canonicalOutput h K 1).1 + (canonicalOutput h K 1).2 - 1 ≠ 1) :
    canonicalOutput h K 1 ∈ interior Q2 := by
  exact (interior_mono (show finiteOutputs ⊆ Q2 from subset_closure))
    (posDef_output_mem_interior_finiteOutputs h K hK hx)

theorem posDef_nonclassical_output_mem_interior_Q2 (h : BlochVec) (K : KMatrix)
    (hK : K.PosDef)
    (hx : (canonicalOutput h K 1).1 + (canonicalOutput h K 1).2 - 1 < 0) :
    canonicalOutput h K 1 ∈ interior Q2 :=
  posDef_output_mem_interior_Q2 h K hK (by linarith)

theorem posDef_of_psd_rank_three (K : KMatrix) (hK : K.PosSemidef) (hr : K.rank = 3) :
    K.PosDef := by
  apply hK.posDef_iff_isUnit.mpr
  apply Matrix.mulVec_surjective_iff_isUnit.mp
  apply Matrix.mulVec_surjective_iff_rank_eq_card.mpr
  simpa using hr

/-- 非经典边界的任意有限 PSD 表示均不能具有满秩噪声。 -/
theorem rank_ne_three_of_nonclassical_frontier (h : BlochVec) (K : KMatrix)
    (hK : K.PosSemidef)
    (hx : (canonicalOutput h K 1).1 + (canonicalOutput h K 1).2 - 1 < 0)
    (hb : canonicalOutput h K 1 ∈ frontier Q2) : K.rank ≠ 3 := by
  intro hr
  have hi := posDef_nonclassical_output_mem_interior_Q2 h K (posDef_of_psd_rank_three K hK hr) hx
  exact hb.2 hi

#print axioms ambientCanonicalEquiv
#print axioms ambientDerivative_surjective
#print axioms ambientOutput_map_nhds
#print axioms canonicalXYDerivative_hermitian_surjective
#print axioms legalParameters_hasStrictFDerivAt
#print axioms legalDerivative_surjective_hermitian
#print axioms legalOutput_map_nhds
#print axioms posDef_output_mem_interior_finiteOutputs
#print axioms posDef_output_mem_interior_Q2
#print axioms rank_ne_three_of_nonclassical_frontier

end TwoStateQuantumEmbedding.AmbientSubmersion
