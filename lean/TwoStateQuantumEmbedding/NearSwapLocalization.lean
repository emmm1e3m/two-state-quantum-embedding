import TwoStateQuantumEmbedding.LocalizationCore
import TwoStateQuantumEmbedding.ActualSwapComparison

/-! 真实全部近优生成元的统一定位；所有常数只依赖近优系数 C。 -/
noncomputable section
open Matrix Complex Filter
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator Topology

namespace TwoStateQuantumEmbedding.NearSwap
open GKSLAlgebra GKSLBounds CanonicalBloch
set_option maxRecDepth 2500
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- 将全部统一结论记录在实际生成元上，不附加近似模型假设。 -/
structure Localized (C b hx hz : ℝ) (K : Matrix (Fin 3) (Fin 3) ℂ) : Prop where
  hx_pos : 0 < hx
  probability_le : unitaryProbability ![hx, 0, hz] 1 ≤ probabilityConstant C * b ^ 2
  dissipation_lower : b / 4 ≤ dissipationSize K
  dissipation_upper : dissipationSize K ≤ scale * b
  perpendicular_le : (perpendicularProjector * K).trace.re ≤ probabilityConstant C * b ^ 2
  hamiltonian_close : ‖euclid ![hx, 0, hz] - euclid ![Real.pi, 0, 0]‖ ≤
    20 * Real.sqrt (probabilityConstant C) * b
  hamiltonian_bounded : ‖(![hx, 0, hz] : BlochVec)‖ ≤ 6
  normalized_close : ‖normalizedNoise K - kernelProjector‖ ≤ matrixError C b
  scale_ratio_close : |dissipationSize K / b - inverseScaleLimit⁻¹| ≤ scaleError C b
  first_circle_angle : |Real.sqrt (hx ^ 2 + hz ^ 2) / 2 - Real.pi / 2| ≤
    2 * Real.sqrt (unitaryProbability ![hx, 0, hz] 1)
  first_circle_a : |(canonicalOutput ![hx, 0, hz] K 1).1 -
    unitaryProbability ![hx, 0, hz] 1 - (Swap.matrixQa 0 * K).trace.re| ≤ errorConstant C * b ^ 2
  first_circle_b : |b - unitaryProbability ![hx, 0, hz] 1 -
    (Swap.matrixQb 0 * K).trace.re| ≤ errorConstant C * b ^ 2

/-- 实际 B2 的存在圈数由统一谱能量强制为零，随后给出所有定量定位。 -/
theorem canonical_planar_localization (hx hz : ℝ) (K : Matrix (Fin 3) (Fin 3) ℂ)
    (hhx : 0 ≤ hx) (hK : K.PosSemidef) (C b : ℝ) (hC : 0 < C) (hb : 0 < b)
    (hsmall : b ≤ radius C) (hbe : b = (canonicalOutput ![hx, 0, hz] K 1).2)
    (hnear : (canonicalOutput ![hx, 0, hz] K 1).1 ≤ Swap.slope * b + C * b ^ 2) :
    Localized C b hx hz K := by
  let a := (canonicalOutput ![hx, 0, hz] K 1).1
  let p := unitaryProbability ![hx, 0, hz] 1
  let θ := Real.sqrt (hx ^ 2 + hz ^ 2) / 2
  have hp : 0 ≤ p := unitaryProbability_nonneg _
  have hd := dissipationSize_nonneg K hK
  obtain ⟨_, _, hsum, hdhi⟩ := canonical_near_scale ![hx, 0, hz] K hK C a b hC hb
    hsmall rfl hbe hnear
  obtain ⟨j, _, hangle, haxis, hRa, hRb⟩ := SwapComparison.canonical_near_swap_comparison
    hx hz K hhx hK (a + b) (by rw [hbe]) hsum
  have hRb' : |b - p - (Swap.matrixQb j * K).trace.re| ≤ Swap.remainderSize p (dissipationSize K) := by
    simpa only [hbe, p, Swap.remainderSize] using hRb
  have hRa' : |a - p - (Swap.matrixQa j * K).trace.re| ≤ Swap.remainderSize p (dissipationSize K) := hRa
  obtain ⟨hj, hprob, hdlo, hperp⟩ := matrix_localization_of_remainders K hK j C a b p
    hC hb hsmall hp hRa' hRb' hnear hdhi
  subst j
  have hangle0 : |θ - Real.pi / 2| ≤ 2 * Real.sqrt p := by
    simpa only [Swap.frequency_zero] using hangle
  have hpmax := localized_probability_small C b p hC hb hsmall hprob
  have hθsq : (2 * θ) ^ 2 = hx ^ 2 + hz ^ 2 := by
    have hh := Real.sq_sqrt (add_nonneg (sq_nonneg hx) (sq_nonneg hz))
    dsimp [θ]
    nlinarith
  obtain ⟨hhxpos, hhxerr, hhzerr⟩ := hamiltonian_coordinate_bounds hx hz θ p hhx
    (by dsimp [θ]; positivity) hθsq hp hpmax hangle0 haxis
  have hsqrt : Real.sqrt p ≤ Real.sqrt (probabilityConstant C) * b := by
    have hP := probabilityConstant_pos C hC
    have hsq : (Real.sqrt (probabilityConstant C) * b) ^ 2 = probabilityConstant C * b ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hP.le]
    nlinarith [Real.sq_sqrt hp, Real.sqrt_nonneg p,
      mul_nonneg (Real.sqrt_nonneg (probabilityConstant C)) hb.le]
  have herr : Swap.remainderSize p (dissipationSize K) ≤ errorConstant C * b ^ 2 := by
    have hm := mul_le_mul hdhi hsqrt (Real.sqrt_nonneg p) (by dsimp [scale]; positivity)
    have hsq : dissipationSize K ^ 2 ≤ (scale * b) ^ 2 :=
      (sq_le_sq₀ hd (by dsimp [scale]; positivity)).mpr hdhi
    unfold Swap.remainderSize errorConstant
    nlinarith
  have hRblast := hRb'.trans herr
  refine ⟨hhxpos, hprob, hdlo, hdhi, hperp, ?_,
    hamiltonian_pi_norm_bound hx hz p hp hpmax hhxerr hhzerr,
    normalized_noise_bound K hK C b hC hb hdlo hdhi hperp,
    scale_ratio_bound K hK C b p hC hb hp hprob hdlo hdhi hperp hRblast,
    hangle0, hRa'.trans herr, hRblast⟩
  have hh := hamiltonian_norm_bound hx hz p hhxerr hhzerr
  nlinarith

def gaugeHamiltonian (h : BlochVec) : BlochVec := ![AzimuthGauge.transverseRadius h, 0, h 2]
def gaugeNoise (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  AzimuthGauge.rotateNoise (AzimuthGauge.gaugeRotation h) K

theorem gaugeNoise_posSemidef (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ) (hK : K.PosSemidef) :
    (gaugeNoise h K).PosSemidef := AzimuthGauge.rotateNoise_posSemidef _ K hK

theorem gaugeNoise_trace (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ) :
    (gaugeNoise h K).trace = K.trace :=
  AzimuthGauge.rotateNoise_trace _ (AzimuthGauge.gaugeRotation_orthogonal h) K

theorem gaugeNoise_dissipation (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ) :
    dissipationSize (gaugeNoise h K) = dissipationSize K := by
  simp only [dissipationSize, Rigidity.trace_realPart, gaugeNoise_trace]

theorem gaugeOutput_eq (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ) (hK : K.IsHermitian) (t : ℝ) :
    canonicalOutput (gaugeHamiltonian h) (gaugeNoise h K) t = canonicalOutput h K t :=
  AzimuthGauge.canonicalOutput_normal_form h K hK t

/-- 同一正半径对全部合法规范生成元成立；方位规范固定 ez 并保留全部时间的真实输出。 -/
theorem canonical_near_localization (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ)
    (hK : K.PosSemidef) (C b : ℝ) (hC : 0 < C) (hb : 0 < b)
    (hsmall : b ≤ radius C) (hbe : b = (canonicalOutput h K 1).2)
    (hnear : (canonicalOutput h K 1).1 ≤ Swap.slope * b + C * b ^ 2) :
    Localized C b (AzimuthGauge.transverseRadius h) (h 2) (gaugeNoise h K) := by
  apply canonical_planar_localization _ _ _ (AzimuthGauge.transverseRadius_nonneg h)
    (gaugeNoise_posSemidef h K hK) C b hC hb hsmall
  · change b = (canonicalOutput (gaugeHamiltonian h) (gaugeNoise h K) 1).2
    rw [gaugeOutput_eq h K hK.isHermitian]
    exact hbe
  · change (canonicalOutput (gaugeHamiltonian h) (gaugeNoise h K) 1).1 ≤ _
    rw [gaugeOutput_eq h K hK.isHermitian]
    exact hnear

/-- 对原始 finiteOutputs 的紧性接口；参数盒固定为 6 和 1，只有半径依赖 C。 -/
theorem finite_near_bounded_parameters (C : ℝ) (hC : 0 < C) (q : ℝ × ℝ)
    (hq : q ∈ finiteOutputs) (hb : 0 < q.2) (hsmall : q.2 ≤ radius C)
    (hnear : q.1 ≤ Swap.slope * q.2 + C * q.2 ^ 2) :
    ∃ (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ),
      K.PosSemidef ∧ ‖h‖ ≤ 6 ∧ K.trace.re ≤ 1 ∧ canonicalOutput h K 1 = q := by
  rw [finiteOutputs_eq_canonicalOutputs] at hq
  obtain ⟨h, K, hK, hout⟩ := hq
  have hloc := canonical_near_localization h K hK C q.2 hC hb hsmall
    (by rw [hout]) (by rw [hout]; exact hnear)
  refine ⟨gaugeHamiltonian h, gaugeNoise h K, gaugeNoise_posSemidef h K hK,
    hloc.hamiltonian_bounded, ?_, (gaugeOutput_eq h K hK.isHermitian 1).trans hout⟩
  have hd := hloc.dissipation_upper
  have hbmax := (radius_bounds C q.2 hsmall).1
  rw [dissipationSize, Rigidity.trace_realPart] at hd
  dsimp [scale] at hd
  linarith

theorem uniform_finite_near_bounded_parameters (C : ℝ) (hC : 0 < C) :
    ∃ η : ℝ, 0 < η ∧ ∀ q ∈ finiteOutputs, 0 < q.2 → q.2 ≤ η →
      q.1 ≤ Swap.slope * q.2 + C * q.2 ^ 2 →
      ∃ (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ),
        K.PosSemidef ∧ ‖h‖ ≤ 6 ∧ K.trace.re ≤ 1 ∧ canonicalOutput h K 1 = q :=
  ⟨radius C, radius_pos C hC, fun q hq hb hsmall hnear =>
    finite_near_bounded_parameters C hC q hq hb hsmall hnear⟩

/-- 原始任意有限跳跃族的完整定位，规范代表保持全部实时间输出。 -/
theorem finite_near_localization {n : ℕ} (H : QubitMatrix) (hH : H.IsHermitian)
    (A : Fin n → QubitMatrix) (C b : ℝ) (hC : 0 < C) (hb : 0 < b)
    (hsmall : b ≤ radius C) (hbe : b = (finiteOutput H A 1).2)
    (hnear : (finiteOutput H A 1).1 ≤ Swap.slope * b + C * b ^ 2) :
    ∃ (hx hz : ℝ) (K : Matrix (Fin 3) (Fin 3) ℂ), K.PosSemidef ∧
      (∀ t : ℝ, canonicalOutput ![hx, 0, hz] K t = finiteOutput H A t) ∧
      Localized C b hx hz K := by
  let h := hamiltonianVector (canonicalHamiltonian H A)
  let K := GKSLAlgebra.kossakowski (fun μ => pauliCoeffs (A μ))
  have hK : K.PosSemidef := kossakowski_posSemidef _
  have he (t : ℝ) : finiteOutput H A t = canonicalOutput h K t :=
    finiteOutput_eq_canonicalOutput H hH A t
  refine ⟨AzimuthGauge.transverseRadius h, h 2, gaugeNoise h K,
    gaugeNoise_posSemidef h K hK, ?_, ?_⟩
  · intro t
    exact (gaugeOutput_eq h K hK.isHermitian t).trans (he t).symm
  · apply canonical_near_localization h K hK C b hC hb hsmall
    · rw [← he]; exact hbe
    · rw [← he]; exact hnear

theorem normalizedNoise_rescale (K : Matrix (Fin 3) (Fin 3) ℂ)
    (hd : 0 < dissipationSize K) : K = dissipationSize K • normalizedNoise K := by
  change K = ((dissipationSize K : ℝ) : ℂ) •
    ((((dissipationSize K)⁻¹ : ℝ) : ℂ) • K)
  rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hd.ne', Complex.ofReal_one, one_smul]

/-- 定量误差给出任意滤子上的统一极限，因此也覆盖任意近优序列。 -/
theorem localized_tendsto {α : Type*} (F : Filter α) (C : ℝ)
    (hx hz b : α → ℝ) (K : α → Matrix (Fin 3) (Fin 3) ℂ)
    (hb : Tendsto b F (𝓝 0))
    (hloc : ∀ᶠ x in F, Localized C (b x) (hx x) (hz x) (K x)) :
    Tendsto (fun x => euclid ![hx x, 0, hz x]) F (𝓝 (euclid ![Real.pi, 0, 0])) ∧
      Tendsto (fun x => normalizedNoise (K x)) F (𝓝 kernelProjector) ∧
      Tendsto (fun x => dissipationSize (K x) / b x) F (𝓝 inverseScaleLimit⁻¹) := by
  refine ⟨?_, ?_, ?_⟩
  · apply tendsto_sub_nhds_zero_iff.mp
    apply squeeze_zero_norm' (hloc.mono (fun _ hh => hh.hamiltonian_close))
    simpa using tendsto_const_nhds.mul hb
  · apply tendsto_sub_nhds_zero_iff.mp
    exact squeeze_zero_norm' (hloc.mono (fun _ hh => hh.normalized_close))
      ((matrixError_tendsto_zero C).comp hb)
  · apply tendsto_sub_nhds_zero_iff.mp
    apply squeeze_zero_norm' (hloc.mono (fun x hh => ?_)) ((scaleError_tendsto_zero C).comp hb)
    simpa only [Real.norm_eq_abs, Function.comp_def] using hh.scale_ratio_close

/-- 全体实际合法规范生成元的近优滤子极限，无预先紧性、圈数或秩假设。 -/
theorem canonical_near_tendsto {α : Type*} (F : Filter α) (C : ℝ) (hC : 0 < C)
    (h : α → BlochVec) (K : α → Matrix (Fin 3) (Fin 3) ℂ)
    (hlegal : ∀ᶠ x in F, (K x).PosSemidef)
    (hbpos : ∀ᶠ x in F, 0 < (canonicalOutput (h x) (K x) 1).2)
    (hb : Tendsto (fun x => (canonicalOutput (h x) (K x) 1).2) F (𝓝 0))
    (hnear : ∀ᶠ x in F, (canonicalOutput (h x) (K x) 1).1 ≤
      Swap.slope * (canonicalOutput (h x) (K x) 1).2 +
        C * (canonicalOutput (h x) (K x) 1).2 ^ 2) :
    Tendsto (fun x => euclid (gaugeHamiltonian (h x))) F (𝓝 (euclid ![Real.pi, 0, 0])) ∧
      Tendsto (fun x => normalizedNoise (gaugeNoise (h x) (K x))) F (𝓝 kernelProjector) ∧
      Tendsto (fun x => dissipationSize (gaugeNoise (h x) (K x)) /
        (canonicalOutput (h x) (K x) 1).2) F (𝓝 inverseScaleLimit⁻¹) := by
  have hs : ∀ᶠ x in F, (canonicalOutput (h x) (K x) 1).2 < radius C :=
    hb.eventually (gt_mem_nhds (radius_pos C hC))
  apply localized_tendsto F C (fun x => AzimuthGauge.transverseRadius (h x))
    (fun x => h x 2) (fun x => (canonicalOutput (h x) (K x) 1).2)
    (fun x => gaugeNoise (h x) (K x)) hb
  filter_upwards [hlegal, hbpos, hs, hnear] with x hK hbpos hs hnear
  exact canonical_near_localization (h x) (K x) hK C _ hC hbpos hs.le rfl hnear

/-- 用于固定开邻域与 KKT 的完整参数三元组收敛。 -/
theorem canonical_normalized_parameters_tendsto {α : Type*} (F : Filter α) (C : ℝ) (hC : 0 < C)
    (h : α → BlochVec) (K : α → Matrix (Fin 3) (Fin 3) ℂ)
    (hlegal : ∀ᶠ x in F, (K x).PosSemidef)
    (hbpos : ∀ᶠ x in F, 0 < (canonicalOutput (h x) (K x) 1).2)
    (hb : Tendsto (fun x => (canonicalOutput (h x) (K x) 1).2) F (𝓝 0))
    (hnear : ∀ᶠ x in F, (canonicalOutput (h x) (K x) 1).1 ≤
      Swap.slope * (canonicalOutput (h x) (K x) 1).2 +
        C * (canonicalOutput (h x) (K x) 1).2 ^ 2) :
    Tendsto (fun x => ((gaugeHamiltonian (h x), gaugeNoise (h x) (K x)),
      normalizedNoise (gaugeNoise (h x) (K x)))) F
      (𝓝 (((![Real.pi, 0, 0] : BlochVec), (0 : Matrix (Fin 3) (Fin 3) ℂ)), kernelProjector)) := by
  obtain ⟨hh, hW, _⟩ := canonical_near_tendsto F C hC h K hlegal hbpos hb hnear
  have hH : Tendsto (fun x => gaugeHamiltonian (h x)) F (𝓝 (![Real.pi, 0, 0] : BlochVec)) := by
    have hc := (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ)).tendsto (euclid ![Real.pi, 0, 0])
    simpa only [Function.comp_def, euclid, WithLp.ofLp_toLp] using hc.comp hh
  have hs : ∀ᶠ x in F, (canonicalOutput (h x) (K x) 1).2 < radius C :=
    hb.eventually (gt_mem_nhds (radius_pos C hC))
  have hzero : Tendsto (fun x => gaugeNoise (h x) (K x)) F (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun x => scale * (canonicalOutput (h x) (K x) 1).2)
    · filter_upwards [hlegal, hbpos, hs, hnear] with x hK hbpos hs hnear
      have hloc := canonical_near_localization (h x) (K x) hK C _ hC hbpos hs.le rfl hnear
      exact (psd_norm_le_dissipation _ (gaugeNoise_posSemidef (h x) (K x) hK)).trans
        hloc.dissipation_upper
    · simpa using tendsto_const_nhds.mul hb
  exact (hH.prodMk_nhds hzero).prodMk_nhds hW

#print axioms canonical_planar_localization
#print axioms canonical_near_localization
#print axioms finite_near_bounded_parameters
#print axioms uniform_finite_near_bounded_parameters
#print axioms finite_near_localization
#print axioms canonical_near_tendsto
#print axioms canonical_normalized_parameters_tendsto
end TwoStateQuantumEmbedding.NearSwap
