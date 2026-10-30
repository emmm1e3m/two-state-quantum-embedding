import TwoStateQuantumEmbedding.CanonicalGradient
import TwoStateQuantumEmbedding.UnitaryBoundary
import TwoStateQuantumEmbedding.ActualSwapSystem
import TwoStateQuantumEmbedding.RankOneChart

/-! 由真实等式约束极小值构造双侧隐函数，再推出 Hamiltonian 与完整坐标驻点。 -/
noncomputable section
open Matrix Filter Set
open scoped Topology Matrix.Norms.Operator ComplexOrder

namespace TwoStateQuantumEmbedding.EqualityIFT

/-- 真正构造保持约束的双侧隐函数；没有将可行曲线作为前提。 -/
theorem constrained_plane_stationarity
    {f g : ℝ × ℝ → ℝ} {f' g' : (ℝ × ℝ) →L[ℝ] ℝ}
    (hf : HasFDerivAt f f' (0, 0))
    (hg : HasStrictFDerivAt g g' (0, 0))
    (hreg : g' (0, 1) ≠ 0)
    (hmin : IsLocalMinOn f {p | g p = g (0, 0)} (0, 0)) :
    f' (1, 0) - (f' (0, 1) / g' (0, 1)) * g' (1, 0) = 0 := by
  have hinv : (g' ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    apply ConeIFT.scalar_isInvertible
    simpa using hreg
  let ψ : ℝ → ℝ := hg.implicitFunctionOfProdDomain hinv
  have hψ0 : ψ 0 = 0 :=
    (hg.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv).self_of_nhds.mp rfl
  let L : ℝ →L[ℝ] ℝ :=
    -(g' ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).inverse ∘L
      (g' ∘L ContinuousLinearMap.inl ℝ ℝ ℝ)
  have hψ : HasDerivAt ψ (L 1) 0 :=
    (hg.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv).hasFDerivAt.hasDerivAt
  let c : ℝ → ℝ × ℝ := fun t => (t, ψ t)
  have hc0 : c 0 = (0, 0) := by simp [c, hψ0]
  have hc : HasDerivAt c (1, L 1) 0 := (hasDerivAt_id 0).prodMk hψ
  have hgcurve : ∀ᶠ t in 𝓝 (0 : ℝ), g (c t) = g (0, 0) :=
    hg.eventually_apply_implicitFunctionOfProdDomain hinv
  have hgder : g' (1, L 1) = 0 := by
    have hd := hg.hasFDerivAt.comp_hasDerivAt_of_eq 0 hc hc0.symm
    have hdconst : HasDerivAt (fun _ : ℝ => g (0, 0)) (g' (1, L 1)) 0 :=
      hd.congr_of_eventuallyEq (hgcurve.mono fun t ht => ht.symm)
    exact hdconst.unique (hasDerivAt_const 0 (g (0, 0)))
  have hctend : Tendsto c (𝓝 (0 : ℝ))
      (𝓝[{p | g p = g (0, 0)}] (0, 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨by simpa [hc0] using hc.continuousAt.tendsto, hgcurve⟩
  have hfcurve : IsLocalMin (f ∘ c) 0 := by
    change ∀ᶠ t in 𝓝 (0 : ℝ), (f ∘ c) 0 ≤ (f ∘ c) t
    simpa [Function.comp_def, hc0] using hctend.eventually hmin
  have hzero : f' (1, L 1) = 0 :=
    hfcurve.hasDerivAt_eq_zero (hf.comp_hasDerivAt_of_eq 0 hc hc0.symm)
  have heval (T : (ℝ × ℝ) →L[ℝ] ℝ) :
      T (1, L 1) = T (1, 0) + L 1 * T (0, 1) := by
    have hv : (1, L 1) = ((1, 0) : ℝ × ℝ) + L 1 • ((0, 1) : ℝ × ℝ) := by
      ext <;> simp
    rw [hv, map_add, map_smul]
    rfl
  rw [heval] at hgder hzero
  have hslope : L 1 = -(g' (1, 0)) / g' (0, 1) := by
    apply (eq_div_iff hreg).mpr
    linarith
  rw [hslope] at hzero
  convert hzero using 1; ring

/-- 任意实范数空间上的等式约束驻点；乘子由指定非零约束方向确定。 -/
theorem lagrange_of_localMin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : E → ℝ} {a' b' : E →L[ℝ] ℝ} {x : E}
    (ha : HasFDerivAt a a' x) (hb : HasStrictFDerivAt b b' x)
    (u : E) (hreg : b' u ≠ 0)
    (hmin : IsLocalMinOn a {q | b q = b x} x) :
    a' - (a' u / b' u) • b' = 0 := by
  ext v
  let D : (ℝ × ℝ) →L[ℝ] E :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight u
  let q : ℝ × ℝ → E := fun p => x + D p
  have hq0 : q (0, 0) = x := by simp [q, D]
  have hq : HasStrictFDerivAt q D (0, 0) := by
    simpa [q] using D.hasStrictFDerivAt.const_add x
  have haf : HasFDerivAt (a ∘ q) (a' ∘L D) (0, 0) :=
    (hq0.symm ▸ ha).comp (0, 0) hq.hasFDerivAt
  have hbf : HasStrictFDerivAt (b ∘ q) (b' ∘L D) (0, 0) :=
    (hq0.symm ▸ hb).comp (0, 0) hq
  have hlocal : IsLocalMinOn (a ∘ q)
      {p | (b ∘ q) p = (b ∘ q) (0, 0)} (0, 0) := by
    have hmap : Tendsto q
        (𝓝[{p | (b ∘ q) p = (b ∘ q) (0, 0)}] (0, 0))
        (𝓝[{z | b z = b x}] x) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · simpa [hq0] using hq.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with p hp
        simpa [Function.comp_def, hq0] using hp
    change ∀ᶠ p in 𝓝[{p | (b ∘ q) p = (b ∘ q) (0, 0)}] (0, 0),
      (a ∘ q) (0, 0) ≤ (a ∘ q) p
    simpa [Function.comp_def, hq0] using hmap.eventually hmin
  have hz := constrained_plane_stationarity haf hbf
    (by simpa [D] using hreg) hlocal
  simpa [D, _root_.sub_apply, _root_.smul_apply, smul_eq_mul] using hz

#print axioms constrained_plane_stationarity
#print axioms lagrange_of_localMin
end TwoStateQuantumEmbedding.EqualityIFT

namespace TwoStateQuantumEmbedding.CanonicalStationarity
open CanonicalBloch GKSLAlgebra ExponentialGradient CanonicalGradient
set_option backward.isDefEq.respectTransparency false

/-- 真正固定返回概率 b 的全局极小；Hamiltonian 与全部 PSD 矩阵均可变化。 -/
def IsGlobalMinimum (h : BlochVec) (K : KMatrix) : Prop :=
  ∀ (g : BlochVec) (W : KMatrix), W.PosSemidef →
    (canonicalOutput g W 1).2 = (canonicalOutput h K 1).2 →
    (canonicalOutput h K 1).1 ≤ (canonicalOutput g W 1).1

def multiplier (h : BlochVec) (K : KMatrix) : ℝ :=
  kDerivative (1/2) (1/2) (h, K) K / kDerivative (1/2) (-1/2) (h, K) K

/-- 下边界的实际达到点自动是上述全参数极小，无额外最优性假设。 -/
theorem globalMinimum_of_lowerBoundary (h : BlochVec) (K : KMatrix)
    (hK : K.PosSemidef) (b : ℝ)
    (he : canonicalOutput h K 1 = (lowerBoundary b, b)) : IsGlobalMinimum h K := by
  have hmem := canonicalOutput_mem_Q2 h K hK 1 (by norm_num)
  rw [he] at hmem
  have hb : b ∈ Icc (0 : ℝ) 1 := (Q2_subset_unitSquare hmem).2
  intro g W hW hB
  have hw := canonicalOutput_mem_Q2 g W hW 1 (by norm_num)
  have hbw : (canonicalOutput g W 1).2 = b := by simpa [he] using hB
  have hw' : ((canonicalOutput g W 1).1, b) ∈ Q2 := by
    simpa only [← hbw, Prod.mk.eta] using hw
  simpa only [he, Prod.fst] using lowerBoundary_le_of_mem hb hw'

def radialLift (h : BlochVec) (K : KMatrix) (p : BlochVec × ℝ) :
    ExponentialGradient.Parameters := (h + p.1, p.2 • K)

def radialLiftDerivative (K : KMatrix) :
    (BlochVec × ℝ) →L[ℝ] ExponentialGradient.Parameters :=
  (ContinuousLinearMap.fst ℝ BlochVec ℝ).prod
    ((ContinuousLinearMap.snd ℝ BlochVec ℝ).smulRight K)

theorem radialLift_hasStrictFDerivAt (h : BlochVec) (K : KMatrix) :
    HasStrictFDerivAt (radialLift h K) (radialLiftDerivative K) (0, 1) := by
  exact (hasStrictFDerivAt_fst.const_add h).prodMk (hasStrictFDerivAt_snd.smul_const K)

/-- 正尺度邻域内保持 PSD，双侧 Hamiltonian 变化由真实全局极小控制。 -/
theorem radialLift_localMin (h : BlochVec) (K : KMatrix) (hK : K.PosSemidef)
    (hmin : IsGlobalMinimum h K) :
    IsLocalMinOn (fun p : BlochVec × ℝ =>
      (canonicalOutput (h + p.1) (p.2 • K) 1).1)
      {p | (canonicalOutput (h + p.1) (p.2 • K) 1).2 =
        (canonicalOutput h K 1).2} (0, 1) := by
  have hs : ∀ᶠ p : BlochVec × ℝ in 𝓝 (0, 1), 0 < p.2 :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds (by norm_num)
  filter_upwards [hs.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with p hp hb
  simpa using hmin (h + p.1) (p.2 • K) (hK.smul hp.le) hb

/-- 由实际全局极小及非零径向 db 得到完整三维 Hamiltonian 梯度为零。 -/
theorem hGradient_stationarity_of_globalMinimum (h : BlochVec) (K : KMatrix)
    (hK : K.PosSemidef)
    (hreg : kDerivative (1/2) (-1/2) (h, K) K ≠ 0)
    (hmin : IsGlobalMinimum h K) :
    hGradient (1/2) (1/2) (h, K) -
      multiplier h K • hGradient (1/2) (-1/2) (h, K) = 0 := by
  let q := radialLift h K
  let D := radialLiftDerivative K
  have hq0 : q (0, 1) = (h, K) := by simp [q, radialLift]
  have hqa := (hq0.symm ▸ hasStrictFDerivAt_canonical_a (h, K)).comp (0, 1)
    (radialLift_hasStrictFDerivAt h K)
  have hqb := (hq0.symm ▸ hasStrictFDerivAt_canonical_b (h, K)).comp (0, 1)
    (radialLift_hasStrictFDerivAt h K)
  have hl := EqualityIFT.lagrange_of_localMin hqa.hasFDerivAt hqb
    ((0, 1) : BlochVec × ℝ) (by simpa [hq0, radialLiftDerivative, kDerivative] using hreg)
    (by simpa [q, radialLift, Function.comp_def] using radialLift_localMin h K hK hmin)
  funext i
  have hv := congrArg (fun L : (BlochVec × ℝ) →L[ℝ] ℝ => L (Pi.single i 1, 0)) hl
  simpa [hq0, radialLiftDerivative, multiplier, kDerivative, hDerivative, hGradient,
    _root_.sub_apply, _root_.smul_apply, smul_eq_mul] using hv

#print axioms globalMinimum_of_lowerBoundary
#print axioms hGradient_stationarity_of_globalMinimum

/-- 写成单个真实 canonicalScalar 梯度，权重对应 a−μb 的非常数部分。 -/
theorem hGradient_lagrangian (μ : ℝ) (p : ExponentialGradient.Parameters) :
    hGradient ((1-μ)/2) ((1+μ)/2) p =
      hGradient (1/2) (1/2) p - μ • hGradient (1/2) (-1/2) p := by
  funext i
  simp [hGradient, hDerivative, canonicalScalarDerivative, measurementCLM]
  ring

theorem hGradient_lagrangian_of_globalMinimum (h : BlochVec) (K : KMatrix)
    (hK : K.PosSemidef)
    (hreg : kDerivative (1/2) (-1/2) (h, K) K ≠ 0)
    (hmin : IsGlobalMinimum h K) :
    hGradient ((1-multiplier h K)/2) ((1+multiplier h K)/2) (h, K) = 0 := by
  rw [hGradient_lagrangian]
  exact hGradient_stationarity_of_globalMinimum h K hK hreg hmin

theorem hGradient_lagrangian_of_lowerBoundary (h : BlochVec) (K : KMatrix)
    (hK : K.PosSemidef)
    (hreg : kDerivative (1/2) (-1/2) (h, K) K ≠ 0)
    (b : ℝ) (he : canonicalOutput h K 1 = (lowerBoundary b, b)) :
    hGradient ((1-multiplier h K)/2) ((1+multiplier h K)/2) (h, K) = 0 :=
  hGradient_lagrangian_of_globalMinimum h K hK hreg
    (globalMinimum_of_lowerBoundary h K hK b he)

/-- 供 PSD 法向接口使用的固定 Hamiltonian 局部极小直接来自同一全局极小。 -/
theorem fixed_h_localMin_of_globalMinimum (h : BlochVec) (K : KMatrix)
    (hmin : IsGlobalMinimum h K) :
    IsLocalMinOn (fun W => (canonicalOutput h W 1).1)
      {W | W.PosSemidef ∧ (canonicalOutput h W 1).2 = (canonicalOutput h K 1).2} K := by
  filter_upwards [self_mem_nhdsWithin] with W hW
  exact hmin h W hW.1 hW.2

/-- 同一真实极小值同时满足 Hamiltonian 驻点、PSD 法向及矩阵互补性。 -/
theorem canonical_kkt_of_globalMinimum (h : BlochVec) (K : KMatrix)
    (hK : K.PosSemidef)
    (hreg : kDerivative (1/2) (-1/2) (h, K) K ≠ 0)
    (hmin : IsGlobalMinimum h K) :
    let μ := multiplier h K
    let S := kGradient (1/2) (1/2) (h, K) - μ • kGradient (1/2) (-1/2) (h, K)
    hGradient ((1-μ)/2) ((1+μ)/2) (h, K) = 0 ∧
      S.PosSemidef ∧ (S * K).trace.re = 0 ∧ S * K = 0 := by
  refine ⟨hGradient_lagrangian_of_globalMinimum h K hK hreg hmin, ?_⟩
  exact canonical_psd_normal_of_localMin h K hK hreg
    (fixed_h_localMin_of_globalMinimum h K hmin)

theorem canonical_kkt_of_lowerBoundary (h : BlochVec) (K : KMatrix)
    (hK : K.PosSemidef)
    (hreg : kDerivative (1/2) (-1/2) (h, K) K ≠ 0)
    (b : ℝ) (he : canonicalOutput h K 1 = (lowerBoundary b, b)) :
    let μ := multiplier h K
    let S := kGradient (1/2) (1/2) (h, K) - μ • kGradient (1/2) (-1/2) (h, K)
    hGradient ((1-μ)/2) ((1+μ)/2) (h, K) = 0 ∧
      S.PosSemidef ∧ (S * K).trace.re = 0 ∧ S * K = 0 :=
  canonical_kkt_of_globalMinimum h K hK hreg (globalMinimum_of_lowerBoundary h K hK b he)

#print axioms hGradient_lagrangian_of_lowerBoundary
#print axioms canonical_kkt_of_lowerBoundary
end TwoStateQuantumEmbedding.CanonicalStationarity

namespace TwoStateQuantumEmbedding.ActualSwapOptimality
open ActualSwapSystem CanonicalBloch GKSLAlgebra ExponentialGradient CanonicalGradient
open CanonicalStationarity
set_option backward.isDefEq.respectTransparency false

theorem probabilityA_eq_canonical (p : Input) :
    probabilityA p = (canonicalOutput (hamiltonianVector p.2) (kossakowskiMatrix p) 1).1 :=
  congrArg Prod.fst (probability_eq_canonical p)

theorem probabilityB_eq_canonical (p : Input) :
    probabilityB p = (canonicalOutput (hamiltonianVector p.2) (kossakowskiMatrix p) 1).2 :=
  congrArg Prod.snd (probability_eq_canonical p)

/-- 实际尺度方向 (k,0) 恰是 K 的径向变化，故其导数是同一个 da[K]。 -/
theorem probabilityA_radial_derivative (p : Input) :
    fderiv ℝ probabilityA p (p.1, 0) =
      kDerivative (1/2) (1/2) (hamiltonianVector p.2, kossakowskiMatrix p)
        (kossakowskiMatrix p) := by
  let c : ℝ → Input := fun r => (r * p.1, p.2)
  have hc : HasDerivAt c (p.1, 0) 1 := by
    simpa [c] using ((hasDerivAt_id 1).mul_const p.1).prodMk (hasDerivAt_const 1 p.2)
  have hc1 : c 1 = p := by simp [c]
  have hd := (analytic_probabilityA p).differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq
    1 hc hc1.symm
  let q : ℝ → ExponentialGradient.Parameters := fun r =>
    (hamiltonianVector p.2, r • kossakowskiMatrix p)
  have hq : HasDerivAt q (0, kossakowskiMatrix p) 1 := by
    simpa [q] using (hasDerivAt_const (1 : ℝ) (hamiltonianVector p.2)).prodMk
      ((hasDerivAt_id (1 : ℝ)).smul_const (kossakowskiMatrix p))
  have hd' := (hasStrictFDerivAt_canonical_a
    (hamiltonianVector p.2, kossakowskiMatrix p)).hasFDerivAt.comp_hasDerivAt_of_eq
      1 hq (by simp [q])
  have he : (fun r => probabilityA (c r)) =
      (fun r => (canonicalOutput (q r).1 (q r).2 1).1) := by
    funext r
    rw [probabilityA_eq_canonical]
    simp [c, q, kossakowskiMatrix, smul_smul]
  rw [show probabilityA ∘ c = (fun r => (canonicalOutput (q r).1 (q r).2 1).1)
    from he] at hd
  exact hd.unique hd'

/-- b 的实际尺度导数也与原始 canonical 径向导数一致。 -/
theorem probabilityB_radial_derivative (p : Input) :
    fderiv ℝ probabilityB p (p.1, 0) =
      kDerivative (1/2) (-1/2) (hamiltonianVector p.2, kossakowskiMatrix p)
        (kossakowskiMatrix p) := by
  let c : ℝ → Input := fun r => (r * p.1, p.2)
  have hc : HasDerivAt c (p.1, 0) 1 := by
    simpa [c] using ((hasDerivAt_id 1).mul_const p.1).prodMk (hasDerivAt_const 1 p.2)
  have hc1 : c 1 = p := by simp [c]
  have hd := (analytic_probabilityB p).differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq
    1 hc hc1.symm
  let q : ℝ → ExponentialGradient.Parameters := fun r =>
    (hamiltonianVector p.2, r • kossakowskiMatrix p)
  have hq : HasDerivAt q (0, kossakowskiMatrix p) 1 := by
    simpa [q] using (hasDerivAt_const (1 : ℝ) (hamiltonianVector p.2)).prodMk
      ((hasDerivAt_id (1 : ℝ)).smul_const (kossakowskiMatrix p))
  have hd' := (hasStrictFDerivAt_canonical_b
    (hamiltonianVector p.2, kossakowskiMatrix p)).hasFDerivAt.comp_hasDerivAt_of_eq
      1 hq (by simp [q])
  have he : (fun r => probabilityB (c r)) =
      (fun r => (canonicalOutput (q r).1 (q r).2 1).2) := by
    funext r
    rw [probabilityB_eq_canonical]
    simp [c, q, kossakowskiMatrix, smul_smul]
  rw [show probabilityB ∘ c = (fun r => (canonicalOutput (q r).1 (q r).2 1).2)
    from he] at hd
  exact hd.unique hd'

/-- k>0 的邻域内，所有七个坐标均保持实际 PSD 可实现性。 -/
theorem probability_localMin (p : Input) (hk : 0 < p.1)
    (hmin : IsGlobalMinimum (hamiltonianVector p.2) (kossakowskiMatrix p)) :
    IsLocalMinOn probabilityA {q | probabilityB q = probabilityB p} p := by
  have hs : ∀ᶠ q : Input in 𝓝 p, 0 < q.1 :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds hk
  filter_upwards [hs.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with q hq hb
  rw [probabilityA_eq_canonical, probabilityA_eq_canonical]
  apply hmin _ _ (kossakowskiMatrix_posSemidef q hq.le)
  simpa only [probabilityB_eq_canonical] using hb

/-- 固定乘子的真实 a−μb 全导数为零；这里尚未把 μ 自身作为 J 的变量求导。 -/
theorem probability_lagrange_of_globalMinimum (p : Input) (hk : 0 < p.1)
    (hreg : kDerivative (1/2) (-1/2)
      (hamiltonianVector p.2, kossakowskiMatrix p) (kossakowskiMatrix p) ≠ 0)
    (hmin : IsGlobalMinimum (hamiltonianVector p.2) (kossakowskiMatrix p)) :
    fderiv ℝ probabilityA p - multiplier (hamiltonianVector p.2) (kossakowskiMatrix p) •
      fderiv ℝ probabilityB p = 0 := by
  have hl := EqualityIFT.lagrange_of_localMin
    (analytic_probabilityA p).differentiableAt.hasFDerivAt
    (analytic_probabilityB p).hasStrictFDerivAt (p.1, 0)
    (by simpa only [probabilityB_radial_derivative] using hreg)
    (probability_localMin p hk hmin)
  simpa only [probabilityA_radial_derivative, probabilityB_radial_derivative, multiplier] using hl

/-- J 的方向中 μ 不变化时，其导数就是固定乘子的 Lagrange 导数。 -/
theorem objective_derivative_fixed_multiplier (p v : Input) (hv : v.2 2 = 0) :
    fderiv ℝ objective p v = fderiv ℝ probabilityA p v - p.2 2 * fderiv ℝ probabilityB p v := by
  let M : Input →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (2 : Fin 7)).comp
      (ContinuousLinearMap.snd ℝ ℝ ActualSwapSystem.Parameters)
  have hm : HasFDerivAt (fun q : Input => q.2 2) M p := M.hasFDerivAt
  have hd := (analytic_probabilityA p).differentiableAt.hasFDerivAt.sub
    (hm.mul (analytic_probabilityB p).differentiableAt.hasFDerivAt)
  rw [show fderiv ℝ objective p = _ from hd.fderiv]
  simp [M, hv, smul_eq_mul]

/-- 全部真实七方程；第三行是尺度 k 的驻点，不是 μ 的偏导。 -/
theorem stationarity_zero_of_globalMinimum (p : Input) (hk : 0 < p.1)
    (hreg : kDerivative (1/2) (-1/2)
      (hamiltonianVector p.2, kossakowskiMatrix p) (kossakowskiMatrix p) ≠ 0)
    (hμ : p.2 2 = multiplier (hamiltonianVector p.2) (kossakowskiMatrix p))
    (hmin : IsGlobalMinimum (hamiltonianVector p.2) (kossakowskiMatrix p)) :
    stationarity p = 0 := by
  have hl := probability_lagrange_of_globalMinimum p hk hreg hmin
  have hdir (v : Input) (hv : v.2 2 = 0) : fderiv ℝ objective p v = 0 := by
    rw [objective_derivative_fixed_multiplier p v hv, hμ]
    have he := congrArg (fun L : Input →L[ℝ] ℝ => L v) hl
    simpa only [_root_.sub_apply, _root_.smul_apply, smul_eq_mul,
      _root_.zero_apply] using he
  apply (stationarity_zero_iff_raw p hk.ne').mpr
  funext i
  fin_cases i
  · simpa [rawStationarity] using hdir (0, Pi.single 0 1) (by simp)
  · simpa [rawStationarity] using hdir (0, Pi.single 1 1) (by simp)
  · simpa [rawStationarity] using hdir (1, 0) (by simp)
  · simpa [rawStationarity] using hdir (0, directionVector 0) (by simp [directionVector, directionIndex])
  · simpa [rawStationarity] using hdir (0, directionVector 1) (by simp [directionVector, directionIndex])
  · simpa [rawStationarity] using hdir (0, directionVector 2) (by simp [directionVector, directionIndex])
  · simpa [rawStationarity] using hdir (0, directionVector 3) (by simp [directionVector, directionIndex])

#print axioms probabilityA_radial_derivative
#print axioms probabilityB_radial_derivative
#print axioms probability_lagrange_of_globalMinimum
#print axioms stationarity_zero_of_globalMinimum

/-- 完整秩一坐标图中的全局极小必为实际 G 的零点，四个方向无平面限制。 -/
theorem stationarity_chart_of_globalMinimum (h : BlochVec) (K : KMatrix)
    (haxis : h 1 = 0) (hK : K.PosSemidef) (hr : K.rank = 1)
    (hk : 0 < RankOneChart.scale K)
    (hreg : kDerivative (1/2) (-1/2) (h, K) K ≠ 0)
    (hmin : IsGlobalMinimum h K) :
    stationarity (RankOneChart.scale K,
      RankOneChart.parameters (h 0) (h 2 / 2) (multiplier h K) (RankOneChart.chart K)) = 0 := by
  let p : Input := (RankOneChart.scale K,
    RankOneChart.parameters (h 0) (h 2 / 2) (multiplier h K) (RankOneChart.chart K))
  have hpH : hamiltonianVector p.2 = h := by
    funext i
    fin_cases i <;> simp [p, ActualSwapSystem.hamiltonianVector, RankOneChart.parameters, haxis]
    ring
  have hpK : kossakowskiMatrix p = K :=
    RankOneChart.actualKossakowski_chart K hK hr hk (h 0) (h 2 / 2) (multiplier h K)
  apply stationarity_zero_of_globalMinimum p hk
  · simpa only [hpH, hpK] using hreg
  · rw [hpH, hpK]
    rfl
  · simpa only [hpH, hpK] using hmin

/-- 原始实际下边界达到点，经完整秩一坐标直接满足七个真实驻点方程。 -/
theorem stationarity_chart_of_lowerBoundary (h : BlochVec) (K : KMatrix)
    (haxis : h 1 = 0) (hK : K.PosSemidef) (hr : K.rank = 1)
    (hk : 0 < RankOneChart.scale K)
    (hreg : kDerivative (1/2) (-1/2) (h, K) K ≠ 0)
    (b : ℝ) (he : canonicalOutput h K 1 = (lowerBoundary b, b)) :
    stationarity (RankOneChart.scale K,
      RankOneChart.parameters (h 0) (h 2 / 2) (multiplier h K) (RankOneChart.chart K)) = 0 :=
  stationarity_chart_of_globalMinimum h K haxis hK hr hk hreg
    (globalMinimum_of_lowerBoundary h K hK b he)

#print axioms stationarity_chart_of_globalMinimum
#print axioms stationarity_chart_of_lowerBoundary
end TwoStateQuantumEmbedding.ActualSwapOptimality

set_option pp.proofs false
#print TwoStateQuantumEmbedding.CanonicalStationarity.hGradient_lagrangian_of_lowerBoundary
#print TwoStateQuantumEmbedding.CanonicalStationarity.canonical_kkt_of_lowerBoundary
#print TwoStateQuantumEmbedding.ActualSwapOptimality.stationarity_chart_of_lowerBoundary
