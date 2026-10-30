import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Tactic

open Filter Set
open scoped Topology ContDiff

namespace QuantumEmbedding.AnalyticFoundation

variable {X Y Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]

/-- 解析隐函数由方程和可逆偏导构造；唯一性覆盖邻域中的全部解。 -/
theorem analytic_implicit_branch
    {G : X × Y → Z} {u : X × Y}
    (ha : AnalyticAt ℝ G u)
    (hi : (fderiv ℝ G u ∘L ContinuousLinearMap.inr ℝ X Y).IsInvertible) :
    ∃ ψ : X → Y,
      AnalyticAt ℝ ψ u.1 ∧ ψ u.1 = u.2 ∧
      (∀ᶠ x in 𝓝 u.1, G (x, ψ x) = G u) ∧
      (∀ᶠ v in 𝓝 u, G v = G u ↔ ψ v.1 = v.2) := by
  have hc : ContDiffAt ℝ ω G u := ha.contDiffAt
  have hn : (ω : ℕ∞ω) ≠ 0 := by simp
  refine ⟨hc.implicitFunction hn hi,
    (hc.contDiffAt_implicitFunction hn hi).analyticAt,
    hc.implicitFunction_apply_self hn hi,
    hc.eventually_apply_implicitFunction hn hi,
    hc.eventually_apply_eq_iff_implicitFunction hn hi⟩

omit [CompleteSpace Y] in
/-- 一维解析函数在零点处可除以参数，零点值由导数给出。 -/
theorem analytic_division_one_variable
    {f : ℝ → Y} (ha : AnalyticAt ℝ f 0) (hzero : f 0 = 0) :
    ∃ q : ℝ → Y,
      AnalyticAt ℝ q 0 ∧ q 0 = deriv f 0 ∧
      (∀ k, k • q k = f k) ∧
      (∀ k, k ≠ 0 → q k = k⁻¹ • f k) := by
  refine ⟨dslope f 0, ?_, dslope_same f 0, ?_, ?_⟩
  · obtain ⟨p, hp⟩ := ha
    exact hp.has_fpower_series_dslope_fslope.analyticAt
  · intro k
    simpa using sub_smul_dslope_of_zero hzero k
  · intro k hk
    simp [dslope_of_ne f hk, slope, hzero]

/-- 非零导数产生解析局部逆以及两侧逆恒等式。 -/
theorem analytic_local_reparameterization
    {b : ℝ → ℝ} {k₀ : ℝ}
    (ha : AnalyticAt ℝ b k₀) (hd : deriv b k₀ ≠ 0) :
    ∃ κ : ℝ → ℝ,
      AnalyticAt ℝ κ (b k₀) ∧ κ (b k₀) = k₀ ∧
      (∀ᶠ k in 𝓝 k₀, κ (b k) = k) ∧
      (∀ᶠ t in 𝓝 (b k₀), b (κ t) = t) := by
  let κ := ha.hasStrictDerivAt.localInverse b (deriv b k₀) k₀ hd
  have hl : ∀ᶠ k in 𝓝 k₀, κ (b k) = k :=
    ha.hasStrictDerivAt.eventually_left_inverse hd
  exact ⟨κ, ha.analyticAt_localInverse hd, hl.self_of_nhds,
    hl, ha.hasStrictDerivAt.eventually_right_inverse hd⟩

/-- 固定开邻域中的全部零点恰为同一解析图像，不预设候选解解析。 -/
theorem analytic_implicit_open_neighborhoods
    {G : X × Y → Z} {x₀ : X} {y₀ : Y}
    (ha : AnalyticAt ℝ G (x₀, y₀)) (hzero : G (x₀, y₀) = 0)
    (hi : (fderiv ℝ G (x₀, y₀) ∘L ContinuousLinearMap.inr ℝ X Y).IsInvertible) :
    ∃ (ψ : X → Y) (U : Set X) (V : Set Y),
      IsOpen U ∧ x₀ ∈ U ∧ IsOpen V ∧ y₀ ∈ V ∧
      ψ x₀ = y₀ ∧ AnalyticOnNhd ℝ ψ U ∧ MapsTo ψ U V ∧
      (∀ x ∈ U, G (x, ψ x) = 0) ∧
      (∀ x ∈ U, ∀ y ∈ V, G (x, y) = 0 ↔ ψ x = y) := by
  obtain ⟨ψ, hψ, hbase, hsol, huniq⟩ := analytic_implicit_branch ha hi
  have huniq' : {v : X × Y | G v = 0 ↔ ψ v.1 = v.2} ∈ 𝓝 (x₀, y₀) := by
    simpa [hzero, Filter.eventually_iff] using huniq
  obtain ⟨U, V, hUo, hxU, hVo, hyV, hUV⟩ := mem_nhds_prod_iff'.mp huniq'
  have hm : ∀ᶠ x in 𝓝 x₀, ψ x ∈ V := by
    exact hψ.continuousAt.eventually (by simpa [hbase] using hVo.mem_nhds hyV)
  have hall : ∀ᶠ x in 𝓝 x₀, x ∈ U ∧ AnalyticAt ℝ ψ x ∧ ψ x ∈ V :=
    (Filter.eventually_mem_set.mpr (hUo.mem_nhds hxU)).and (hψ.eventually_analyticAt.and hm)
  obtain ⟨U', hU', hU'o, hxU'⟩ := eventually_nhds_iff.mp hall
  refine ⟨ψ, U', V, hU'o, hxU', hVo, hyV, hbase,
    (fun x hx => (hU' x hx).2.1), (fun x hx => (hU' x hx).2.2), ?_, ?_⟩
  · intro x hx
    exact (hUV ⟨(hU' x hx).1, (hU' x hx).2.2⟩).mpr rfl
  · intro x hx y hy
    exact hUV ⟨(hU' x hx).1, hy⟩

omit [CompleteSpace X] in
/-- 对解析复合函数，内层方向导数的参数因子传给外层；商联合解析。 -/
theorem analytic_directional_factor
    {Q C : ℝ × X → Y} {φ : Y → Z} {x₀ : X} {v : ℝ × X}
    (hQ : AnalyticAt ℝ Q (0, x₀)) (hC : AnalyticAt ℝ C (0, x₀))
    (hφ : AnalyticAt ℝ φ (Q (0, x₀)))
    (hfactor : ∀ᶠ p in 𝓝 (0, x₀), fderiv ℝ Q p v = p.1 • C p) :
    ∃ q : ℝ × X → Z,
      AnalyticAt ℝ q (0, x₀) ∧
      q (0, x₀) = fderiv ℝ φ (Q (0, x₀)) (C (0, x₀)) ∧
      (∀ᶠ p in 𝓝 (0, x₀),
        p.1 • q p = fderiv ℝ (φ ∘ Q) p v ∧
        (p.1 ≠ 0 → q p = p.1⁻¹ • fderiv ℝ (φ ∘ Q) p v)) := by
  let q : ℝ × X → Z := fun p => fderiv ℝ φ (Q p) (C p)
  have hD : AnalyticAt ℝ (fun p => fderiv ℝ φ (Q p)) (0, x₀) :=
    hφ.fderiv.comp hQ
  have hq : AnalyticAt ℝ q (0, x₀) :=
    ((hD.contDiffAt : ContDiffAt ℝ ω _ _).clm_apply hC.contDiffAt).analyticAt
  refine ⟨q, hq, rfl, ?_⟩
  filter_upwards [hQ.eventually_analyticAt,
    hQ.continuousAt.eventually hφ.eventually_analyticAt, hfactor] with p hQp hφp hfac
  have heq : fderiv ℝ (φ ∘ Q) p v = p.1 • q p := by
    rw [fderiv_comp p hφp.differentiableAt hQp.differentiableAt,
      ContinuousLinearMap.comp_apply, hfac, map_smul]
  constructor
  · exact heq.symm
  · intro hp
    rw [heq, inv_smul_smul₀ hp]

omit [CompleteSpace Y] in
/-- 解析曲线可通过导数非零的解析观测量重新参数化。 -/
theorem analytic_curve_reparameterization
    {ψ : ℝ → Y} {b : ℝ → ℝ} {k₀ : ℝ}
    (hψ : AnalyticAt ℝ ψ k₀) (hb : AnalyticAt ℝ b k₀)
    (hd : deriv b k₀ ≠ 0) :
    ∃ κ : ℝ → ℝ,
      AnalyticAt ℝ κ (b k₀) ∧ κ (b k₀) = k₀ ∧
      AnalyticAt ℝ (ψ ∘ κ) (b k₀) ∧
      (ψ ∘ κ) (b k₀) = ψ k₀ ∧
      (∀ᶠ k in 𝓝 k₀, (ψ ∘ κ) (b k) = ψ k) ∧
      (∀ᶠ t in 𝓝 (b k₀), b (κ t) = t) := by
  obtain ⟨κ, hκ, hbase, hleft, hright⟩ := analytic_local_reparameterization hb hd
  have han : AnalyticAt ℝ (ψ ∘ κ) (b k₀) := by
    apply AnalyticAt.comp
    · simpa [hbase] using hψ
    · exact hκ
  refine ⟨κ, hκ, hbase, han, by simp [hbase], ?_, hright⟩
  exact hleft.mono fun k hk => by simp [hk]

omit [CompleteSpace X] in
/-- 内层生成元对参数仿射时，方向导数之商的联合解析性由链式法则直接得到。 -/
theorem analytic_affine_parameter_directional_factor
    {A R : X → Y} {φ : Y → Z} {x₀ v : X}
    (hA : AnalyticAt ℝ A x₀) (hR : AnalyticAt ℝ R x₀)
    (hφ : AnalyticAt ℝ φ (A x₀))
    (hAzero : ∀ᶠ x in 𝓝 x₀, fderiv ℝ A x v = 0) :
    ∃ q : ℝ × X → Z,
      AnalyticAt ℝ q (0, x₀) ∧
      (∀ᶠ p in 𝓝 (0, x₀),
        p.1 • q p =
          fderiv ℝ (fun r : ℝ × X => φ (A r.2 + r.1 • R r.2)) p (0, v) ∧
        (p.1 ≠ 0 → q p = p.1⁻¹ •
          fderiv ℝ (fun r : ℝ × X => φ (A r.2 + r.1 • R r.2)) p (0, v))) := by
  let Q : ℝ × X → Y := fun p => A p.2 + p.1 • R p.2
  let C : ℝ × X → Y := fun p => fderiv ℝ R p.2 v
  have hsnd : AnalyticAt ℝ (fun p : ℝ × X => p.2) (0, x₀) := (ContinuousLinearMap.snd ℝ ℝ X).analyticAt _
  have hfst : AnalyticAt ℝ (fun p : ℝ × X => p.1) (0, x₀) := (ContinuousLinearMap.fst ℝ ℝ X).analyticAt _
  have hQ : AnalyticAt ℝ Q (0, x₀) := (hA.comp hsnd).add (hfst.smul (hR.comp hsnd))
  have hC : AnalyticAt ℝ C (0, x₀) :=
    ((((hR.fderiv.comp hsnd).contDiffAt : ContDiffAt ℝ ω _ _).clm_apply
      contDiffAt_const)).analyticAt
  have hfac : ∀ᶠ p in 𝓝 (0, x₀), fderiv ℝ Q p (0, v) = p.1 • C p := by
    have hm := hsnd.continuousAt.eventually
      (hA.eventually_analyticAt.and (hR.eventually_analyticAt.and hAzero))
    filter_upwards [hm] with p hp
    have hAp := hp.1.differentiableAt.hasFDerivAt.comp p hasFDerivAt_snd
    have hRp := hp.2.1.differentiableAt.hasFDerivAt.comp p hasFDerivAt_snd
    have hfull := hAp.add (hasFDerivAt_fst.smul hRp)
    rw [show fderiv ℝ Q p = _ from hfull.fderiv]
    simp [C, hp.2.2]
  obtain ⟨q, hq, _, hqeq⟩ := analytic_directional_factor hQ hC
    (by simpa [Q] using hφ) hfac
  exact ⟨q, hq, hqeq⟩

omit [CompleteSpace Y] in
/-- 已得到解析因子后，其零点值恰等于原函数的小参数导数。 -/
theorem analytic_factor_value_eq_deriv
    {f q : ℝ → Y} (hq : AnalyticAt ℝ q 0)
    (hfactor : ∀ᶠ k in 𝓝 0, f k = k • q k) :
    deriv f 0 = q 0 := by
  have hd : HasDerivAt (fun k : ℝ => k • q k) (q 0) 0 := by
    have hfun : ((id : ℝ → ℝ) • q : ℝ → Y) = (fun k : ℝ => k • q k) := by
      ext k
      rfl
    rw [← hfun]
    simpa using (hasDerivAt_id (0 : ℝ)).smul hq.differentiableAt.hasDerivAt
  exact (Filter.EventuallyEq.deriv_eq hfactor).trans hd.deriv

#print axioms analytic_factor_value_eq_deriv
#print axioms analytic_affine_parameter_directional_factor
#print axioms analytic_implicit_open_neighborhoods
#print axioms analytic_directional_factor
#print axioms analytic_curve_reparameterization
#print axioms analytic_implicit_branch
#print axioms analytic_division_one_variable
#print axioms analytic_local_reparameterization

end QuantumEmbedding.AnalyticFoundation








