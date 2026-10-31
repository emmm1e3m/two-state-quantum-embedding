import TwoStateQuantumEmbedding.ResetDiagonalFamily
import TwoStateQuantumEmbedding.ResetDiagonalScalar

noncomputable section
open Matrix Complex Filter Topology
open scoped Matrix.Norms.Operator
open TwoStateQuantumEmbedding.ResetDiagonalEnvelope

namespace TwoStateQuantumEmbedding.ResetDiagonalFamily

/-- 最优时间使用实际快衰减率换元。 -/
def shapeTime (χ τ : ℝ) : ℝ := optimalTime (shapeBeta χ τ) (shapeD χ τ) / shapeFast χ τ
def shapeGain (χ τ : ℝ) : ℝ := scalarD0 (shapeBeta χ τ) (shapeD χ τ)
def shapeEpsilon (χ τ : ℝ) : ℝ := occupation χ * (1 + shapeGain χ τ)

theorem shape_optimal_output (χ τ : ℝ) (hχ : χ ≠ 1) (hτ : 0 ≤ τ)
    (hdisc : 0 < shapeDiscriminant χ τ) (hs : 0 < shapeSlow χ τ)
    (hd : 0 < shapeD χ τ) :
    0 < shapeTime χ τ ∧ 0 < shapeGain χ τ ∧
    finiteOutput (hamiltonian (kappa (Real.sqrt τ) 1 χ)) (jumps (Real.sqrt τ) 1 χ)
      (shapeTime χ τ) = (shapeEpsilon χ τ - shapeGain χ τ, 1 - shapeEpsilon χ τ) := by
  obtain ⟨hgap, hgp, htrace, hdet⟩ := shape_spectrum χ τ hdisc
  have hsf : shapeSlow χ τ < shapeFast χ τ := by linarith
  have hf : 0 < shapeFast χ τ := lt_trans hs hsf
  have hb0 : 0 < shapeBeta χ τ := div_pos hs hf
  have hb1 : shapeBeta χ τ < 1 := (div_lt_one hf).2 hsf
  have hopt := scalarD0_exponential_attains (shapeBeta χ τ) (shapeD χ τ) hb0 hb1 hd
  have htfast : -shapeFast χ τ * shapeTime χ τ = -optimalTime (shapeBeta χ τ) (shapeD χ τ) := by
    unfold shapeTime
    field_simp
  have htslow : -shapeSlow χ τ * shapeTime χ τ =
      -shapeBeta χ τ * optimalTime (shapeBeta χ τ) (shapeD χ τ) := by
    unfold shapeTime shapeBeta
    ring
  have hq : (1 + shapeD χ τ) * Real.exp (-shapeFast χ τ * shapeTime χ τ) -
      shapeD χ τ * Real.exp (-shapeSlow χ τ * shapeTime χ τ) = -shapeGain χ τ := by
    rw [htfast, htslow]
    unfold shapeGain
    linarith
  refine ⟨div_pos (optimalTime_pos _ _ hb0 hb1 hd) hf,
    scalarD0_pos _ _ hb0 hb1 hd, ?_⟩
  rw [shape_finiteOutput χ τ (shapeTime χ τ) hχ hτ hdisc, hq]
  ext <;> dsimp [shapeEpsilon] <;> ring

/-- 论文所写的有限最优时间与标量优化器一致。 -/
theorem optimal_time_log_formula (f s d : ℝ) (hs : 0 < s) (hsf : s < f) (hd : 0 < d) :
    optimalTime (s / f) d / f = Real.log ((1 + d) * f / (d * s)) / (f - s) := by
  have hf : 0 < f := lt_trans hs hsf
  have hb : 0 < s / f := div_pos hs hf
  have hb1 : s / f < 1 := (div_lt_one hf).2 hsf
  have hbn : 1 - s / f ≠ 0 := by linarith
  have hfs : f - s ≠ 0 := by linarith
  have hi : (1 + d) * f / (d * s) = (d * (s / f) / (1 + d))⁻¹ := by
    field_simp
    <;> ring
  rw [hi, Real.log_inv]
  unfold optimalTime
  field_simp
  <;> ring

/-- 标量最优增益的精确分解；指数修正保持实际谱。 -/
theorem scalarD0_factorized (β d : ℝ) (hβ : 0 < β) (hβ1 : β < 1) (hd : 0 < d) :
    scalarD0 β d = (1 - β) * d ^ 2 * (β / (1 + d)) ^ (β / (1 - β)) *
      Real.exp ((1 / (1 - β) - 2) * Real.log d) := by
  have hbn : 1 - β ≠ 0 := by linarith
  have hbase : 0 < β / (1 + d) := by positivity
  have hexp : Real.exp ((1 / (1 - β) - 2) * Real.log d) =
      d ^ (β / (1 - β) - 1) := by
    rw [Real.rpow_def_of_pos hd]
    congr 1
    field_simp
    <;> ring
  have hpow : d ^ 2 * d ^ (β / (1 - β) - 1) = d * d ^ (β / (1 - β)) := by
    rw [← Real.rpow_two, ← Real.rpow_add hd]
    rw [show (2 : ℝ) + (β / (1 - β) - 1) = 1 + β / (1 - β) by ring,
      Real.rpow_add hd, Real.rpow_one]
  unfold scalarD0
  rw [show d * β / (1 + d) = d * (β / (1 + d)) by ring,
    Real.mul_rpow hd.le hbase.le, hexp]
  calc
    _ = (1 - β) * (d * d ^ (β / (1 - β))) * (β / (1 + d)) ^ (β / (1 - β)) := by ring
    _ = _ := by rw [← hpow]; ring

/-- 真实谱的幂指数等于快衰减率除以谱差。 -/
theorem shape_exponent_exact (χ τ : ℝ) (hdisc : 0 < shapeDiscriminant χ τ)
    (hf : 0 < shapeFast χ τ) :
    1 / (1 - shapeBeta χ τ) = shapeFast χ τ / shapeGap χ τ := by
  obtain ⟨hg, hgp, _, _⟩ := shape_spectrum χ τ hdisc
  have hf0 := ne_of_gt hf
  have hg0 := ne_of_gt hgp
  have hb0 : 1 - shapeSlow χ τ / shapeFast χ τ ≠ 0 := by
    apply ne_of_gt
    have hs : shapeSlow χ τ < shapeFast χ τ := by linarith
    exact sub_pos.mpr ((div_lt_one hf).2 hs)
  unfold shapeBeta
  field_simp
  rw [hg, div_self hg0]

def curveTime (L : ℝ) : ℝ := shapeTime (curveChi L) (curveTau L)
def curveGain (L : ℝ) : ℝ := shapeGain (curveChi L) (curveTau L)
def curveEpsilon (L : ℝ) : ℝ := curveNu L * (1 + curveGain L)

theorem curve_actual_output : ∀ᶠ L : ℝ in atTop,
    0 < curveTime L ∧ 0 < curveGain L ∧
    finiteOutput (hamiltonian (kappa (Real.sqrt (curveTau L)) 1 (curveChi L)))
      (jumps (Real.sqrt (curveTau L)) 1 (curveChi L)) (curveTime L) =
      (curveEpsilon L - curveGain L, 1 - curveEpsilon L) := by
  filter_upwards [curve_parameters_eventually, curve_spectral_tail] with L hp hs
  have h := shape_optimal_output (curveChi L) (curveTau L) (ne_of_lt hp.2.2.2.1)
    hp.2.2.2.2.2.le hs.1 hs.2.1 hs.2.2.2.1
  simpa only [shapeEpsilon, hp.2.2.2.2.1, curveTime, curveGain, curveEpsilon] using h

theorem curve_chi_square_ratio_limit :
    Tendsto (fun L => curveChi L ^ 2 / curveNu L) atTop (𝓝 1) := by
  have hOne : Tendsto (fun L => 1 - curveNu L) atTop (𝓝 1) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub curveNu_limit
  have hbase : Tendsto (fun L => 1 / (1 - curveNu L)) atTop (𝓝 1) := by
    convert (tendsto_const_nhds (x := (1 : ℝ))).div hOne (by norm_num) using 1 <;> norm_num <;> rfl
  apply hbase.congr'
  filter_upwards [curve_parameters_eventually] with L hp
  have hv : 0 < 1 - curveNu L := by linarith [hp.2.1]
  dsimp [curveChi, chi]
  rw [Real.sq_sqrt (div_nonneg hp.1.le hv.le)]
  field_simp [hp.1.ne']

/-- 真实显式族在实际谱下达到 64/e² 的 ν 归一化增益。 -/
theorem curve_gain_scaled_limit :
    Tendsto (fun L => curveGain L * L ^ 2 / curveNu L) atTop (𝓝 (64 / Real.exp 1 ^ 2)) := by
  obtain ⟨ha, hl, hp, hd, hg, hf, hs, hc, hb, hfac⟩ :=
    shape_limits curveChi curveTau curveChi_limit curveTau_limit
  have hbase : Tendsto (fun L => shapeBeta (curveChi L) (curveTau L) /
      (1 + shapeD (curveChi L) (curveTau L))) atTop (𝓝 (1 / 2)) := by
    convert hb.div ((tendsto_const_nhds (x := (1 : ℝ))).add hc) (by norm_num) using 1 <;> norm_num <;> rfl
  have hpow : Tendsto (fun L => shapeBeta (curveChi L) (curveTau L) /
      (1 - shapeBeta (curveChi L) (curveTau L))) atTop (𝓝 1) := by
    convert hb.div ((tendsto_const_nhds (x := (1 : ℝ))).sub hb) (by norm_num) using 1 <;> norm_num <;> rfl
  have hterm : Tendsto (fun L => (shapeBeta (curveChi L) (curveTau L) /
      (1 + shapeD (curveChi L) (curveTau L))) ^
        (shapeBeta (curveChi L) (curveTau L) / (1 - shapeBeta (curveChi L) (curveTau L))))
      atTop (𝓝 (1 / 2)) := by
    simpa only [Real.rpow_one] using hbase.rpow hpow (Or.inl (by norm_num))
  have hconst : 64 * Real.exp (-2) = 64 / Real.exp 1 ^ 2 := by
    rw [Real.exp_neg, Real.exp_one_pow]
    ring
  have hlim : Tendsto (fun L => (1 - shapeBeta (curveChi L) (curveTau L)) *
      dFactor (curveChi L) (curveTau L) ^ 2 * (curveChi L ^ 2 / curveNu L) * 4 *
      (shapeBeta (curveChi L) (curveTau L) / (1 + shapeD (curveChi L) (curveTau L))) ^
        (shapeBeta (curveChi L) (curveTau L) / (1 - shapeBeta (curveChi L) (curveTau L))) *
      Real.exp ((shapeFast (curveChi L) (curveTau L) / shapeGap (curveChi L) (curveTau L) - 2) *
        Real.log (shapeD (curveChi L) (curveTau L)))) atTop (𝓝 (64 / Real.exp 1 ^ 2)) := by
    rw [← hconst]
    convert ((((((tendsto_const_nhds (x := (1 : ℝ))).sub hb).mul (hfac.pow 2)).mul
      curve_chi_square_ratio_limit).mul_const 4).mul hterm).mul curve_power_correction_limit using 1 <;> norm_num
  apply hlim.congr'
  filter_upwards [curve_parameters_eventually, curve_spectral_tail, eventually_gt_atTop (0 : ℝ)]
    with L hp hs hL
  have hgp := (shape_spectrum _ _ hs.1).2.1
  have hfast : 0 < shapeFast (curveChi L) (curveTau L) := lt_trans hs.2.1 hs.2.2.1
  have hscale : shapeD (curveChi L) (curveTau L) ^ 2 * L ^ 2 / curveNu L =
      dFactor (curveChi L) (curveTau L) ^ 2 * (curveChi L ^ 2 / curveNu L) * 4 := by
    rw [shapeD_factor _ _ (ne_of_lt hp.2.2.2.1) (ne_of_gt hgp)
      (ne_of_gt hs.2.2.2.2.2.2.2) hs.1.le]
    dsimp [curveTau]
    field_simp
    <;> ring
  symm
  unfold curveGain shapeGain
  rw [scalarD0_factorized _ _ hs.2.2.2.2.1 hs.2.2.2.2.2.1 hs.2.2.2.1,
    shape_exponent_exact _ _ hs.1 hfast]
  calc
    _ = (1 - shapeBeta (curveChi L) (curveTau L)) *
      (shapeD (curveChi L) (curveTau L) ^ 2 * L ^ 2 / curveNu L) *
      (shapeBeta (curveChi L) (curveTau L) / (1 + shapeD (curveChi L) (curveTau L))) ^
        (shapeBeta (curveChi L) (curveTau L) / (1 - shapeBeta (curveChi L) (curveTau L))) *
      Real.exp ((shapeFast (curveChi L) (curveTau L) / shapeGap (curveChi L) (curveTau L) - 2) *
        Real.log (shapeD (curveChi L) (curveTau L))) := by ring
    _ = _ := by rw [hscale]; ring

theorem curveGain_limit : Tendsto curveGain atTop (𝓝 0) := by
  obtain ⟨ha, hl, hp, hd, hg, hf, hs, hc, hb, hfac⟩ :=
    shape_limits curveChi curveTau curveChi_limit curveTau_limit
  have hbase : Tendsto (fun L => shapeD (curveChi L) (curveTau L) *
      shapeBeta (curveChi L) (curveTau L) / (1 + shapeD (curveChi L) (curveTau L))) atTop (𝓝 0) := by
    convert (hc.mul hb).div ((tendsto_const_nhds (x := (1 : ℝ))).add hc)
      (by norm_num) using 1 <;> norm_num <;> rfl
  have he : Tendsto (fun L => shapeBeta (curveChi L) (curveTau L) /
      (1 - shapeBeta (curveChi L) (curveTau L))) atTop (𝓝 1) := by
    convert hb.div ((tendsto_const_nhds (x := (1 : ℝ))).sub hb)
      (by norm_num) using 1 <;> norm_num <;> rfl
  have hr := hbase.rpow he (Or.inr (by norm_num))
  convert (((tendsto_const_nhds (x := (1 : ℝ))).sub hb).mul hc).mul hr using 1 <;>
    norm_num [curveGain, shapeGain, scalarD0] <;> rfl

theorem curveEpsilon_limit : Tendsto curveEpsilon atTop (𝓝 0) := by
  convert curveNu_limit.mul ((tendsto_const_nhds (x := (1 : ℝ))).add curveGain_limit) using 1 <;>
    norm_num [curveEpsilon] <;> rfl

theorem curveEpsilon_scaled_limit :
    Tendsto (fun L => curveEpsilon L / curveNu L) atTop (𝓝 1) := by
  have hbase : Tendsto (fun L => 1 + curveGain L) atTop (𝓝 1) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add curveGain_limit
  apply hbase.congr'
  filter_upwards with L
  unfold curveEpsilon
  field_simp [ne_of_gt (curveNu_pos L)]

theorem curveEpsilon_eventually_pos : ∀ᶠ L : ℝ in atTop, 0 < curveEpsilon L := by
  filter_upwards [curve_actual_output] with L hL
  exact mul_pos (curveNu_pos L) (by linarith [hL.2.1])

theorem curve_log_scale_limit :
    Tendsto (fun L => Real.log (1 / curveEpsilon L) / L) atTop (𝓝 1) := by
  have hOne : Tendsto (fun L => 1 + curveGain L) atTop (𝓝 1) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add curveGain_limit
  have hlog : Tendsto (fun L => Real.log (1 + curveGain L)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.log_one] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hOne
  have hbase : Tendsto (fun L => 1 - Real.log (1 + curveGain L) / L) atTop (𝓝 1) := by
    simpa only [sub_zero, id_eq] using (hlog.div_atTop tendsto_id).const_sub 1
  apply hbase.congr'
  filter_upwards [curve_actual_output, eventually_gt_atTop (0 : ℝ)] with L hout hL
  have hgain : 0 < 1 + curveGain L := by linarith [hout.2.1]
  rw [one_div, Real.log_inv, curveEpsilon,
    Real.log_mul (curveNu_pos L).ne' hgain.ne']
  simp only [curveNu, Real.log_exp]
  field_simp
  <;> ring

/-- 使用真正读出误差 ε 的有限构造渐近，不把 ν 当作 ε。 -/
theorem actual_curve_gain_limit : Tendsto (fun L =>
    Real.log (1 / curveEpsilon L) ^ 2 / curveEpsilon L * curveGain L)
    atTop (𝓝 (64 / Real.exp 1 ^ 2)) := by
  have hbase : Tendsto (fun L => (curveGain L * L ^ 2 / curveNu L) /
      (curveEpsilon L / curveNu L) * (Real.log (1 / curveEpsilon L) / L) ^ 2)
      atTop (𝓝 (64 / Real.exp 1 ^ 2)) := by
    convert (curve_gain_scaled_limit.div curveEpsilon_scaled_limit (by norm_num)).mul
      (curve_log_scale_limit.pow 2) using 1 <;> norm_num <;> rfl
  apply hbase.congr'
  filter_upwards [curveEpsilon_eventually_pos, eventually_gt_atTop (0 : ℝ)] with L he hL
  have hv := (curveNu_pos L).ne'
  field_simp
  <;> ring

/-- 正则尾段上，实际误差随参数连续。 -/
theorem curveEpsilon_continuousAt (L : ℝ) (hL : 0 < L)
    (hν : curveNu L < 1) (hχ : curveChi L < 1)
    (hdisc : 0 < shapeDiscriminant (curveChi L) (curveTau L))
    (hs : 0 < shapeSlow (curveChi L) (curveTau L))
    (hd : 0 < shapeD (curveChi L) (curveTau L)) : ContinuousAt curveEpsilon L := by
  have hχn : 1 - curveChi L ≠ 0 := by linarith
  have hνn : 1 - Real.exp (-L) ≠ 0 := by change 1 - curveNu L ≠ 0; linarith
  have hχc : ContinuousAt curveChi L := by
    unfold curveChi chi curveNu
    fun_prop (disch := assumption)
  have hτc : ContinuousAt curveTau L := by
    unfold curveTau
    fun_prop (disch := exact ne_of_gt hL)
  have ha : ContinuousAt (fun x => shapeAlpha (curveChi x)) L := by
    unfold shapeAlpha
    fun_prop
  have hl : ContinuousAt (fun x => shapeDamping (curveChi x) (curveTau x)) L := by
    unfold shapeDamping
    fun_prop
  have hp : ContinuousAt (fun x => shapeProduct (curveChi x) (curveTau x)) L := by
    unfold shapeProduct
    fun_prop (disch := exact pow_ne_zero _ hχn)
  have hg : ContinuousAt (fun x => shapeGap (curveChi x) (curveTau x)) L := by
    unfold shapeGap shapeDiscriminant
    fun_prop
  have hf : ContinuousAt (fun x => shapeFast (curveChi x) (curveTau x)) L := by
    unfold shapeFast
    fun_prop
  have hsl : ContinuousAt (fun x => shapeSlow (curveChi x) (curveTau x)) L := by
    unfold shapeSlow
    fun_prop
  obtain ⟨hgap, hgp, _, _⟩ := shape_spectrum _ _ hdisc
  have hsf : shapeSlow (curveChi L) (curveTau L) < shapeFast (curveChi L) (curveTau L) := by linarith
  have hfast : 0 < shapeFast (curveChi L) (curveTau L) := lt_trans hs hsf
  have hdc : ContinuousAt (fun x => shapeD (curveChi x) (curveTau x)) L := by
    exact (ha.sub hf).div hg (ne_of_gt hgp)
  have hbc : ContinuousAt (fun x => shapeBeta (curveChi x) (curveTau x)) L := by
    exact hsl.div hf (ne_of_gt hfast)
  have hb0 : 0 < shapeBeta (curveChi L) (curveTau L) := div_pos hs hfast
  have hb1 : shapeBeta (curveChi L) (curveTau L) < 1 := (div_lt_one hfast).2 hsf
  have hbase : 0 < shapeD (curveChi L) (curveTau L) * shapeBeta (curveChi L) (curveTau L) /
      (1 + shapeD (curveChi L) (curveTau L)) := by positivity
  have hdn : 1 + shapeD (curveChi L) (curveTau L) ≠ 0 := by positivity
  have hbn : 1 - shapeBeta (curveChi L) (curveTau L) ≠ 0 := by linarith
  have hbcBase := (hdc.mul hbc).div (continuousAt_const.add hdc) hdn
  have hec := hbc.div (continuousAt_const.sub hbc) hbn
  have hpc := hbcBase.rpow hec (Or.inl (ne_of_gt hbase))
  have hgc : ContinuousAt curveGain L := by
    unfold curveGain shapeGain scalarD0
    exact ((continuousAt_const.sub hbc).mul hdc).mul hpc
  unfold curveEpsilon curveNu
  fun_prop

/-- 任意已证尾段性质都可随实际误差的连续反像一起保留。 -/
theorem cover_actual_errors_with_eventual (P : ℝ → Prop) (hP : ∀ᶠ L : ℝ in atTop, P L) :
    ∃ ε₀ > 0, ∀ ε ∈ Set.Ioo 0 ε₀, ∃ L : ℝ, curveEpsilon L = ε ∧ P L := by
  have ht : ∀ᶠ L : ℝ in atTop,
      0 < L ∧ curveNu L < 1 ∧ curveChi L < 1 ∧
      0 < shapeDiscriminant (curveChi L) (curveTau L) ∧
      0 < shapeSlow (curveChi L) (curveTau L) ∧
      0 < shapeD (curveChi L) (curveTau L) ∧ 0 < curveEpsilon L ∧ P L := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), curve_parameters_eventually,
      curve_spectral_tail, curveEpsilon_eventually_pos, hP] with L hL hp hs he hP
    exact ⟨hL, lt_trans hp.2.1 (by norm_num), hp.2.2.2.1,
      hs.1, hs.2.1, hs.2.2.2.1, he, hP⟩
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp ht
  have he0 : 0 < curveEpsilon L₀ := (hL₀ L₀ le_rfl).2.2.2.2.2.2.1
  refine ⟨curveEpsilon L₀, he0, ?_⟩
  intro ε hε
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.mp
    (curveEpsilon_limit.eventually (eventually_lt_nhds hε.1))
  let M := max L₀ L₁
  have hm : L₀ ≤ M := le_max_left _ _
  have heM : curveEpsilon M < ε := hL₁ M (le_max_right _ _)
  have hc : ContinuousOn curveEpsilon (Set.Icc L₀ M) := by
    intro x hx
    obtain ⟨hxp, hxν, hxχ, hxd, hxs, hxc, _, _⟩ := hL₀ x hx.1
    exact (curveEpsilon_continuousAt x hxp hxν hxχ hxd hxs hxc).continuousWithinAt
  obtain ⟨L, hLint, hLe⟩ := intermediate_value_Icc' hm hc ⟨heM.le, hε.2.le⟩
  exact ⟨L, hLe, (hL₀ L hLint.1).2.2.2.2.2.2.2⟩

/-- 每个充分小的实际 ε 都有同一显式族的有限正时间见证。 -/
theorem every_small_actual_error (η : ℝ) (hη : 0 < η) :
    ∃ ε₀ > 0, ∀ ε ∈ Set.Ioo 0 ε₀, ∃ L : ℝ,
      0 < curveTime L ∧ 0 < curveNu L ∧ curveNu L < 1 ∧
      gkslAction (hamiltonian (kappa (Real.sqrt (curveTau L)) 1 (curveChi L)))
        (jumps (Real.sqrt (curveTau L)) 1 (curveChi L)) (diagonalState (curveNu L)) = 0 ∧
      finiteOutput (hamiltonian (kappa (Real.sqrt (curveTau L)) 1 (curveChi L)))
        (jumps (Real.sqrt (curveTau L)) 1 (curveChi L)) (curveTime L) =
          (ε - curveGain L, 1 - ε) ∧
      |Real.log (1 / ε) ^ 2 / ε * curveGain L - 64 / Real.exp 1 ^ 2| < η := by
  have hb : ∀ᶠ L : ℝ in atTop,
      |Real.log (1 / curveEpsilon L) ^ 2 / curveEpsilon L * curveGain L -
        64 / Real.exp 1 ^ 2| < η := by
    simpa only [Metric.mem_ball, Real.dist_eq] using
      actual_curve_gain_limit.eventually (Metric.ball_mem_nhds _ hη)
  have hp := curve_parameters_eventually.and (curve_actual_output.and hb)
  obtain ⟨ε₀, hε₀, hcover⟩ := cover_actual_errors_with_eventual _ hp
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε
  obtain ⟨L, he, hpar, hout, hb⟩ := hcover ε hε
  have hstat := family_stationary (Real.sqrt (curveTau L)) 1 (curveChi L)
    (ne_of_lt hpar.2.2.2.1)
  simp only [mul_one, hpar.2.2.2.2.1] at hstat
  refine ⟨L, hout.1, hpar.1, lt_trans hpar.2.1 (by norm_num), hstat, ?_, ?_⟩
  · simpa only [he] using hout.2.2
  · simpa only [he] using hb

/-- 完整下界见证：固定实际 ε、单跳、单位时间、真实对角稳态及尖锐系数。 -/
theorem every_small_actual_error_unit (η : ℝ) (hη : 0 < η) :
    ∃ ε₀ > 0, ∀ ε ∈ Set.Ioo 0 ε₀,
      ∃ (H : QubitMatrix) (J : Fin 1 → QubitMatrix) (ν a : ℝ),
        H.IsHermitian ∧ ν ∈ Set.Ioo 0 1 ∧ gkslAction H J (diagonalState ν) = 0 ∧
        finiteOutput H J 1 = (a, 1 - ε) ∧
        |Real.log (1 / ε) ^ 2 / ε * (ε - a) - 64 / Real.exp 1 ^ 2| < η := by
  obtain ⟨ε₀, hε₀, h⟩ := every_small_actual_error η hη
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε
  obtain ⟨L, ht, hν0, hν1, hstat, hout, hb⟩ := h ε hε
  let H := hamiltonian (kappa (Real.sqrt (curveTau L)) 1 (curveChi L))
  let J := jumps (Real.sqrt (curveTau L)) 1 (curveChi L)
  refine ⟨curveTime L • H, (fun μ => Real.sqrt (curveTime L) • J μ),
    curveNu L, ε - curveGain L, ?_, ⟨hν0, hν1⟩, ?_, ?_, ?_⟩
  · simp only [H, Matrix.IsHermitian, Matrix.conjTranspose_smul, star_trivial,
      (hamiltonian_hermitian _).eq]
  · rw [gkslAction_time_scaling H J _ (curveTime L) ht.le, hstat, smul_zero]
  · rw [finiteOutput_time_normalization H J (curveTime L) ht.le]
    exact hout
  · simpa only [sub_sub_cancel] using hb

#print axioms shape_optimal_output
#print axioms optimal_time_log_formula
#print axioms curve_gain_scaled_limit
#print axioms actual_curve_gain_limit
#print axioms cover_actual_errors_with_eventual
#print axioms every_small_actual_error_unit
end TwoStateQuantumEmbedding.ResetDiagonalFamily


