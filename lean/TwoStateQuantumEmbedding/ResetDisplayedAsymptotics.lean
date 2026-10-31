import TwoStateQuantumEmbedding.ResetDisplayedFamily

noncomputable section
open Filter Topology
open TwoStateQuantumEmbedding.ResetFamily
open TwoStateQuantumEmbedding.ResetDisplayedFamily

namespace TwoStateQuantumEmbedding.ResetDisplayedAsymptotics

def u (L : ℝ) : ℝ := Real.sqrt (1 - pFamily L)
def d (L : ℝ) : ℝ := 1 - 1 / L
def correction (L : ℝ) : ℝ := Real.exp ((1 - BFamily L) / 2)

theorem radius_sq (L : ℝ) : radius L ^ 2 = pFamily L := by
  simp only [radius, pFamily, pow_two, ← Real.exp_add]
  congr 1
  ring

theorem p_pos (L : ℝ) : 0 < pFamily L := Real.exp_pos _

theorem p_limit : Tendsto pFamily atTop (𝓝 0) := by
  simpa only [radius_sq, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using radius_limit.pow 2

theorem u_limit : Tendsto u atTop (𝓝 1) := by
  change Tendsto (fun L => Real.sqrt (1 - pFamily L)) atTop (𝓝 1)
  simpa only [sub_zero, Real.sqrt_one] using
    ((tendsto_const_nhds (x := (1 : ℝ))).sub p_limit).sqrt

theorem v_limit : Tendsto (fun L => v (pFamily L)) atTop (𝓝 1) := by
  simpa [v] using (p_limit.const_mul 2).const_sub 1

theorem d_limit : Tendsto d atTop (𝓝 1) := by
  change Tendsto (fun L : ℝ => 1 - 1 / L) atTop (𝓝 1)
  simpa only [id_eq, sub_zero] using (tendsto_id.const_div_atTop (1 : ℝ)).const_sub 1

theorem B_limit : Tendsto BFamily atTop (𝓝 1) := by
  have hlog : Tendsto (fun L : ℝ => Real.log L / L) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h := (hlog.add (tendsto_id.const_div_atTop (1 - Real.log 4))).const_add 1
  simp only [add_zero, id_eq] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  unfold BFamily AFamily
  field_simp
  ring

theorem correction_limit : Tendsto correction atTop (𝓝 1) := by
  change Tendsto (fun L => Real.exp ((1 - BFamily L) / 2)) atTop (𝓝 1)
  simpa only [sub_self, zero_div, Real.exp_zero] using
    ((B_limit.const_sub 1).div_const 2).rexp

theorem radius_div_sqrt_limit :
    Tendsto (fun L => radius L / Real.sqrt L) atTop (𝓝 0) :=
  radius_limit.div_atTop Real.tendsto_sqrt_atTop

theorem radius_mul_sqrt_limit :
    Tendsto (fun L => radius L * Real.sqrt L) atTop (𝓝 0) := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2) (1 / 2) (by norm_num)
  simpa [radius, Real.sqrt_eq_rpow, neg_div, div_eq_mul_inv, mul_comm] using h

theorem d_pos (L : ℝ) (hL : 4 < L) : 0 < d L := by
  have hL0 : 0 < L := by linarith
  unfold d
  have h := (div_lt_one hL0).mpr (show 1 < L by linarith)
  linarith

theorem w_exact (L : ℝ) : w (pFamily L) = 2 * radius L * u L := by
  rw [w, Real.sqrt_mul (p_pos L).le, ← radius_sq L,
    Real.sqrt_sq (radius_pos L).le]
  rw [radius_sq]
  unfold u
  ring

theorem slow_exact (L : ℝ) (hL : 0 < L) :
    S (AFamily L) (BFamily L) =
      (2 / Real.exp 1) * (radius L / Real.sqrt L) * correction L := by
  have hsqrt : Real.sqrt L = Real.exp (Real.log L / 2) := by
    rw [Real.exp_half, Real.exp_log hL]
  have htwo : (2 : ℝ) = Real.exp (Real.log 4 / 2) := by
    rw [Real.exp_half, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    norm_num
  have hfactor : 2 / Real.exp 1 = Real.exp (Real.log 4 / 2 - 1) := by
    rw [Real.exp_sub, ← htwo]
  rw [hsqrt, hfactor]
  unfold S radius correction AFamily
  simp only [div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
  congr 1
  ring

theorem cross_exact (L : ℝ) (hL : 4 < L) :
    K (AFamily L) (BFamily L) =
      2 / (Real.sqrt L * d L) * (S (AFamily L) (BFamily L) - F (AFamily L)) := by
  have hL0 : 0 < L := by linarith
  have hA := (displayed_parameters L hL).2.1
  have hsqrt : Real.sqrt (AFamily L * BFamily L) = AFamily L / Real.sqrt L := by
    rw [show AFamily L * BFamily L = AFamily L ^ 2 / L by unfold BFamily; ring,
      Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hA.le]
  have hden : AFamily L - (AFamily L + BFamily L) / 2 = AFamily L * d L / 2 := by
    unfold BFamily d
    ring
  unfold K
  rw [hsqrt, hden]
  field_simp [hA.ne', (d_pos L hL).ne', (Real.sqrt_pos.mpr hL0).ne']

theorem fast_limit : Tendsto (fun L => F (AFamily L)) atTop (𝓝 0) := by
  have h := (p_limit.div_atTop tendsto_id).const_mul (4 / Real.exp 1)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  rw [displayed_fast_exact L hL]
  simp only [id_eq]
  ring

theorem slow_limit : Tendsto (fun L => S (AFamily L) (BFamily L)) atTop (𝓝 0) := by
  have h := (radius_div_sqrt_limit.const_mul (2 / Real.exp 1)).mul correction_limit
  simp only [mul_zero, zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  exact (slow_exact L hL).symm

theorem cross_limit : Tendsto (fun L => K (AFamily L) (BFamily L)) atTop (𝓝 0) := by
  have h := ((Real.tendsto_sqrt_atTop.const_div_atTop (2 : ℝ)).div d_limit one_ne_zero).mul
    (slow_limit.sub fast_limit)
  simp only [zero_div, sub_self, zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (4 : ℝ)] with L hL
  rw [cross_exact L hL]
  simp only [Pi.div_apply]
  ring

theorem w_limit : Tendsto (fun L => w (pFamily L)) atTop (𝓝 0) := by
  simpa only [w_exact, mul_zero, zero_mul] using (radius_limit.const_mul 2).mul u_limit

theorem error_ratio_algebra (r u v f s k : ℝ) (hr : r ≠ 0) :
    (r ^ 2 + v * r ^ 2 * f - (2 * r * u) ^ 2 / 2 * s -
      r ^ 2 * (2 * r * u) * k) / r ^ 2 =
    1 + v * f - 2 * u ^ 2 * s - (2 * r * u) * k := by
  field_simp

theorem error_ratio_exact (L : ℝ) :
    displayedError L / pFamily L =
      1 + v (pFamily L) * F (AFamily L) -
        2 * u L ^ 2 * S (AFamily L) (BFamily L) -
        w (pFamily L) * K (AFamily L) (BFamily L) := by
  simpa only [radius_sq, ← w_exact, displayedError, actualError] using
    error_ratio_algebra (radius L) (u L) (v (pFamily L)) (F (AFamily L))
      (S (AFamily L) (BFamily L)) (K (AFamily L) (BFamily L)) (radius_pos L).ne'

theorem error_ratio_limit :
    Tendsto (fun L => displayedError L / pFamily L) atTop (𝓝 1) := by
  have h := (((v_limit.mul fast_limit).const_add 1).sub
    (((u_limit.pow 2).mul slow_limit).const_mul 2)).sub (w_limit.mul cross_limit)
  simp only [mul_zero, add_zero, sub_zero] at h
  apply h.congr'
  filter_upwards [] with L
  rw [error_ratio_exact]
  ring

/-- 将真实 q 归一化后的唯一有理代数步骤。 -/
theorem q_ratio_algebra (r s u v d h c : ℝ) (hr : r ≠ 0) (hs : s ≠ 0) (hd : d ≠ 0) :
    s ^ 2 / r ^ 2 *
      (v ^ 2 * (c * r ^ 2 / s ^ 2) + (2 * r * u) ^ 2 * (c / 2 * (r / s) * h) -
        v * (2 * r * u) * (2 / (s * d) * (c / 2 * (r / s) * h - c * r ^ 2 / s ^ 2))) =
    c * (v ^ 2 + 2 * u ^ 2 * (r * s) * h - 2 * v * u * h / d +
      4 * v * u * (r / s) / d) := by
  field_simp
  ring

theorem q_ratio_exact (L : ℝ) (hL : 4 < L) :
    L / pFamily L * displayedDeterminant L =
      (4 / Real.exp 1) *
        (v (pFamily L) ^ 2 + 2 * u L ^ 2 * (radius L * Real.sqrt L) * correction L -
          2 * v (pFamily L) * u L * correction L / d L +
          4 * v (pFamily L) * u L * (radius L / Real.sqrt L) / d L) := by
  have hL0 : 0 < L := by linarith
  have hf : F (AFamily L) = (4 / Real.exp 1) * pFamily L / L := by
    rw [displayed_fast_exact L hL0]
    ring
  have hs : S (AFamily L) (BFamily L) =
      (4 / Real.exp 1) / 2 * (radius L / Real.sqrt L) * correction L := by
    rw [slow_exact L hL0]
    ring
  unfold displayedDeterminant determinant
  simp only [cross_exact L hL, hf, hs, w_exact]
  simpa only [radius_sq, Real.sq_sqrt hL0.le] using
    q_ratio_algebra (radius L) (Real.sqrt L) (u L) (v (pFamily L)) (d L)
      (correction L) (4 / Real.exp 1) (radius_pos L).ne'
      (Real.sqrt_pos.mpr hL0).ne' (d_pos L hL).ne'

theorem q_ratio_limit :
    Tendsto (fun L => L / pFamily L * displayedDeterminant L) atTop
      (𝓝 (-(4 / Real.exp 1))) := by
  have hc := (((u_limit.pow 2).mul radius_mul_sqrt_limit).mul correction_limit).const_mul 2
  have hn := (((v_limit.mul u_limit).mul correction_limit).const_mul 2).div d_limit one_ne_zero
  have hf := (((v_limit.mul u_limit).mul radius_div_sqrt_limit).const_mul 4).div d_limit one_ne_zero
  have h := ((((v_limit.pow 2).add hc).sub hn).add hf).const_mul (4 / Real.exp 1)
  have h' : Tendsto (fun L => (4 / Real.exp 1) *
      (v (pFamily L) ^ 2 + 2 * u L ^ 2 * (radius L * Real.sqrt L) * correction L -
        2 * v (pFamily L) * u L * correction L / d L +
        4 * v (pFamily L) * u L * (radius L / Real.sqrt L) / d L)) atTop
      (𝓝 (-(4 / Real.exp 1))) := by
    convert h using 1
    · funext L
      simp only [Pi.div_apply]
      ring
    · norm_num <;> ring
  apply h'.congr'
  filter_upwards [eventually_gt_atTop (4 : ℝ)] with L hL
  exact (q_ratio_exact L hL).symm

theorem error_eventually_pos : ∀ᶠ L : ℝ in atTop, 0 < displayedError L := by
  have h := error_ratio_limit.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [h] with L hL
  exact (div_pos_iff_of_pos_right (p_pos L)).mp hL

theorem error_limit : Tendsto displayedError atTop (𝓝 0) := by
  have h := error_ratio_limit.mul p_limit
  simp only [one_mul] at h
  apply h.congr'
  exact Filter.Eventually.of_forall (fun L => div_mul_cancel₀ _ (p_pos L).ne')

def logScale (L : ℝ) : ℝ := Real.log (1 / displayedError L)
def scaledActualGain (L : ℝ) : ℝ := logScale L / displayedError L * (-displayedDeterminant L)

theorem log_identity (L : ℝ) (he : 0 < displayedError L) :
    logScale L = L - Real.log (displayedError L / pFamily L) := by
  unfold logScale
  rw [Real.log_div he.ne' (p_pos L).ne', pFamily, Real.log_exp,
    one_div, Real.log_inv]
  ring

theorem log_difference_limit : Tendsto (fun L => logScale L - L) atTop (𝓝 0) := by
  have h := (error_ratio_limit.log one_ne_zero).neg
  simp only [Real.log_one, neg_zero] at h
  apply h.congr'
  filter_upwards [error_eventually_pos] with L he
  rw [log_identity L he]
  ring

theorem log_ratio_limit : Tendsto (fun L => logScale L / L) atTop (𝓝 1) := by
  have h := (log_difference_limit.div_atTop tendsto_id).const_add 1
  simp only [add_zero, id_eq] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  field_simp
  ring

theorem scaled_gain_limit : Tendsto scaledActualGain atTop (𝓝 (4 / Real.exp 1)) := by
  have h := ((q_ratio_limit.neg).div error_ratio_limit one_ne_zero).mul log_ratio_limit
  simp only [neg_neg, div_one, mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ), error_eventually_pos] with L hL he
  unfold scaledActualGain
  simp only [Pi.div_apply]
  field_simp [(p_pos L).ne', hL.ne', he.ne']

/-- 将同一个显示族的任意已证明尾段性质保留到逐实际误差见证。 -/
theorem cover_with_eventual (P : ℝ → Prop) (hP : ∀ᶠ L : ℝ in atTop, P L) :
    ∃ ε₀ > 0, ∀ ε ∈ Set.Ioo 0 ε₀, ∃ L : ℝ,
      4 < L ∧ displayedError L = ε ∧ P L := by
  have ht : ∀ᶠ L : ℝ in atTop, 4 < L ∧ 0 < displayedError L ∧ P L :=
    (eventually_gt_atTop (4 : ℝ)).and (error_eventually_pos.and hP)
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp ht
  refine ⟨displayedError L₀, (hL₀ L₀ le_rfl).2.1, ?_⟩
  intro ε hε
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.mp
    (error_limit.eventually (eventually_lt_nhds hε.1))
  let M := max L₀ L₁
  have hm : L₀ ≤ M := le_max_left _ _
  have hεM : displayedError M < ε := hL₁ M (le_max_right _ _)
  have hc : ContinuousOn displayedError (Set.Icc L₀ M) := by
    intro x hx
    exact (displayed_error_continuousAt x (hL₀ x hx.1).1).continuousWithinAt
  obtain ⟨L, hLint, he⟩ := intermediate_value_Icc' hm hc ⟨hεM.le, hε.2.le⟩
  exact ⟨L, (hL₀ L hLint.1).1, he, (hL₀ L hLint.1).2.2⟩

/-- 论文显示的同一有限单跳跃族，在每个充分小实际 ε 达到任意精度的 4/e 匹配。 -/
theorem displayed_finite_matching (η : ℝ) (hη : 0 < η) :
    ∃ ε₀ > 0, ∀ ε ∈ Set.Ioo 0 ε₀, ∃ (L a : ℝ),
      4 < L ∧ displayedError L = ε ∧
      finiteOutput 0 (displayedJumps L) 1 = (a, 1 - ε) ∧
      (a, 1 - ε) ∈ finiteOutputs ∧
      |Real.log (1 / ε) / ε * (ε - a) - 4 / Real.exp 1| < η := by
  have hclose : ∀ᶠ L : ℝ in atTop, |scaledActualGain L - 4 / Real.exp 1| < η := by
    simpa only [Metric.mem_ball, Real.dist_eq] using
      scaled_gain_limit.eventually (Metric.ball_mem_nhds (4 / Real.exp 1) hη)
  obtain ⟨ε₀, hε₀, hc⟩ := cover_with_eventual _ hclose
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε
  obtain ⟨L, hL, he, hgain⟩ := hc ε hε
  have hout : finiteOutput 0 (displayedJumps L) 1 =
      (ε + displayedDeterminant L, 1 - ε) := by
    rw [displayed_output_exact L hL, he]
  refine ⟨L, ε + displayedDeterminant L, hL, he, hout,
    ⟨1, 0, displayedJumps L, 1, by simp, by norm_num, hout⟩, ?_⟩
  simpa only [scaledActualGain, logScale, he, sub_add_eq_sub_sub, sub_self, zero_sub] using hgain

/-- 极限直接以原始有限输出的两个概率表述。 -/
theorem finiteOutput_scaled_gain_limit :
    Tendsto (fun L =>
      let z := finiteOutput 0 (displayedJumps L) 1
      Real.log (1 / (1 - z.2)) / (1 - z.2) * ((1 - z.2) - z.1))
      atTop (𝓝 (4 / Real.exp 1)) := by
  apply scaled_gain_limit.congr'
  filter_upwards [eventually_gt_atTop (4 : ℝ)] with L hL
  dsimp only
  rw [displayed_output_exact L hL]
  simp only [sub_sub_cancel, sub_add_eq_sub_sub, sub_self, zero_sub, scaledActualGain, logScale]

end TwoStateQuantumEmbedding.ResetDisplayedAsymptotics

#print axioms TwoStateQuantumEmbedding.ResetDisplayedAsymptotics.slow_exact
#print axioms TwoStateQuantumEmbedding.ResetDisplayedAsymptotics.cross_exact
#print axioms TwoStateQuantumEmbedding.ResetDisplayedAsymptotics.B_limit
#print axioms TwoStateQuantumEmbedding.ResetDisplayedAsymptotics.error_ratio_limit
#print axioms TwoStateQuantumEmbedding.ResetDisplayedAsymptotics.q_ratio_limit
#print axioms TwoStateQuantumEmbedding.ResetDisplayedAsymptotics.log_difference_limit
#print axioms TwoStateQuantumEmbedding.ResetDisplayedAsymptotics.scaled_gain_limit
#print axioms TwoStateQuantumEmbedding.ResetDisplayedAsymptotics.cover_with_eventual
#print axioms TwoStateQuantumEmbedding.ResetDisplayedAsymptotics.displayed_finite_matching
#print axioms TwoStateQuantumEmbedding.ResetDisplayedAsymptotics.finiteOutput_scaled_gain_limit
#check TwoStateQuantumEmbedding.ResetDisplayedAsymptotics.error_ratio_limit
#check TwoStateQuantumEmbedding.ResetDisplayedAsymptotics.q_ratio_limit
#check TwoStateQuantumEmbedding.ResetDisplayedAsymptotics.displayed_finite_matching
#check TwoStateQuantumEmbedding.ResetDisplayedAsymptotics.finiteOutput_scaled_gain_limit
