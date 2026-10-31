import TwoStateQuantumEmbedding.ResetMixedEnvelope
import TwoStateQuantumEmbedding.ResetLowRatioTools

noncomputable section
open Filter Topology

namespace TwoStateQuantumEmbedding.ResetEnvelope
open LowRatio
set_option maxHeartbeats 1500000
set_option maxRecDepth 3000

theorem slow_weight_budget_coarse (L p x τ : ℝ) (hL : 0 ≤ L)
    (hp : 0 ≤ p) (hpρ : p ≤ rho L) (hρ : rho L ≤ 1 / 2)
    (hx : 0 ≤ x) (hxρ : x ≤ 2 * root L) (hxsmall : x ≤ 1 / 100)
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1 / 2) : slowWeight p x τ ≤ 68 * root L := by
  have hq := slow_weight_coarse p x τ hp (hpρ.trans hρ) hx hxsmall hτ hτ1
  have hpτ : p * τ ≤ rho L := by nlinarith [mul_le_mul_of_nonneg_left hτ1 hp]
  have hs : Real.sqrt (p * τ) ≤ root L := by
    simpa only [sqrt_rho] using Real.sqrt_le_sqrt hpτ
  have hxτ : x * τ ≤ root L := by
    have h1 := mul_le_mul_of_nonneg_right hxρ hτ
    have h2 := mul_le_mul_of_nonneg_left hτ1 (root_pos L).le
    nlinarith
  linarith [rho_le_root L hL]

/-- 小固定窗口内，真实慢模权重平方及正底限的统一误差。 -/
theorem regularized_weight_square (L p x τ s : ℝ)
    (hL : 0 ≤ L) (hp : 0 ≤ p) (hpρ : p ≤ rho L) (hρ : rho L ≤ 1 / 2)
    (hx : 0 ≤ x) (hxρ : x ≤ 2 * root L) (hxsmall : x ≤ 1 / 100)
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1 / 2) (hs : 0 ≤ s) (hs1 : s ≤ 1) (hτs : τ ≤ s)
    (hrefined : slowWeight p x τ ≤ 4 * p + (1 + s) *
      (4 * Real.sqrt (p * τ) + 8 * x * τ)) :
    (slowWeight p x τ + floor L) ^ 2 / 4 ≤
      4 * p * τ * (1 + s) ^ 2 + rho L * τ * windowError s + rho L * residual L := by
  have hρ0 := (rho_pos L).le
  have hr0 := (root_pos L).le
  have hq0 := slow_weight_nonneg p x τ hp (hpρ.trans hρ) hx (by linarith) hτ1
  have hq := slow_weight_budget_coarse L p x τ hL hp hpρ hρ hx hxρ hxsmall hτ hτ1
  have hb := weight_square_estimate (slowWeight p x τ) p x τ (rho L) (1 + s)
    hq0 hp hpρ hx (by simpa only [sqrt_rho] using hxρ) hτ (by linarith)
    (by linarith) hrefined
  rw [sqrt_rho] at hb
  have hf2 : (1 + s) ^ 2 ≤ 4 := by nlinarith
  have hsqrt := Real.sqrt_le_sqrt hτs
  have h1 : 32 * (1 + s) ^ 2 * rho L * τ * Real.sqrt τ ≤
      128 * rho L * τ * Real.sqrt s := by
    calc
      _ ≤ 32 * 4 * rho L * τ * Real.sqrt s := by gcongr
      _ = _ := by ring
  have h2 : 64 * (1 + s) ^ 2 * rho L * τ ^ 2 ≤ 256 * rho L * τ * s := by
    have ht2 : τ ^ 2 ≤ τ * s := by nlinarith [mul_le_mul_of_nonneg_left hτs hτ]
    calc
      _ ≤ 64 * 4 * rho L * (τ * s) := by gcongr
      _ = _ := by ring
  have h3 : 40 * (1 + s) * rho L * root L ≤ 80 * rho L * root L := by
    have := mul_le_mul_of_nonneg_right (show 40 * (1 + s) ≤ 80 by linarith)
      (mul_nonneg (rho_pos L).le (root_pos L).le)
    nlinarith
  have hr := regularized_square (slowWeight p x τ) L hL hq0 hq
  unfold windowError LowRatio.residual
  nlinarith only [hb, h1, h2, h3, hr]

theorem low_ratio_regularized_uniform (η : ℝ) (hη : 0 < η) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ p x τ : ℝ,
      0 ≤ p → p ≤ Real.exp (-L) →
      0 ≤ x → x ≤ 2 * Real.exp (-L / 2) →
      0 ≤ τ → τ ≤ 1 / 2 →
      L * Reset.scalarEnvelope (1 - 8 * Real.exp (-L))
        (slowWeight p x τ + Real.exp (-3 * L / 4)) (rateA x / beta x τ - 1) ≤
          4 * p / Real.exp 1 + η * Real.exp (-L) := by
  have hev := totalWindowError_continuous.tendsto.eventually
    (eventually_lt_nhds (show totalWindowError 0 < η / 2 by rw [totalWindowError_zero]; linarith))
  obtain ⟨e, he, hnear⟩ := Metric.eventually_nhds_iff.mp hev
  let s : ℝ := min (e / 2) (1 / 2)
  have hs : 0 < s := lt_min (by positivity) (by norm_num)
  have hs1 : s ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hse : s < e := (min_le_left _ _).trans_lt (by linarith)
  have herr : totalWindowError s < η / 2 :=
    hnear (by simpa only [Real.dist_eq, sub_zero, abs_of_pos hs] using hse)
  obtain ⟨dw, hdw, _, hweight⟩ := slow_weight_uniform_refined s hs
  obtain ⟨dp, hdp, hpref⟩ := mode_prefactor_uniform s hs
  let d : ℝ := min s (min (dw / 2) (dp / 2))
  have hd : 0 < d := lt_min hs (lt_min (by positivity) (by positivity))
  have hds : d ≤ s := min_le_left _ _
  have hdw' : d < dw := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hdp' : d < dp := ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by linarith)
  let K : ℝ := 64 * 69 ^ 2 * Real.exp logConstant
  have hK : 0 < K := by dsimp [K]; positivity
  have htail : Tendsto (fun L : ℝ => K * (L * Real.exp (-d * L))) atTop (𝓝 0) := by
    simpa using (linear_exp_decay_limit d hd).const_mul K
  have hres : Tendsto (fun L : ℝ => windowMultiplier s * (L * residual L)) atTop (𝓝 0) := by
    simpa using residual_linear_limit.const_mul (windowMultiplier s)
  have hevent : ∀ᶠ L : ℝ in atTop,
      ∀ p x τ : ℝ, 0 ≤ p → p ≤ rho L → 0 ≤ x → x ≤ 2 * root L →
      0 ≤ τ → τ ≤ 1 / 2 →
      L * Reset.scalarEnvelope (1 - 8 * rho L) (slowWeight p x τ + floor L)
        (rateA x / beta x τ - 1) ≤ 4 * p / Real.exp 1 + η * rho L := by
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      rho_limit.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 / 16 by norm_num)),
      root_limit.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 / 200 by norm_num)),
      root_limit.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 / 69 by norm_num)),
      root_limit.eventually (eventually_lt_nhds (show (0 : ℝ) < dw / 2 by positivity)),
      rho_limit.eventually (eventually_lt_nhds (show (0 : ℝ) < dp / 8 by positivity)),
      root_limit.eventually (eventually_lt_nhds (show (0 : ℝ) < dp / 32 by positivity)),
      correction_limit.eventually (eventually_lt_nhds (show (1 : ℝ) < 1 + s by linarith)),
      hres.eventually (eventually_lt_nhds (show (0 : ℝ) < η / 2 by positivity)),
      htail.eventually (eventually_lt_nhds hη)]
      with L hL hρ16 hr200 hr69 hrw hρp hrp hcorr hresL htailL
    intro p x τ hp hpρ hx hxρ hτ hτ1
    have hρ0 := (rho_pos L).le
    have hr0 := (root_pos L).le
    have hv0 := (quarter_pos L).le
    have hρ : rho L ≤ 1 / 2 := by linarith
    have hxsmall : x ≤ 1 / 100 := by linarith
    have hx1 : x < 1 := by linarith
    have hp2 : p ≤ 1 / 2 := hpρ.trans hρ
    let q : ℝ := slowWeight p x τ
    let Q : ℝ := q + floor L
    let P : ℝ := 1 - 8 * rho L
    let θ : ℝ := beta x τ / rateA x
    have hq0 : 0 ≤ q := slow_weight_nonneg p x τ hp hp2 hx hx1 hτ1
    have hq : q ≤ 68 * root L := slow_weight_budget_coarse L p x τ hL.le
      hp hpρ hρ hx hxρ hxsmall hτ hτ1
    obtain ⟨hQ0, hQ69, hloglo, hloghi⟩ := regularized_bounds q L hL.le hq0 hq
    have hQ1 : Q ≤ 1 := by dsimp [Q]; linarith
    have hP : 1 / 2 ≤ P := by dsimp [P]; linarith
    have hP1 : P ≤ 1 := by dsimp [P]; linarith [rho_pos L]
    have hP0 : 0 < P := by linarith
    have hθbounds := theta_low_ratio x τ hx hxsmall hτ hτ1
    have hθ : 2 / 5 ≤ θ := by dsimp [θ]; linarith
    have hθ1 : θ ≤ 3 / 4 := by dsimp [θ]; linarith
    have hθ0 : 0 < θ := by linarith
    have hθlt : θ < 1 := by linarith
    have hpre := mode_prefactor_bounded P θ hP hP1 hθ hθ1
    have heq : rateA x / beta x τ - 1 = 1 / θ - 1 := by
      dsimp [θ]
      rw [one_div_div]
    have hfactor : Reset.scalarEnvelope P Q (rateA x / beta x τ - 1) =
        modePrefactor P θ * Q ^ (1 / (1 - θ)) := by
      rw [heq]
      exact scalar_envelope_factor P Q θ hP0 hQ0.le hθ0 hθlt
    have hpower := rpow_split_bound Q (1 / (1 - θ)) τ x L logConstant
      hQ0 hQ1 hτ hx (power_exponent_lower θ τ x hx hτ hτ1 hθbounds.1 hθ1)
      hloglo hloghi
    have hC : 0 ≤ logConstant := Real.log_nonneg (by norm_num)
    have hxcorr : Real.exp (128 * x * L) ≤ 1 + s := by
      calc
        _ ≤ Real.exp (256 * root L * L) := by
          apply Real.exp_le_exp.mpr
          nlinarith only [mul_le_mul_of_nonneg_right hxρ hL.le]
        _ ≤ _ := hcorr.le
    by_cases hτd : τ < d
    · have hτs : τ ≤ s := hτd.le.trans hds
      have hsmallpre : modePrefactor P θ ≤ (1 + s) / 4 := by
        apply hpref P θ
        · rw [show P - 1 = -(8 * rho L) by dsimp [P]; ring, abs_neg,
            abs_of_nonneg (by positivity : 0 ≤ 8 * rho L)]
          linarith
        · apply abs_lt.mpr
          constructor <;> dsimp [θ] <;> linarith [hτd.trans hdp']
      have hrefined := hweight p x τ hp hp2 hx (by linarith) hτ (hτd.trans hdw')
      have hsquare : Q ^ 2 / 4 ≤ 4 * p * τ * (1 + s) ^ 2 +
          rho L * τ * windowError s + rho L * residual L :=
        regularized_weight_square L p x τ s hL.le hp hpρ hρ hx hxρ hxsmall
          hτ hτ1 hs.le hs1 hτs hrefined
      have hcorrall : Real.exp (-τ * L + 2 * logConstant * τ + 128 * x * L) ≤
          Real.exp (-τ * L) * Real.exp (2 * logConstant * s) * (1 + s) := by
        rw [Real.exp_add, Real.exp_add]
        gcongr
      have hscalar : Reset.scalarEnvelope P Q (rateA x / beta x τ - 1) ≤
          windowMultiplier s * (Q ^ 2 / 4) * Real.exp (-τ * L) := by
        rw [hfactor]
        calc
          _ ≤ ((1 + s) / 4) * (Q ^ 2 *
              (Real.exp (-τ * L) * Real.exp (2 * logConstant * s) * (1 + s))) := by
            exact mul_le_mul hsmallpre
              (hpower.trans (mul_le_mul_of_nonneg_left hcorrall (sq_nonneg Q)))
              (Real.rpow_nonneg hQ0.le _) (by positivity)
          _ = _ := by unfold windowMultiplier; ring
      have hA : 0 ≤ windowMultiplier s := (by norm_num : (0 : ℝ) ≤ 1).trans
        (windowMultiplier_ge_one s hs.le)
      have hE : 0 ≤ windowError s := by unfold windowError; positivity
      have hR : 0 ≤ residual L := by unfold LowRatio.residual; positivity
      have hpr := profile_bound L τ hL
      have hexp : Real.exp (-τ * L) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      have hpr1 := mul_le_mul_of_nonneg_left hpr
        (show 0 ≤ 4 * p * (1 + s) ^ 2 by positivity)
      have hpr2 := mul_le_mul_of_nonneg_left hpr
        (mul_nonneg (rho_pos L).le hE)
      have hpr3 := mul_le_mul_of_nonneg_left hexp
        (mul_nonneg (rho_pos L).le (mul_nonneg hL.le hR))
      have hprsum := mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add hpr1 hpr2) hpr3) hA
      have hmain : L * Reset.scalarEnvelope P Q (rateA x / beta x τ - 1) ≤
          windowMultiplier s * (4 * p * (1 + s) ^ 2 / Real.exp 1 +
            rho L * windowError s / Real.exp 1 + rho L * (L * residual L)) := by
        calc
          _ ≤ windowMultiplier s * (L * (Q ^ 2 / 4) * Real.exp (-τ * L)) := by
            nlinarith only [mul_le_mul_of_nonneg_left hscalar hL.le]
          _ ≤ windowMultiplier s *
              (L * (4 * p * τ * (1 + s) ^ 2 + rho L * τ * windowError s +
                rho L * residual L) * Real.exp (-τ * L)) := by gcongr
          _ = windowMultiplier s *
              (4 * p * (1 + s) ^ 2 * (L * τ * Real.exp (-τ * L)) +
                rho L * windowError s * (L * τ * Real.exp (-τ * L)) +
                rho L * (L * residual L) * Real.exp (-τ * L)) := by ring
          _ ≤ _ := by simpa only [div_eq_mul_inv, one_div, mul_one, one_mul] using hprsum
      have hlead : 0 ≤ windowMultiplier s * (1 + s) ^ 2 - 1 := by
        have hA1 := windowMultiplier_ge_one s hs.le
        have hs2 : 1 ≤ (1 + s) ^ 2 := by nlinarith
        nlinarith
      have hpbound := mul_le_mul_of_nonneg_left hpρ
        (mul_nonneg hlead (show 0 ≤ 4 / Real.exp 1 by positivity))
      have hresbound := mul_le_mul_of_nonneg_left hresL.le (rho_pos L).le
      have herrbound := mul_le_mul_of_nonneg_left herr.le (rho_pos L).le
      change L * Reset.scalarEnvelope P Q (rateA x / beta x τ - 1) ≤ _
      unfold totalWindowError at herrbound
      calc
        _ ≤ windowMultiplier s * (4 * p * (1 + s) ^ 2 / Real.exp 1 +
            rho L * windowError s / Real.exp 1 + rho L * (L * residual L)) := hmain
        _ = 4 * p / Real.exp 1 +
            ((windowMultiplier s * (1 + s) ^ 2 - 1) * (4 / Real.exp 1)) * p +
            rho L * (windowMultiplier s * windowError s / Real.exp 1) +
            rho L * (windowMultiplier s * (L * residual L)) := by ring
        _ ≤ 4 * p / Real.exp 1 +
            ((windowMultiplier s * (1 + s) ^ 2 - 1) * (4 / Real.exp 1)) * rho L +
            rho L * (windowMultiplier s * windowError s / Real.exp 1) +
            rho L * (windowMultiplier s * (L * residual L)) :=
          add_le_add (add_le_add (add_le_add (le_refl _) hpbound) (le_refl _)) (le_refl _)
        _ = 4 * p / Real.exp 1 +
            (rho L * ((windowMultiplier s * (1 + s) ^ 2 - 1) * (4 / Real.exp 1) +
              windowMultiplier s * windowError s / Real.exp 1) +
            rho L * (windowMultiplier s * (L * residual L))) := by ring
        _ ≤ 4 * p / Real.exp 1 + (rho L * (η / 2) + rho L * (η / 2)) :=
          add_le_add (le_refl (4 * p / Real.exp 1)) (add_le_add herrbound hresbound)
        _ = _ := by ring
    · have hdt : d ≤ τ := le_of_not_gt hτd
      have hQsq : Q ^ 2 ≤ 69 ^ 2 * rho L := by
        have h := sq_le_sq₀ hQ0.le (by positivity : 0 ≤ 69 * root L) |>.mpr hQ69
        simpa only [mul_pow, root_sq] using h
      have he : Real.exp (-τ * L) ≤ Real.exp (-d * L) := by gcongr
      have hcτ : Real.exp (2 * logConstant * τ) ≤ Real.exp logConstant := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hτ1 hC]
      have hcorrall : Real.exp (-τ * L + 2 * logConstant * τ + 128 * x * L) ≤
          Real.exp (-d * L) * Real.exp logConstant * 2 := by
        rw [Real.exp_add, Real.exp_add]
        apply mul_le_mul
        · exact mul_le_mul he hcτ (Real.exp_nonneg _) (Real.exp_nonneg _)
        · linarith [hxcorr]
        · exact Real.exp_nonneg _
        · positivity
      have hscalar : Reset.scalarEnvelope P Q (rateA x / beta x τ - 1) ≤
          K * rho L * Real.exp (-d * L) := by
        rw [hfactor]
        calc
          _ ≤ 32 * (69 ^ 2 * rho L *
              (Real.exp (-d * L) * Real.exp logConstant * 2)) := by
            apply mul_le_mul hpre.2
              (hpower.trans (mul_le_mul hQsq hcorrall (Real.exp_nonneg _) (by positivity)))
              (Real.rpow_nonneg hQ0.le _) (by norm_num)
          _ = _ := by dsimp [K]; ring
      have hmul := mul_le_mul_of_nonneg_left hscalar hL.le
      have ht := mul_le_mul_of_nonneg_left htailL.le (rho_pos L).le
      change L * Reset.scalarEnvelope P Q (rateA x / beta x τ - 1) ≤ _
      calc
        _ ≤ L * (K * rho L * Real.exp (-d * L)) := hmul
        _ = rho L * (K * (L * Real.exp (-d * L))) := by ring
        _ ≤ rho L * η := ht
        _ = η * rho L := mul_comm _ _
        _ ≤ 4 * p / Real.exp 1 + η * rho L := le_add_of_nonneg_left (by positivity)
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp hevent
  refine ⟨L₀, ?_⟩
  intro L hL p x τ hp hpρ hx hxρ hτ hτ1
  exact hL₀ L hL p x τ hp hpρ hx hxρ hτ hτ1

end TwoStateQuantumEmbedding.ResetEnvelope

#print axioms TwoStateQuantumEmbedding.ResetEnvelope.regularized_weight_square
#print axioms TwoStateQuantumEmbedding.ResetEnvelope.low_ratio_regularized_uniform
