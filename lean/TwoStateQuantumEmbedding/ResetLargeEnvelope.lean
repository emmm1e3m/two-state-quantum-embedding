import TwoStateQuantumEmbedding.ResetMixedEnvelope

noncomputable section
open Filter Topology Matrix
namespace TwoStateQuantumEmbedding.ResetEnvelope

/-- 大比率衰减比较的统一标量尾部；常数刻意取整数粗界。 -/
theorem large_ratio_scalar_tail (a s L : ℝ) (ha : 1 ≤ a) (ha1 : a ≤ 101 / 100)
    (hsmall : 512 * Real.exp (-L / 2) ≤ 1) :
    max (512 * Real.exp (-L / 2) * Real.exp (-(3 / 5) * s) -
      (1 / 2) * Real.exp (-a * s)) 0 ≤
      (32 * 512 ^ 3 : ℝ) * Real.exp (-(6 / 5) * L) := by
  let θ : ℝ := (3 / 5) / a
  let Q : ℝ := 512 * Real.exp (-L / 2)
  have ha0 : 0 < a := by linarith
  have hθ : 2 / 5 ≤ θ := by
    dsimp [θ]
    apply (le_div_iff₀ ha0).2
    linarith
  have hθ1 : θ ≤ 3 / 4 := by
    dsimp [θ]
    apply (div_le_iff₀ ha0).2
    linarith
  have hθp : 0 < θ := by linarith
  have hθlt : θ < 1 := by linarith
  have hθ7 : 7 / 12 ≤ θ := by
    dsimp [θ]
    apply (le_div_iff₀ ha0).2
    linarith
  have ht : 12 / 5 ≤ 1 / (1 - θ) := by
    apply (le_div_iff₀ (show 0 < 1 - θ by linarith)).2
    linarith
  have hQp : 0 < Q := by dsimp [Q]; positivity
  have hQ1 : Q ≤ 1 := hsmall
  have hk : a / (3 / 5) - 1 = 1 / θ - 1 := by dsimp [θ]; field_simp
  have henv := two_rate_positive_bound (1 / 2) Q a (3 / 5) s
    (by norm_num) hQp (by norm_num) (by linarith)
  rw [hk, scalar_envelope_factor (1 / 2) Q θ (by norm_num) hQp.le hθp hθlt] at henv
  have hpre := mode_prefactor_bounded (1 / 2) θ (by norm_num) (by norm_num) hθ hθ1
  have hpow := Real.rpow_le_rpow_of_exponent_ge hQp hQ1 ht
  have hpower : Q ^ (12 / 5 : ℝ) ≤ (512 : ℝ) ^ 3 * Real.exp (-(6 / 5) * L) := by
    dsimp [Q]
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 512) (Real.exp_nonneg _), ← Real.exp_mul]
    have hc : (512 : ℝ) ^ (12 / 5 : ℝ) ≤ (512 : ℝ) ^ (3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have he : (-L / 2) * (12 / 5) = -(6 / 5) * L := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_right (by simpa using hc) (Real.exp_nonneg _)
  calc
    _ ≤ modePrefactor (1 / 2) θ * Q ^ (1 / (1 - θ)) := henv
    _ ≤ 32 * ((512 : ℝ) ^ 3 * Real.exp (-(6 / 5) * L)) :=
      mul_le_mul hpre.2 (hpow.trans hpower) (by positivity) (by norm_num)
    _ = _ := by ring

def feedbackRatio (x τ : ℝ) : ℝ :=
  coupling x τ / ((rateA x - 3 / 5) * (rateL x τ - 3 / 5))
def initialTransfer (p x τ : ℝ) : ℝ :=
  rateR x τ * tiltW p / (rateL x τ - 3 / 5)
def barrierSize (p x τ : ℝ) : ℝ :=
  (tiltV p + initialTransfer p x τ) / (1 - feedbackRatio x τ)
def largeCoefficient (p x τ : ℝ) : ℝ :=
  tiltV p * (initialTransfer p x τ + feedbackRatio x τ * barrierSize p x τ) +
    tiltW p ^ 2 + tiltW p * rateC x τ * barrierSize p x τ / (rateL x τ - 3 / 5)

theorem large_rate_gaps (x τ : ℝ) (hx : 0 ≤ x) (hxsmall : x ≤ 1 / 1000)
    (hτ : 1 / 2 ≤ τ) :
    2 / 5 ≤ rateA x - 3 / 5 ∧ τ / 4 ≤ rateL x τ - 3 / 5 := by
  constructor
  · unfold rateA
    nlinarith [sq_nonneg x]
  · unfold rateL
    nlinarith [sq_nonneg x]

theorem large_rate_ratios (x τ : ℝ) (hx : 0 ≤ x) (hxsmall : x ≤ 1 / 1000)
    (hτ : 1 / 2 ≤ τ) :
    0 ≤ feedbackRatio x τ ∧ feedbackRatio x τ ≤ 30 * x ∧
      rateC x τ / (rateL x τ - 3 / 5) ≤ 16 ∧
      rateR x τ / (rateL x τ - 3 / 5) ≤ 24 * x := by
  have ht : 0 < τ := by linarith
  have hx1 : x < 1 := by linarith
  have hd := large_rate_gaps x τ hx hxsmall hτ
  have hdA : 0 < rateA x - 3 / 5 := by linarith [hd.1]
  have hdL : 0 < rateL x τ - 3 / 5 := by linarith [hd.2]
  have hden : τ / 10 ≤ (rateA x - 3 / 5) * (rateL x τ - 3 / 5) := by
    have := mul_le_mul hd.1 hd.2 (by positivity : 0 ≤ τ / 4) (by positivity)
    nlinarith
  have hη : feedbackRatio x τ ≤ 30 * x := by
    unfold feedbackRatio
    calc
      _ ≤ (3 * x * τ) / (τ / 10) := div_le_div₀ (by positivity)
        (coupling_small x τ hx (by linarith) ht.le) (by positivity) hden
      _ = _ := by field_simp; ring
  have hs : Real.sqrt τ ≤ 2 * τ := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · nlinarith [mul_nonneg ht.le (show 0 ≤ τ - 1 / 2 by linarith)]
  have hr0 : 0 ≤ rateR x τ := by unfold rateR; positivity
  have hc : rateC x τ ≤ 2 * Real.sqrt τ :=
    (le_add_of_nonneg_left hr0).trans (rates_sum_small x τ hx (by linarith))
  have hr : rateR x τ ≤ 3 * x * Real.sqrt τ := by
    unfold rateR
    apply (div_le_iff₀ (show 0 < 1 - x by linarith)).2
    have := mul_le_mul_of_nonneg_left (show (2 : ℝ) ≤ 3 * (1 - x) by linarith)
      (show 0 ≤ x * Real.sqrt τ by positivity)
    nlinarith
  refine ⟨?_, hη, ?_, ?_⟩
  · unfold feedbackRatio
    exact div_nonneg (coupling_nonneg x τ hx hx1) (by positivity)
  · apply (div_le_iff₀ hdL).2
    nlinarith [hd.2]
  · apply (div_le_iff₀ hdL).2
    have h1 := mul_le_mul_of_nonneg_left hs (show 0 ≤ 3 * x by positivity)
    have h2 := mul_le_mul_of_nonneg_left hd.2 (show 0 ≤ 24 * x by positivity)
    nlinarith

/-- 显式正上解的系数在无界比率上仍为O(√ρ)。 -/
theorem large_coefficient_bound (p x τ ρ : ℝ) (hp : 0 ≤ p) (hpρ : p ≤ ρ)
    (hρ : ρ ≤ 1 / 8) (hx : 0 ≤ x) (hxsmall : x ≤ 1 / 1000)
    (hxρ : x ≤ 2 * Real.sqrt ρ) (hτ : 1 / 2 ≤ τ) :
    largeCoefficient p x τ ≤ 512 * Real.sqrt ρ := by
  have hρ0 : 0 ≤ ρ := hp.trans hpρ
  have hxden : 0 < 1 - x := by linarith
  have hratio := large_rate_ratios x τ hx hxsmall hτ
  have hη0 := hratio.1
  have hη30 := hratio.2.1
  have hηhalf : feedbackRatio x τ ≤ 1 / 2 := by linarith
  have hden : 0 < 1 - feedbackRatio x τ := by linarith
  have hL : 0 < rateL x τ - 3 / 5 := by
    have h := (large_rate_gaps x τ hx hxsmall hτ).2
    linarith
  have hv0 : 0 ≤ tiltV p := by unfold tiltV; linarith
  have hv1 : tiltV p ≤ 1 := by unfold tiltV; linarith
  have hw0 : 0 ≤ tiltW p := by unfold tiltW; positivity
  have hw2 := tiltW_sq_le p hp (by linarith)
  have hw1 : tiltW p ≤ 1 := by nlinarith
  have hwp : tiltW p ≤ 2 * Real.sqrt ρ := by
    unfold tiltW
    have h : p * (1 - p) ≤ ρ := by nlinarith [sq_nonneg p]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h) (by norm_num)
  have hd0 : 0 ≤ initialTransfer p x τ := by
    unfold initialTransfer rateR
    positivity
  have hd24 : initialTransfer p x τ ≤ 24 * x := by
    unfold initialTransfer
    have hm := mul_le_mul_of_nonneg_right hratio.2.2.2 hw0
    have hm2 := mul_le_mul_of_nonneg_left hw1 (show 0 ≤ 24 * x by positivity)
    calc
      _ = rateR x τ / (rateL x τ - 3 / 5) * tiltW p := by ring
      _ ≤ 24 * x * tiltW p := hm
      _ ≤ 24 * x := by simpa using hm2
  have hP0 : 0 ≤ barrierSize p x τ := by unfold barrierSize; positivity
  have hP4 : barrierSize p x τ ≤ 4 := by
    unfold barrierSize
    apply (div_le_iff₀ hden).2
    linarith
  have hfeed : initialTransfer p x τ + feedbackRatio x τ * barrierSize p x τ ≤ 144 * x := by
    have h := mul_le_mul hη30 hP4 hP0 (by positivity : 0 ≤ 30 * x)
    nlinarith
  have hvfeed := mul_le_mul hv1 hfeed (by positivity : 0 ≤ initialTransfer p x τ +
    feedbackRatio x τ * barrierSize p x τ) (by norm_num : (0 : ℝ) ≤ 1)
  have hc0 : 0 ≤ rateC x τ / (rateL x τ - 3 / 5) := by unfold rateC; positivity
  have hcross : tiltW p * rateC x τ * barrierSize p x τ / (rateL x τ - 3 / 5) ≤
      128 * Real.sqrt ρ := by
    calc
      _ = tiltW p * (rateC x τ / (rateL x τ - 3 / 5)) * barrierSize p x τ := by ring
      _ ≤ (2 * Real.sqrt ρ) * 16 * 4 := by gcongr; exact hratio.2.2.1
      _ = _ := by ring
  have hs := Real.sq_sqrt hρ0
  have hs0 := Real.sqrt_nonneg ρ
  have hrhosqrt : ρ ≤ Real.sqrt ρ := by
    have hρ2 : ρ ^ 2 ≤ ρ := by nlinarith [mul_nonneg hρ0 (show 0 ≤ 1 - ρ by linarith)]
    nlinarith
  unfold largeCoefficient
  nlinarith

/-- 大比率标量尾项在同一有限阈值后统一低于任意ηρ/L。 -/
theorem large_ratio_scalar_uniform (η : ℝ) (hη : 0 < η) :
    ∃ L₀ : ℝ, ∀ L a s : ℝ, L₀ ≤ L → 1 ≤ a → a ≤ 101 / 100 →
      L * max (512 * Real.exp (-L / 2) * Real.exp (-(3 / 5) * s) -
        (1 / 2) * Real.exp (-a * s)) 0 ≤ η * Real.exp (-L) := by
  have hsmall : Tendsto (fun L : ℝ => 512 * Real.exp (-L / 2)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0 : ℝ) (1 / 2)
      (by norm_num)).const_mul 512
    convert h using 1 <;> simp only [Real.rpow_zero, one_mul, mul_zero]
    funext L
    congr 2
    ring
  have htail : Tendsto (fun L : ℝ => (32 * 512 ^ 3 : ℝ) * L * Real.exp (-L / 5))
      atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) (1 / 5)
      (by norm_num)).const_mul (32 * 512 ^ 3)
    convert h using 1 <;> simp only [Real.rpow_one, mul_zero]
    funext L
    have he : -(1 / 5 : ℝ) * L = -L / 5 := by ring
    rw [he]
    ring
  obtain ⟨L₁, hL₁⟩ := Filter.eventually_atTop.mp
    (hsmall.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)))
  obtain ⟨L₂, hL₂⟩ := Filter.eventually_atTop.mp
    (htail.eventually (eventually_lt_nhds hη))
  refine ⟨max 1 (max L₁ L₂), ?_⟩
  intro L a s hL ha ha1
  have hL0 : 0 ≤ L := by have := (le_max_left 1 (max L₁ L₂)).trans hL; linarith
  have h1 : L₁ ≤ L := (le_max_left L₁ L₂).trans ((le_max_right 1 (max L₁ L₂)).trans hL)
  have h2 : L₂ ≤ L := (le_max_right L₁ L₂).trans ((le_max_right 1 (max L₁ L₂)).trans hL)
  have hb := mul_le_mul_of_nonneg_left
    (large_ratio_scalar_tail a s L ha ha1 (hL₁ L h1).le) hL0
  have he : Real.exp (-(6 / 5) * L) = Real.exp (-L / 5) * Real.exp (-L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hb
  have hm := mul_le_mul_of_nonneg_right (hL₂ L h2).le (Real.exp_nonneg (-L))
  nlinarith


#print axioms large_ratio_scalar_tail
#print axioms large_rate_ratios
#print axioms large_coefficient_bound
#print axioms large_ratio_scalar_uniform
end TwoStateQuantumEmbedding.ResetEnvelope
