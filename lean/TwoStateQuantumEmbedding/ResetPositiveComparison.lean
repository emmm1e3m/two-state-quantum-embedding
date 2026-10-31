import TwoStateQuantumEmbedding.PureDynamics
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic

noncomputable section
open Set Filter Matrix Complex
open scoped Topology Matrix.Norms.Operator

namespace TwoStateQuantumEmbedding.ResetComparison
set_option backward.isDefEq.respectTransparency false

/-- 有限个光滑障碍的严格边界指向条件蕴含正向不变性。 -/
theorem finite_fence {ι : Type*} [Finite ι] (f f' : ι → ℝ → ℝ)
    {a b : ℝ} (hd : ∀ i t, t ∈ Icc a b → HasDerivAt (f i) (f' i t) t)
    (h0 : ∀ i, f i a ≤ 0)
    (hb : ∀ t ∈ Ico a b, (∀ i, f i t ≤ 0) → ∀ i, f i t = 0 → f' i t < 0) :
    ∀ t ∈ Icc a b, ∀ i, f i t ≤ 0 := by
  let s : Set ℝ := {t | ∀ i, f i t ≤ 0}
  have hc : IsClosed (s ∩ Icc a b) := by
    have hc' : ContinuousOn (fun t i => f i t) (Icc a b) :=
      continuousOn_pi.mpr (fun i t ht => (hd i t ht).continuousAt.continuousWithinAt)
    have htgt : IsClosed {y : ι → ℝ | ∀ i, y i ≤ 0} := by
      have heq : {y : ι → ℝ | ∀ i, y i ≤ 0} = ⋂ i, {y | y i ≤ 0} := by ext y; simp
      rw [heq]
      exact isClosed_iInter (fun i => isClosed_le (continuous_apply i) continuous_const)
    simpa only [s, inter_comm, Set.preimage_setOf_eq] using
      hc'.preimage_isClosed_of_isClosed isClosed_Icc htgt
  apply hc.Icc_subset_of_forall_exists_gt h0
  intro x hx y hy
  have hi (i : ι) : ∀ᶠ z in 𝓝[>] x, f i z ≤ 0 := by
    have hdx := hd i x (Ico_subset_Icc_self hx.2)
    rcases (hx.1 i).lt_or_eq with hlt | heq
    · exact ((hdx.continuousAt.eventually (gt_mem_nhds hlt)).filter_mono nhdsWithin_le_nhds).mono
        (fun z hz => hz.le)
    · have hneg := hb x hx.2 hx.1 i heq
      have hslope : ∀ᶠ z in 𝓝[>] x, slope (f i) x z < 0 :=
        (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl x)).1
          hdx.hasDerivWithinAt.Ioi_of_Ici (Iio_mem_nhds hneg)
      filter_upwards [hslope, self_mem_nhdsWithin] with z hz hzx
      rw [slope_def_field, heq, sub_zero] at hz
      have hlt := (div_lt_iff₀ (sub_pos.mpr hzx)).mp hz
      simpa using hlt.le
  have hi' : ∀ᶠ z in 𝓝[>] x, ∀ i, f i z ≤ 0 := Filter.eventually_all.mpr hi
  exact (hi'.and (Ioc_mem_nhdsGT hy)).exists

def comparisonMatrix (α r c lam : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-α, r; c, -lam]

def comparisonFlow (α r c lam v w t : ℝ) : Fin 2 → ℝ :=
  NormedSpace.exp (t • comparisonMatrix α r c lam) *ᵥ ![v, w]

def vectorEvaluation (v : Fin 2 → ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] (Fin 2 → ℝ) :=
  (show Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] (Fin 2 → ℝ) from
    { toFun := fun M => M *ᵥ v
      map_add' := by intros; exact Matrix.add_mulVec _ _ _
      map_smul' := by intros; exact Matrix.smul_mulVec _ _ _ }).toContinuousLinearMap

theorem comparisonFlow_hasDerivAt (α r c lam v w t : ℝ) :
    HasDerivAt (comparisonFlow α r c lam v w)
      (comparisonMatrix α r c lam *ᵥ comparisonFlow α r c lam v w t) t := by
  have h := (vectorEvaluation ![v,w]).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const' (comparisonMatrix α r c lam) t)
  change HasDerivAt (fun s => NormedSpace.exp (s • comparisonMatrix α r c lam) *ᵥ ![v,w])
    ((comparisonMatrix α r c lam * NormedSpace.exp (t • comparisonMatrix α r c lam)) *ᵥ ![v,w]) t at h
  unfold comparisonFlow
  rw [Matrix.mulVec_mulVec]
  exact h

theorem comparisonFlow_zero (α r c lam v w : ℝ) :
    comparisonFlow α r c lam v w 0 = ![v,w] := by
  simp [comparisonFlow, NormedSpace.exp_zero]

theorem comparisonFlow_deriv_zero (α r c lam v w t : ℝ) :
    HasDerivAt (fun s => comparisonFlow α r c lam v w s 0)
      (-α * comparisonFlow α r c lam v w t 0 +
        r * comparisonFlow α r c lam v w t 1) t := by
  simpa [comparisonMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using
    hasDerivAt_pi.mp (comparisonFlow_hasDerivAt α r c lam v w t) 0

theorem comparisonFlow_deriv_one (α r c lam v w t : ℝ) :
    HasDerivAt (fun s => comparisonFlow α r c lam v w s 1)
      (c * comparisonFlow α r c lam v w t 0 -
        lam * comparisonFlow α r c lam v w t 1) t := by
  simpa [comparisonMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, sub_eq_add_neg] using
    hasDerivAt_pi.mp (comparisonFlow_hasDerivAt α r c lam v w t) 1

/-- 严格上解使用统一指数扰动，不除以任何物理速率。 -/
def fenceRate (α r c lam : ℝ) : ℝ := |α| + |lam| + r + c + 1

theorem fenceRate_bounds (α r c lam : ℝ) (hr : 0 ≤ r) (hc : 0 ≤ c) :
    0 < fenceRate α r c lam + α - r ∧ 0 < fenceRate α r c lam + lam - c := by
  constructor <;> dsimp [fenceRate] <;>
    linarith [neg_abs_le α, neg_abs_le lam, abs_nonneg α, abs_nonneg lam]

theorem positive_system_nonneg (α r c lam : ℝ) (hr : 0 ≤ r) (hc : 0 ≤ c)
    (X Z : ℝ → ℝ)
    (hX : ∀ t, HasDerivAt X (-α * X t + r * Z t) t)
    (hZ : ∀ t, HasDerivAt Z (c * X t - lam * Z t) t)
    (hX0 : 0 ≤ X 0) (hZ0 : 0 ≤ Z 0) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ X t ∧ 0 ≤ Z t := by
  let L := fenceRate α r c lam
  have hL := fenceRate_bounds α r c lam hr hc
  have hbump (ε s : ℝ) : HasDerivAt (fun x : ℝ => ε * Real.exp (L * x))
      (L * (ε * Real.exp (L * s))) s := by
    convert (((hasDerivAt_id s).const_mul L).exp).const_mul ε using 1 <;> simp only [id_eq, mul_one] <;> ring
  have hp (ε : ℝ) (hε : 0 < ε) :
      0 ≤ X t + ε * Real.exp (L * t) ∧ 0 ≤ Z t + ε * Real.exp (L * t) := by
    let f : Fin 2 → ℝ → ℝ := ![fun s => -(X s + ε * Real.exp (L * s)),
      fun s => -(Z s + ε * Real.exp (L * s))]
    let f' : Fin 2 → ℝ → ℝ :=
      ![fun s => -(-α * X s + r * Z s + L * (ε * Real.exp (L * s))),
        fun s => -(c * X s - lam * Z s + L * (ε * Real.exp (L * s)))]
    have hd : ∀ i s, HasDerivAt (f i) (f' i s) s := by
      intro i s; fin_cases i
      · exact ((hX s).add (hbump ε s)).neg
      · exact ((hZ s).add (hbump ε s)).neg
    have hinit : ∀ i, f i 0 ≤ 0 := by
      intro i; fin_cases i <;> simp [f] <;> linarith
    have hb : ∀ s ∈ Ico (0 : ℝ) t, (∀ i, f i s ≤ 0) →
        ∀ i, f i s = 0 → f' i s < 0 := by
      intro s hs hfs i heq
      have hpos : 0 < ε * Real.exp (L * s) := mul_pos hε (Real.exp_pos _)
      have hx := hfs 0
      have hz := hfs 1
      dsimp [f] at hx hz
      fin_cases i
      · dsimp [f, f'] at heq ⊢
        have hp := mul_pos hL.1 hpos
        have hh := mul_nonneg hr (show 0 ≤ Z s + ε * Real.exp (L * s) by linarith)
        change 0 < (L + α - r) * (ε * Real.exp (L * s)) at hp
        have hxx : X s = -(ε * Real.exp (L * s)) := by linarith
        rw [hxx]
        nlinarith only [hp, hh]
      · dsimp [f, f'] at heq ⊢
        have hp := mul_pos hL.2 hpos
        have hh := mul_nonneg hc (show 0 ≤ X s + ε * Real.exp (L * s) by linarith)
        change 0 < (L + lam - c) * (ε * Real.exp (L * s)) at hp
        have hzz : Z s = -(ε * Real.exp (L * s)) := by linarith
        rw [hzz]
        nlinarith only [hp, hh]
    have h := finite_fence f f' (fun i s _ => hd i s) hinit hb t ⟨ht, le_rfl⟩
    exact ⟨neg_nonpos.mp (h 0), neg_nonpos.mp (h 1)⟩
  constructor
  · have hcont : ContinuousWithinAt (fun ε : ℝ => X t + ε * Real.exp (L * t)) (Ioi 0) 0 := by fun_prop
    have h := continuousWithinAt_const.closure_le (by simp : (0 : ℝ) ∈ closure (Ioi 0))
      hcont (fun ε hε => (hp ε hε).1)
    simpa using h
  · have hcont : ContinuousWithinAt (fun ε : ℝ => Z t + ε * Real.exp (L * t)) (Ioi 0) 0 := by fun_prop
    have h := continuousWithinAt_const.closure_le (by simp : (0 : ℝ) ∈ closure (Ioi 0))
      hcont (fun ε hε => (hp ε hε).2)
    simpa using h

/-- 只微分平方模长，故允许原模长在零点不可微。 -/
theorem squared_comparison (α r c lam : ℝ) (hr : 0 ≤ r) (hc : 0 ≤ c)
    (a b da db X Z : ℝ → ℝ)
    (ha : ∀ s, 0 ≤ a s) (hb : ∀ s, 0 ≤ b s)
    (hda : ∀ s, 0 ≤ s → HasDerivAt (fun x => a x ^ 2) (da s) s)
    (hdb : ∀ s, 0 ≤ s → HasDerivAt (fun x => b x ^ 2) (db s) s)
    (hda_le : ∀ s, 0 ≤ s → da s ≤ -2 * α * a s ^ 2 + 2 * r * a s * b s)
    (hdb_le : ∀ s, 0 ≤ s → db s ≤ 2 * c * a s * b s - 2 * lam * b s ^ 2)
    (hX : ∀ s, HasDerivAt X (-α * X s + r * Z s) s)
    (hZ : ∀ s, HasDerivAt Z (c * X s - lam * Z s) s)
    (ha0 : a 0 ≤ X 0) (hb0 : b 0 ≤ Z 0) {t : ℝ} (ht : 0 ≤ t) :
    a t ≤ X t ∧ b t ≤ Z t := by
  let L := fenceRate α r c lam
  have hL := fenceRate_bounds α r c lam hr hc
  have hXZ (s : ℝ) (hs : 0 ≤ s) :=
    positive_system_nonneg α r c lam hr hc X Z hX hZ ((ha 0).trans ha0) ((hb 0).trans hb0) hs
  have hbump (ε s : ℝ) : HasDerivAt (fun x : ℝ => ε * Real.exp (L * x))
      (L * (ε * Real.exp (L * s))) s := by
    convert (((hasDerivAt_id s).const_mul L).exp).const_mul ε using 1 <;> simp only [id_eq, mul_one] <;> ring
  have hp (ε : ℝ) (hε : 0 < ε) :
      a t ≤ X t + ε * Real.exp (L * t) ∧ b t ≤ Z t + ε * Real.exp (L * t) := by
    let P := fun s => X s + ε * Real.exp (L * s)
    let Q := fun s => Z s + ε * Real.exp (L * s)
    let Pd := fun s => -α * X s + r * Z s + L * (ε * Real.exp (L * s))
    let Qd := fun s => c * X s - lam * Z s + L * (ε * Real.exp (L * s))
    have hP (s : ℝ) : HasDerivAt P (Pd s) s := (hX s).add (hbump ε s)
    have hQ (s : ℝ) : HasDerivAt Q (Qd s) s := (hZ s).add (hbump ε s)
    have hPpos (s : ℝ) (hs : 0 ≤ s) : 0 < P s :=
      add_pos_of_nonneg_of_pos (hXZ s hs).1 (mul_pos hε (Real.exp_pos _))
    have hQpos (s : ℝ) (hs : 0 ≤ s) : 0 < Q s :=
      add_pos_of_nonneg_of_pos (hXZ s hs).2 (mul_pos hε (Real.exp_pos _))
    let f : Fin 2 → ℝ → ℝ := ![fun s => a s ^ 2 - P s ^ 2, fun s => b s ^ 2 - Q s ^ 2]
    let f' : Fin 2 → ℝ → ℝ := ![fun s => da s - 2 * P s * Pd s, fun s => db s - 2 * Q s * Qd s]
    have hd : ∀ i s, s ∈ Icc (0 : ℝ) t → HasDerivAt (f i) (f' i s) s := by
      intro i s hs; fin_cases i
      · simpa [f, f', pow_one] using (hda s hs.1).fun_sub ((hP s).fun_pow 2)
      · simpa [f, f', pow_one] using (hdb s hs.1).fun_sub ((hQ s).fun_pow 2)
    have hinit : ∀ i, f i 0 ≤ 0 := by
      intro i; fin_cases i
      · dsimp [f, P]; simp only [mul_zero, Real.exp_zero, mul_one]
        nlinarith [ha 0]
      · dsimp [f, Q]; simp only [mul_zero, Real.exp_zero, mul_one]
        nlinarith [hb 0]
    have hboundary : ∀ s ∈ Ico (0 : ℝ) t, (∀ i, f i s ≤ 0) →
        ∀ i, f i s = 0 → f' i s < 0 := by
      intro s hs hfs i heq
      have hapos := ha s
      have hbpos := hb s
      have hp' := hPpos s hs.1
      have hq' := hQpos s hs.1
      have hf0 := hfs 0
      have hf1 := hfs 1
      dsimp [f] at hf0 hf1
      have hab : a s ≤ P s := by nlinarith
      have hbb : b s ≤ Q s := by nlinarith
      have hδ : 0 < ε * Real.exp (L * s) := mul_pos hε (Real.exp_pos _)
      fin_cases i
      · dsimp [f] at heq
        have heq' : a s = P s := by nlinarith
        change da s - 2 * P s * Pd s < 0
        calc
          _ ≤ (-2 * α * a s ^ 2 + 2 * r * a s * b s) - 2 * P s * Pd s :=
            sub_le_sub_right (hda_le s hs.1) _
          _ ≤ (-2 * α * P s ^ 2 + 2 * r * P s * Q s) - 2 * P s * Pd s := by
            rw [heq']; gcongr
          _ = -(2 * P s * (ε * Real.exp (L * s)) * (L + α - r)) := by dsimp [P, Q, Pd]; ring
          _ < 0 := neg_neg_of_pos (mul_pos (mul_pos (mul_pos (by norm_num) hp') hδ) hL.1)
      · dsimp [f] at heq
        have heq' : b s = Q s := by nlinarith
        change db s - 2 * Q s * Qd s < 0
        calc
          _ ≤ (2 * c * a s * b s - 2 * lam * b s ^ 2) - 2 * Q s * Qd s :=
            sub_le_sub_right (hdb_le s hs.1) _
          _ ≤ (2 * c * P s * Q s - 2 * lam * Q s ^ 2) - 2 * Q s * Qd s := by
            rw [heq']; gcongr
          _ = -(2 * Q s * (ε * Real.exp (L * s)) * (L + lam - c)) := by dsimp [P, Q, Qd]; ring
          _ < 0 := neg_neg_of_pos (mul_pos (mul_pos (mul_pos (by norm_num) hq') hδ) hL.2)
    have h := finite_fence f f' hd hinit hboundary t ⟨ht, le_rfl⟩
    have h0 := h 0
    have h1 := h 1
    dsimp [f] at h0 h1
    exact ⟨by nlinarith [ha t, hPpos t ht], by nlinarith [hb t, hQpos t ht]⟩
  constructor
  · have hcont : ContinuousWithinAt (fun ε : ℝ => X t + ε * Real.exp (L * t)) (Ioi 0) 0 := by fun_prop
    have h := continuousWithinAt_const.closure_le (by simp : (0 : ℝ) ∈ closure (Ioi 0))
      hcont (fun ε hε => (hp ε hε).1)
    simpa using h
  · have hcont : ContinuousWithinAt (fun ε : ℝ => Z t + ε * Real.exp (L * t)) (Ioi 0) 0 := by fun_prop
    have h := continuousWithinAt_const.closure_le (by simp : (0 : ℝ) ∈ closure (Ioi 0))
      hcont (fun ε hε => (hp ε hε).2)
    simpa using h

theorem feedback_abs_le (R z : ℂ) (r : ℝ) (hR : ‖R‖ ≤ r) :
    |(R * star z).re| ≤ r * ‖z‖ := by
  calc
    _ ≤ ‖R * star z‖ := Complex.abs_re_le_norm _
    _ = ‖R‖ * ‖z‖ := by simp
    _ ≤ r * ‖z‖ := mul_le_mul_of_nonneg_right hR (norm_nonneg _)

theorem population_energy_le (α r u : ℝ) (R z : ℂ) (hR : ‖R‖ ≤ r) :
    2 * u * (-α * u + (R * star z).re) ≤
      -2 * α * |u| ^ 2 + 2 * r * |u| * ‖z‖ := by
  have h : u * (R * star z).re ≤ r * |u| * ‖z‖ := by
    calc
      _ ≤ |u * (R * star z).re| := le_abs_self _
      _ = |u| * |(R * star z).re| := abs_mul _ _
      _ ≤ |u| * (r * ‖z‖) := mul_le_mul_of_nonneg_left (feedback_abs_le R z r hR) (abs_nonneg _)
      _ = _ := by ring
  rw [sq_abs]
  nlinarith only [h]

/-- 任意频率的旋转项在平方模长导数中精确消失。 -/
theorem coherence_energy_le (Γ ω c lam u : ℝ) (C E z : ℂ)
    (hC : ‖C‖ ≤ c) (hΓ : lam ≤ Γ - ‖E‖) :
    2 * inner (𝕜 := ℝ) z (C * (u : ℂ) + E * star z - ((Γ : ℂ) + I * ω) * z) ≤
      2 * c * |u| * ‖z‖ - 2 * lam * ‖z‖ ^ 2 := by
  have heq : inner (𝕜 := ℝ) z (C * (u : ℂ) + E * star z - ((Γ : ℂ) + I * ω) * z) =
      (C * (u : ℂ) * star z).re + (E * star z * star z).re - Γ * ‖z‖ ^ 2 := by
    simp [Complex.inner, Complex.mul_re, Complex.mul_im, Complex.sq_norm, normSq_apply]
    ring
  have hsrc : (C * (u : ℂ) * star z).re ≤ c * |u| * ‖z‖ := by
    calc
      _ ≤ ‖C * (u : ℂ) * star z‖ := Complex.re_le_norm _
      _ = ‖C‖ * |u| * ‖z‖ := by simp
      _ ≤ c * |u| * ‖z‖ := by gcongr
  have hself : (E * star z * star z).re ≤ ‖E‖ * ‖z‖ ^ 2 := by
    calc
      _ ≤ ‖E * star z * star z‖ := Complex.re_le_norm _
      _ = ‖E‖ * ‖z‖ ^ 2 := by simp; ring
  have hdamp := mul_le_mul_of_nonneg_right hΓ (sq_nonneg ‖z‖)
  rw [heq]
  nlinarith

theorem ode_modulus_comparison (α r c lam Γ ω : ℝ) (R C E : ℂ)
    (hr : 0 ≤ r) (hc : 0 ≤ c) (hR : ‖R‖ ≤ r) (hC : ‖C‖ ≤ c) (hΓ : lam ≤ Γ - ‖E‖)
    (u : ℝ → ℝ) (z : ℝ → ℂ) (X Z : ℝ → ℝ)
    (hu : ∀ s, 0 ≤ s → HasDerivAt u (-α * u s + (R * star (z s)).re) s)
    (hz : ∀ s, 0 ≤ s → HasDerivAt z (C * (u s : ℂ) + E * star (z s) - ((Γ : ℂ) + I * ω) * z s) s)
    (hX : ∀ s, HasDerivAt X (-α * X s + r * Z s) s)
    (hZ : ∀ s, HasDerivAt Z (c * X s - lam * Z s) s)
    (hu0 : |u 0| ≤ X 0) (hz0 : ‖z 0‖ ≤ Z 0) {t : ℝ} (ht : 0 ≤ t) :
    |u t| ≤ X t ∧ ‖z t‖ ≤ Z t := by
  apply squared_comparison α r c lam hr hc (fun s => |u s|) (fun s => ‖z s‖)
    (fun s => 2 * u s * (-α * u s + (R * star (z s)).re))
    (fun s => 2 * inner (𝕜 := ℝ) (z s)
      (C * (u s : ℂ) + E * star (z s) - ((Γ : ℂ) + I * ω) * z s)) X Z
    (fun s => abs_nonneg _) (fun s => norm_nonneg _)
  · intro s hs
    simpa only [sq_abs, pow_one, Nat.reduceSub, Nat.cast_ofNat] using (hu s hs).fun_pow 2
  · intro s hs; exact (hz s hs).norm_sq
  · intro s _; exact population_energy_le α r (u s) R (z s) hR
  · intro s _; exact coherence_energy_le Γ ω c lam (u s) C E (z s) hC hΓ
  · exact hX
  · exact hZ
  · exact hu0
  · exact hz0
  · exact ht

/-- 人口与比较人口之和保留两份自由衰减。 -/
theorem population_retained_decay (α r v : ℝ) (R : ℂ) (hr : 0 ≤ r) (hR : ‖R‖ ≤ r)
    (u : ℝ → ℝ) (z : ℝ → ℂ) (X Z : ℝ → ℝ)
    (hu : ∀ s, 0 ≤ s → HasDerivAt u (-α * u s + (R * star (z s)).re) s)
    (hX : ∀ s, HasDerivAt X (-α * X s + r * Z s) s)
    (hu0 : u 0 = v) (hX0 : X 0 = v)
    (hbound : ∀ s, 0 ≤ s → ‖z s‖ ≤ Z s) {t : ℝ} (ht : 0 ≤ t) :
    2 * v * Real.exp (-α * t) - X t ≤ u t := by
  let F := fun s : ℝ => Real.exp (α * s) * (u s + X s)
  let F' := fun s : ℝ => Real.exp (α * s) * ((R * star (z s)).re + r * Z s)
  have hd (s : ℝ) (hs : 0 ≤ s) : HasDerivAt F (F' s) s := by
    convert (((hasDerivAt_id s).const_mul α).exp).fun_mul ((hu s hs).fun_add (hX s)) using 1 <;>
      dsimp [F, F'] <;> ring
  have hpos (s : ℝ) (hs : 0 ≤ s) : 0 ≤ F' s := by
    apply mul_nonneg (Real.exp_pos _).le
    have hfb := (abs_le.mp (feedback_abs_le R (z s) r hR)).1
    have hm := mul_le_mul_of_nonneg_left (hbound s hs) hr
    linarith
  have hmono : MonotoneOn F (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · exact fun s hs => (hd s hs).continuousAt.continuousWithinAt
    · intro s hs; exact (hd s (interior_subset hs)).hasDerivWithinAt
    · intro s hs; exact hpos s (interior_subset hs)
  have hh := hmono (show (0 : ℝ) ∈ Ici 0 by simp) ht ht
  dsimp [F] at hh
  simp only [mul_zero, Real.exp_zero, one_mul, hu0, hX0] at hh
  have hh' := mul_le_mul_of_nonneg_left hh (Real.exp_pos (-α * t)).le
  have hexp : Real.exp (-α * t) * Real.exp (α * t) = 1 := by
    rw [← Real.exp_add]; simp
  rw [← mul_assoc, hexp, one_mul] at hh'
  nlinarith

/-- 完整复线性方程到真实二阶矩阵指数的正比较。 -/
theorem positive_comparison (α r c lam Γ ω v w : ℝ) (R C E : ℂ)
    (hv : 0 ≤ v) (hw : 0 ≤ w) (hr : 0 ≤ r) (hc : 0 ≤ c)
    (hR : ‖R‖ ≤ r) (hC : ‖C‖ ≤ c) (hΓ : lam ≤ Γ - ‖E‖)
    (u : ℝ → ℝ) (z : ℝ → ℂ)
    (hu : ∀ s, 0 ≤ s → HasDerivAt u (-α * u s + (R * star (z s)).re) s)
    (hz : ∀ s, 0 ≤ s → HasDerivAt z (C * (u s : ℂ) + E * star (z s) - ((Γ : ℂ) + I * ω) * z s) s)
    (hu0 : u 0 = v) (hz0 : z 0 = (w : ℂ)) {t : ℝ} (ht : 0 ≤ t) :
    2 * v ^ 2 * Real.exp (-α * t) -
      dotProduct ![v,w] (NormedSpace.exp (t • comparisonMatrix α r c lam) *ᵥ ![v,w]) ≤
        v * u t + w * (z t).re := by
  let X := fun s => comparisonFlow α r c lam v w s 0
  let Z := fun s => comparisonFlow α r c lam v w s 1
  have hX := comparisonFlow_deriv_zero α r c lam v w
  have hZ := comparisonFlow_deriv_one α r c lam v w
  have hX0 : X 0 = v := by simp [X, comparisonFlow_zero]
  have hZ0 : Z 0 = w := by simp [Z, comparisonFlow_zero]
  have hbound (s : ℝ) (hs : 0 ≤ s) : |u s| ≤ X s ∧ ‖z s‖ ≤ Z s := by
    apply ode_modulus_comparison α r c lam Γ ω R C E hr hc hR hC hΓ u z X Z hu hz hX hZ
    · simp [hu0, hX0, abs_of_nonneg hv]
    · simp [hz0, hZ0, abs_of_nonneg hw]
    · exact hs
  have hpop := population_retained_decay α r v R hr hR u z X Z hu hX hu0 hX0
    (fun s hs => (hbound s hs).2) ht
  have hzlower : -Z t ≤ (z t).re := by
    have hzabs := Complex.abs_re_le_norm (z t)
    have hzbd := (hbound t ht).2
    have := (abs_le.mp (hzabs.trans hzbd)).1
    exact this
  have hp := mul_le_mul_of_nonneg_left hpop hv
  have hq := mul_le_mul_of_nonneg_left hzlower hw
  change 2 * v ^ 2 * Real.exp (-α * t) -
      dotProduct ![v,w] (comparisonFlow α r c lam v w t) ≤ _
  simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  change 2 * v ^ 2 * Real.exp (-α * t) - (v * X t + w * Z t) ≤ _
  nlinarith

#print axioms finite_fence
#print axioms comparisonFlow_hasDerivAt
#print axioms positive_system_nonneg
#print axioms squared_comparison
#print axioms ode_modulus_comparison
#print axioms population_retained_decay
#print axioms positive_comparison

end TwoStateQuantumEmbedding.ResetComparison
