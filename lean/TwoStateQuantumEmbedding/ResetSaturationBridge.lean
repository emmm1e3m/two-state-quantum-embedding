import TwoStateQuantumEmbedding.ResetActualEnvelope
import TwoStateQuantumEmbedding.ResetBudgetAsymptotics

noncomputable section
open Set Filter Matrix Complex
open scoped Topology ComplexOrder

namespace TwoStateQuantumEmbedding.ResetFinal
open ResetEndpoint ResetActual PureStationary

/-- 容差形式的全参数界沿任意合法序列给出趋零余项。 -/
theorem refined_remainder_exists (C : ℝ)
    (hsharp : ∀ η : ℝ, 0 < η → ∃ δ > 0,
      ∀ ρ p ν A B : ℝ, 0 < ρ → ρ < δ → 0 ≤ p → 0 ≤ ν → p+ν ≤ ρ →
        0 ≤ A → 0 ≤ B → Real.log (1/ρ)*ResetEnvelope.envelope p ν A B ≤ C*p+η*ρ)
    (ε p ν A B g : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝[>] (0 : ℝ)))
    (hdata : ∀ᶠ n in atTop, 0 ≤ p n ∧ 0 ≤ ν n ∧
      p n+ν n ≤ spectralBudget (ε n) ∧ 0 ≤ A n ∧ 0 ≤ B n ∧
      g n ≤ ResetEnvelope.envelope (p n) (ν n) (A n) (B n)) :
    ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, Real.log (1/spectralBudget (ε n))*g n ≤
        C*p n+r n*spectralBudget (ε n) := by
  let r := fun n => max ((Real.log (1/spectralBudget (ε n))*g n-C*p n) /
    spectralBudget (ε n)) 0
  have hρ := spectralBudget_tendsto_zero.comp hε
  have hsmall := hε.eventually (Ioo_mem_nhdsGT (show (0 : ℝ) < 1/64 by norm_num))
  refine ⟨r,?_,?_⟩
  · apply tendsto_order.2
    constructor
    · intro a ha
      exact Eventually.of_forall fun n => lt_of_lt_of_le ha (le_max_right _ _)
    · intro b hb
      obtain ⟨δ,hδ,hs⟩ := hsharp (b/2) (by positivity)
      filter_upwards [hdata,hsmall,hρ.eventually (eventually_lt_nhds hδ),
        hρ.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))]
        with n hd he hδn hρone
      have hρpos := spectralBudget_pos_small he
      have hL := resetLog_pos ⟨hρpos,hρone⟩
      have hf := hs (spectralBudget (ε n)) (p n) (ν n) (A n) (B n)
        hρpos hδn hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2.1
      have hg := mul_le_mul_of_nonneg_left hd.2.2.2.2.2 hL.le
      have hr : r n ≤ b/2 := by
        apply max_le _ (by linarith)
        apply (div_le_iff₀ hρpos).2
        linarith
      linarith
  · filter_upwards [hsmall] with n hn
    have hρpos := spectralBudget_pos_small hn
    have hr := (div_le_iff₀ hρpos).mp
      (le_max_left ((Real.log (1/spectralBudget (ε n))*g n-C*p n) /
        spectralBudget (ε n)) 0)
    change _ ≤ C*p n+r n*spectralBudget (ε n)
    dsimp only [r] at *
    linarith

def outputError (P : ℝ × ℝ) : ℝ := 1-P.2
def outputGain (P : ℝ × ℝ) : ℝ := 1-P.2-P.1

/-- 只包含实际原模型序列；统一优化前提将在最终无条件推论中由150消除。 -/
theorem actual_stationary_saturation_of_refined_envelope
    (hsharp : ∀ η : ℝ, 0 < η → ∃ δ > 0,
      ∀ ρ p ν A B : ℝ, 0 < ρ → ρ < δ → 0 ≤ p → 0 ≤ ν → p+ν ≤ ρ →
        0 ≤ A → 0 ≤ B → Real.log (1/ρ)*ResetEnvelope.envelope p ν A B ≤
          (4/Real.exp 1)*p+η*ρ)
    (N : ℕ → ℕ) (H : ℕ → QubitMatrix) (J : ∀ n, Fin (N n) → QubitMatrix)
    (t : ℕ → ℝ) (ρ : ℕ → QubitMatrix)
    (hH : ∀ n, (H n).IsHermitian) (ht : ∀ n, 0 ≤ t n)
    (hρ : ∀ n, (ρ n).PosSemidef ∧ (ρ n).trace=1 ∧ gkslAction (H n) (J n) (ρ n)=0)
    (hε : Tendsto (fun n => outputError (finiteOutput (H n) (J n) (t n)))
      atTop (𝓝[>] (0 : ℝ)))
    (hsat : Tendsto (fun n =>
      Real.log (1/outputError (finiteOutput (H n) (J n) (t n))) /
        outputError (finiteOutput (H n) (J n) (t n)) *
          outputGain (finiteOutput (H n) (J n) (t n))) atTop (𝓝 (4/Real.exp 1))) :
    ∃ (ν p : ℕ → ℝ) (U : ℕ → QubitMatrix),
      (∀ᶠ n in atTop, 0 ≤ ν n ∧ ν n < 1/2 ∧ 0 ≤ p n ∧ p n < 1/2 ∧
        (U n)ᴴ*U n=1 ∧ U n*(U n)ᴴ=1 ∧
        ρ n=conjugate (U n) (ResetMixed.state 1 (ν n) 0) ∧
        p n=normSq (U n 0 1)) ∧
      Tendsto (fun n => p n/outputError (finiteOutput (H n) (J n) (t n))) atTop (𝓝 1) ∧
      Tendsto (fun n => ν n/outputError (finiteOutput (H n) (J n) (t n))) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖ρ n 0 1‖^2/outputError (finiteOutput (H n) (J n) (t n)))
        atTop (𝓝 1) ∧
      Tendsto (fun n => (1-(ρ n*ρ n).trace.re) /
        outputError (finiteOutput (H n) (J n) (t n))) atTop (𝓝 0) := by
  classical
  let ε := fun n => outputError (finiteOutput (H n) (J n) (t n))
  let g := fun n => outputGain (finiteOutput (H n) (J n) (t n))
  have hε' : Tendsto ε atTop (𝓝[>] (0 : ℝ)) := hε
  have hsat' : Tendsto (fun n => Real.log (1/ε n)/ε n*g n) atTop (𝓝 (4/Real.exp 1)) := hsat
  let good := fun n => 0 < ε n ∧ ε n < 1/4 ∧ 0 ≤ g n
  have hgood : ∀ᶠ n in atTop, good n := by
    filter_upwards [hε'.eventually (Ioo_mem_nhdsGT (show (0 : ℝ) < 1/4 by norm_num)),
      hsat'.eventually (eventually_gt_nhds (show (0 : ℝ) < 4/Real.exp 1 by positivity))]
      with n he hg
    have hL : 0 < Real.log (1/ε n)/ε n :=
      div_pos (resetLog_pos ⟨he.1,by linarith [he.2]⟩) he.1
    exact ⟨he.1,he.2,((mul_pos_iff_of_pos_left hL).mp hg).le⟩
  have hex (n : ℕ) : ∃ (ν p A B : ℝ) (U : QubitMatrix), good n →
      0 ≤ ν ∧ ν < 1/2 ∧ 0 ≤ p ∧ p < 1/2 ∧ 0 ≤ A ∧ 0 ≤ B ∧
      Uᴴ*U=1 ∧ U*Uᴴ=1 ∧ ρ n=conjugate U (ResetMixed.state 1 ν 0) ∧
      p=normSq (U 0 1) ∧ (ρ n 0 0).re=ν+(1-2*ν)*p ∧
      p+ν ≤ spectralBudget (ε n) ∧ g n ≤ ResetEnvelope.envelope p ν A B := by
    by_cases hg : good n
    · have he : 1-(finiteOutput (H n) (J n) (t n)).2 < 1/4 := hg.2.1
      have hq : (finiteOutput (H n) (J n) (t n)).1+
          (finiteOutput (H n) (J n) (t n)).2-1 ≤ 0 := by
        have hgn := hg.2.2
        dsimp [g,outputGain] at hgn
        linarith
      obtain ⟨ν,p,A,B,U,hν0,hν,hp0,hp,hA,hB,hU,hUU,hρU,hpn,hpop,hbudget,hl,hgain⟩ :=
        stationary_finiteOutput_mixed_comparison (H n) (J n) (t n) (hH n) (ht n)
          (ρ n) (hρ n).1 (hρ n).2.1 (hρ n).2.2 he hq
      exact ⟨ν,p,A,B,U,fun _ => ⟨hν0,hν,hp0,hp,hA,hB,hU,hUU,hρU,hpn,hpop,hbudget,hgain⟩⟩
    · exact ⟨0,0,0,0,1,fun hn => (hg hn).elim⟩
  choose ν p A B U hchosen using hex
  have hdata : ∀ᶠ n in atTop, 0 ≤ p n ∧ 0 ≤ ν n ∧
      p n+ν n ≤ spectralBudget (ε n) ∧ 0 ≤ A n ∧ 0 ≤ B n ∧
      g n ≤ ResetEnvelope.envelope (p n) (ν n) (A n) (B n) := by
    filter_upwards [hgood] with n hn
    rcases hchosen n hn with ⟨hν0,hν,hp0,hp,hA,hB,hU,hUU,hρU,hpn,hpop,hbudget,hgain⟩
    exact ⟨hp0,hν0,hbudget,hA,hB,hgain⟩
  obtain ⟨r,hr,hbound⟩ := refined_remainder_exists (4/Real.exp 1) hsharp ε p ν A B g hε' hdata
  have hdet : ∀ᶠ n in atTop, (ρ n).det=(ν n : ℂ)*(1-ν n) := by
    filter_upwards [hgood] with n hn
    rcases hchosen n hn with ⟨hν0,hν,hp0,hp,hA,hB,hU,hUU,hρU,hpn,hpop,hbudget,hgain⟩
    apply spectral_conjugate_det (ρ n) (U n) (ν n) hU
    have hd : ResetMixed.state 1 (ν n) 0=Matrix.diagonal ![(ν n : ℂ),1-ν n] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [ResetMixed.state]
    simpa only [hd,conjugate] using hρU
  have hpop : ∀ᶠ n in atTop, (ρ n 0 0).re=ν n+(1-2*ν n)*p n := by
    filter_upwards [hgood] with n hn
    exact (hchosen n hn).2.2.2.2.2.2.2.2.2.2.1
  have hout := actual_saturation_stationary_structure (4/Real.exp 1) (by positivity)
    ε p ν g r ρ hε' (hdata.mono fun n h => ⟨h.1,h.2.1⟩)
    (hdata.mono fun n h => h.2.2.1) hbound hsat' hr
    (Eventually.of_forall fun n => ⟨(hρ n).1,(hρ n).2.1⟩) hdet hpop
  refine ⟨ν,p,U,?_,hout⟩
  filter_upwards [hgood] with n hn
  rcases hchosen n hn with ⟨hν0,hν,hp0,hp,hA,hB,hU,hUU,hρU,hpn,hpop,hbudget,hgain⟩
  exact ⟨hν0,hν,hp0,hp,hU,hUU,hρU,hpn⟩

#print axioms refined_remainder_exists
#print axioms actual_stationary_saturation_of_refined_envelope
end TwoStateQuantumEmbedding.ResetFinal
