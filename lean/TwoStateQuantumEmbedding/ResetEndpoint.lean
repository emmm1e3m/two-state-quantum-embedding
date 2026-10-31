import TwoStateQuantumEmbedding.Envelope
import TwoStateQuantumEmbedding.OriginalProblem
import TwoStateQuantumEmbedding.ResetUniform

noncomputable section
open Set Filter Matrix
open scoped Topology ComplexOrder

namespace TwoStateQuantumEmbedding.ResetEndpoint

/-- 测量基中的全部对角密度矩阵，包括两个纯态端点。 -/
def diagonalState (ν : ℝ) : QubitMatrix := Matrix.diagonal ![(ν : ℂ), 1 - ν]

/-- 存在至少一个对角稳态，不要求稳态唯一。 -/
def HasDiagonalStationary {n : ℕ} (H : QubitMatrix) (J : Fin n → QubitMatrix) : Prop :=
  ∃ ν ∈ Icc (0 : ℝ) 1, gkslAction H J (diagonalState ν) = 0

/-- 原始有限时间输出类，附加对角稳态条件。 -/
def diagonalFiniteOutputs : Set (ℝ × ℝ) :=
  {p | ∃ (n : ℕ) (H : QubitMatrix) (J : Fin n → QubitMatrix) (t : ℝ),
    H.IsHermitian ∧ 0 ≤ t ∧ HasDiagonalStationary H J ∧ finiteOutput H J t = p}

def Qdiag : Set (ℝ × ℝ) := closure diagonalFiniteOutputs

/-- 固定实际扰动 ε 的全部增益；没有将 ε 改为误差上限。 -/
def gainValues (S : Set (ℝ × ℝ)) (ε : ℝ) : Set ℝ :=
  {g | (ε - g, 1 - ε) ∈ S}

def gain (S : Set (ℝ × ℝ)) (ε : ℝ) : ℝ := sSup (gainValues S ε)
def resetGain (ε : ℝ) : ℝ := gain Q2 ε
def diagonalResetGain (ε : ℝ) : ℝ := gain Qdiag ε

def scaledGain (k : ℕ) (S : Set (ℝ × ℝ)) (ε : ℝ) : ℝ :=
  Real.log (1 / ε) ^ k / ε * gain S ε

/-- K016 的最终无条件目标类型；此定义不宣称已证明。 -/
def ResetLaw : Prop :=
  Tendsto (scaledGain 1 Q2) (𝓝[>] (0 : ℝ)) (𝓝 (4 / Real.exp 1))

/-- K017 的最终无条件目标类型；此定义不宣称已证明。 -/
def DiagonalResetLaw : Prop :=
  Tendsto (scaledGain 2 Qdiag) (𝓝[>] (0 : ℝ)) (𝓝 (64 / Real.exp 1 ^ 2))

theorem diagonalFiniteOutputs_subset_finiteOutputs : diagonalFiniteOutputs ⊆ finiteOutputs := by
  rintro p ⟨n, H, J, t, hH, ht, _, hp⟩
  exact ⟨n, H, J, t, hH, ht, hp⟩

theorem Qdiag_subset_Q2 : Qdiag ⊆ Q2 :=
  closure_mono diagonalFiniteOutputs_subset_finiteOutputs

theorem Qdiag_isClosed : IsClosed Qdiag := isClosed_closure

theorem Qdiag_isCompact : IsCompact Qdiag :=
  Q2_isCompact.of_isClosed_subset Qdiag_isClosed Qdiag_subset_Q2

theorem diagonalFiniteOutput_mem_Qdiag {n : ℕ} (H : QubitMatrix)
    (J : Fin n → QubitMatrix) (t : ℝ) (hH : H.IsHermitian) (ht : 0 ≤ t)
    (hs : HasDiagonalStationary H J) : finiteOutput H J t ∈ Qdiag :=
  subset_closure ⟨n, H, J, t, hH, ht, hs, rfl⟩

theorem diagonalState_is_density {ν : ℝ} (hν : ν ∈ Icc (0 : ℝ) 1) :
    (diagonalState ν).PosSemidef ∧ Matrix.trace (diagonalState ν) = 1 := by
  constructor
  · apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    fin_cases i <;> simp
    · exact_mod_cast hν.1
    · exact_mod_cast hν.2
  · simp [diagonalState, Matrix.trace, Fin.sum_univ_two]

theorem hasDiagonalStationary_time_scaling {n : ℕ} (H : QubitMatrix)
    (J : Fin n → QubitMatrix) (t : ℝ) (ht : 0 ≤ t)
    (hs : HasDiagonalStationary H J) :
    HasDiagonalStationary (t • H) (fun μ => Real.sqrt t • J μ) := by
  obtain ⟨ν, hν, hs⟩ := hs
  refine ⟨ν, hν, ?_⟩
  rw [gkslAction_time_scaling H J _ t ht, hs, smul_zero]

/-- 任意有限非负时间和时间一描述相同的对角稳态输出类。 -/
theorem mem_diagonalFiniteOutputs_iff_unitTime (p : ℝ × ℝ) :
    p ∈ diagonalFiniteOutputs ↔
      ∃ (n : ℕ) (H : QubitMatrix) (J : Fin n → QubitMatrix),
        H.IsHermitian ∧ HasDiagonalStationary H J ∧ finiteOutput H J 1 = p := by
  constructor
  · rintro ⟨n, H, J, t, hH, ht, hs, hp⟩
    refine ⟨n, t • H, (fun μ => Real.sqrt t • J μ), ?_,
      hasDiagonalStationary_time_scaling H J t ht hs,
      (finiteOutput_time_normalization H J t ht).trans hp⟩
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_smul, star_trivial, hH.eq]
  · rintro ⟨n, H, J, hH, hs, hp⟩
    exact ⟨n, H, J, 1, hH, by norm_num, hs, hp⟩

theorem gainValues_isCompact {S : Set (ℝ × ℝ)} (hclosed : IsClosed S)
    (hS : S ⊆ Q2) (ε : ℝ) : IsCompact (gainValues S ε) := by
  apply (isCompact_Icc : IsCompact (Icc (ε - 1) ε)).of_isClosed_subset
    (hclosed.preimage (by fun_prop))
  intro g hg
  have hp := (Q2_subset_unitSquare (hS hg)).1
  change 0 ≤ ε - g ∧ ε - g ≤ 1 at hp
  constructor <;> linarith [hp.1, hp.2]

theorem gainValues_bddAbove {S : Set (ℝ × ℝ)} (hS : S ⊆ Q2) (ε : ℝ) :
    BddAbove (gainValues S ε) := by
  refine ⟨ε, ?_⟩
  intro g hg
  have hp := (Q2_subset_unitSquare (hS hg)).1.1
  change 0 ≤ ε - g at hp
  linarith

theorem gain_isGreatest {S : Set (ℝ × ℝ)} (hclosed : IsClosed S)
    (hS : S ⊆ Q2) {ε : ℝ} (hne : (gainValues S ε).Nonempty) :
    IsGreatest (gainValues S ε) (gain S ε) :=
  (gainValues_isCompact hclosed hS ε).isGreatest_sSup hne

theorem output_gain_le {S : Set (ℝ × ℝ)} (hS : S ⊆ Q2) {a ε : ℝ}
    (hp : (a, 1 - ε) ∈ S) : ε - a ≤ gain S ε := by
  apply le_csSup (gainValues_bddAbove hS ε)
  simpa only [gainValues, mem_ofPred_eq, sub_sub_cancel] using hp

theorem gain_le_of_output_bound {S : Set (ℝ × ℝ)} {ε B : ℝ}
    (hne : (gainValues S ε).Nonempty)
    (hB : ∀ a : ℝ, (a, 1 - ε) ∈ S → ε - a ≤ B) : gain S ε ≤ B := by
  apply csSup_le hne
  intro g hg
  have h := hB (ε - g) hg
  simpa only [sub_sub_cancel] using h

theorem zero_gain_mem_Q2 {ε : ℝ} (hε : ε ∈ Icc (0 : ℝ) 1) :
    (ε, 1 - ε) ∈ Q2 := by
  have h : CanonicalBias.outputFromXZ 0 (2 * ε - 1) ∈ Q2 := by
    apply Envelope.mem_Q2_iff.mpr
    constructor
    · norm_num
    · rw [Envelope.F_classical (by norm_num : (0 : ℝ) ∈ Icc 0 1)]
      rw [abs_le]
      constructor <;> linarith [hε.1, hε.2]
  convert h using 1 <;> dsimp [CanonicalBias.outputFromXZ] <;> congr 1 <;> ring

theorem resetGain_isGreatest {ε : ℝ} (hε : ε ∈ Icc (0 : ℝ) 1) :
    IsGreatest (gainValues Q2 ε) (resetGain ε) := by
  apply gain_isGreatest Q2_isClosed (Subset.refl _)
  exact ⟨0, by simpa [gainValues] using zero_gain_mem_Q2 hε⟩

theorem resetGain_bounds {ε : ℝ} (hε : ε ∈ Icc (0 : ℝ) 1) :
    0 ≤ resetGain ε ∧ resetGain ε ≤ ε := by
  refine ⟨(resetGain_isGreatest hε).2 ?_, ?_⟩
  · simpa [gainValues] using zero_gain_mem_Q2 hε
  · have hp := (Q2_subset_unitSquare (resetGain_isGreatest hε).1).1.1
    change 0 ≤ ε - resetGain ε at hp
    linarith

/-- 固定正 ε 处的连续性把统一有限输出上界传到概率闭包。 -/
theorem output_bound_on_closure {S : Set (ℝ × ℝ)} {B : ℝ → ℝ} {δ : ℝ}
    (hB : ContinuousOn B (Ioo 0 δ))
    (hfinite : ∀ p ∈ S, 0 < 1 - p.2 → 1 - p.2 < δ →
      1 - p.2 - p.1 ≤ B (1 - p.2))
    {a ε : ℝ} (hp : (a, 1 - ε) ∈ closure S) (hε : ε ∈ Ioo 0 δ) :
    ε - a ≤ B ε := by
  let p : ℝ × ℝ := (a, 1 - ε)
  have hp' : p ∈ closure S := hp
  have : NeBot (𝓝[S] p) := mem_closure_iff_nhdsWithin_neBot.mp hp'
  have hcε : ContinuousAt (fun q : ℝ × ℝ => 1 - q.2) p := by fun_prop
  have hbε : ContinuousAt B ε := (hB ε hε).continuousAt (Ioo_mem_nhds hε.1 hε.2)
  have hb : ContinuousAt (fun q : ℝ × ℝ => B (1 - q.2)) p := by
    have hb' : ContinuousAt B (1 - p.2) := by simpa [p] using hbε
    exact ContinuousAt.comp (f := fun q : ℝ × ℝ => 1 - q.2) hb' hcε
  have he : ∀ᶠ q : ℝ × ℝ in 𝓝[S] p, 1 - q.2 ∈ Ioo 0 δ := by
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    exact hcε.preimage_mem_nhds (by simpa [p] using Ioo_mem_nhds hε.1 hε.2)
  have hlim := le_of_tendsto_of_tendsto
    (show Tendsto (fun q : ℝ × ℝ => 1 - q.2 - q.1) (𝓝[S] p)
      (𝓝 (1 - p.2 - p.1)) from (by fun_prop : ContinuousAt
        (fun q : ℝ × ℝ => 1 - q.2 - q.1) p).continuousWithinAt)
    hb.continuousWithinAt
    (show ∀ᶠ q : ℝ × ℝ in 𝓝[S] p, 1 - q.2 - q.1 ≤ B (1 - q.2) from by
      filter_upwards [self_mem_nhdsWithin, he] with q hq hqε
      exact hfinite q hq hqε.1 hqε.2)
  simpa [p] using hlim

/-- 统一上包络与逐个实际误差的有限见证，在同一切片上夹逼最优增益。 -/
theorem scaledGain_tendsto_of_bounds {S : Set (ℝ × ℝ)} (hS : S ⊆ Q2)
    (k : ℕ) (C : ℝ) (a upper : ℝ → ℝ)
    (hwitness : ∀ᶠ ε : ℝ in 𝓝[>] 0, (a ε, 1 - ε) ∈ S)
    (hupper : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ∀ a' : ℝ, (a', 1 - ε) ∈ S → ε - a' ≤ upper ε)
    (hlower : Tendsto (fun ε => Real.log (1 / ε) ^ k / ε * (ε - a ε))
      (𝓝[>] 0) (𝓝 C))
    (hlimupper : Tendsto (fun ε => Real.log (1 / ε) ^ k / ε * upper ε)
      (𝓝[>] 0) (𝓝 C)) :
    Tendsto (scaledGain k S) (𝓝[>] 0) (𝓝 C) := by
  have hscale : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 ≤ Real.log (1 / ε) ^ k / ε := by
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
      nhdsWithin_le_nhds] with ε hε hε1
    have hpos : 0 < ε := hε
    have hlog : 0 ≤ Real.log (1 / ε) := Real.log_nonneg ((le_div_iff₀ hpos).mpr (by linarith))
    exact div_nonneg (pow_nonneg hlog _) hpos.le
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hlimupper
  · filter_upwards [hwitness, hscale] with ε hp hs
    exact mul_le_mul_of_nonneg_left (output_gain_le hS hp) hs
  · filter_upwards [hwitness, hupper, hscale] with ε hp hu hs
    apply mul_le_mul_of_nonneg_left _ hs
    apply gain_le_of_output_bound ?_ hu
    exact ⟨ε - a ε, by simpa [gainValues] using hp⟩

/-- 有限类上的统一连续上界和匹配下界，自动装配为其概率闭包的极限。
此引理保留全部数学输入，不声称这些上界或匹配极限已获证明。 -/
theorem scaledGain_closure_tendsto_of_finite_bounds
    {S : Set (ℝ × ℝ)} (hS : S ⊆ Q2) (k : ℕ) (C : ℝ)
    (a upper : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hcontinuous : ContinuousOn upper (Ioo 0 δ))
    (hfinite : ∀ p ∈ S, 0 < 1 - p.2 → 1 - p.2 < δ →
      1 - p.2 - p.1 ≤ upper (1 - p.2))
    (hwitness : ∀ᶠ ε : ℝ in 𝓝[>] 0, (a ε, 1 - ε) ∈ S)
    (hlower : Tendsto (fun ε => Real.log (1 / ε) ^ k / ε * (ε - a ε))
      (𝓝[>] 0) (𝓝 C))
    (hupper : Tendsto (fun ε => Real.log (1 / ε) ^ k / ε * upper ε)
      (𝓝[>] 0) (𝓝 C)) :
    Tendsto (scaledGain k (closure S)) (𝓝[>] 0) (𝓝 C) := by
  apply scaledGain_tendsto_of_bounds (closure_minimal hS Q2_isClosed) k C a upper
  · exact hwitness.mono fun _ hp => subset_closure hp
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with ε hε hεδ
    intro a' hp
    exact output_bound_on_closure hcontinuous hfinite hp ⟨hε, hεδ⟩
  · exact hlower
  · exact hupper

/-- K016 的条件装配：输入必须是在实际有限 GKSL 输出上的已证明估计。 -/
theorem resetLaw_of_finite_bounds (a upper : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hcontinuous : ContinuousOn upper (Ioo 0 δ))
    (hfinite : ∀ p ∈ finiteOutputs, 0 < 1 - p.2 → 1 - p.2 < δ →
      1 - p.2 - p.1 ≤ upper (1 - p.2))
    (hwitness : ∀ᶠ ε : ℝ in 𝓝[>] 0, (a ε, 1 - ε) ∈ finiteOutputs)
    (hlower : Tendsto (fun ε => Real.log (1 / ε) / ε * (ε - a ε))
      (𝓝[>] 0) (𝓝 (4 / Real.exp 1)))
    (hupper : Tendsto (fun ε => Real.log (1 / ε) / ε * upper ε)
      (𝓝[>] 0) (𝓝 (4 / Real.exp 1))) : ResetLaw := by
  apply scaledGain_closure_tendsto_of_finite_bounds
    (S := finiteOutputs) subset_closure 1 (4 / Real.exp 1) a upper δ hδ
    hcontinuous hfinite hwitness
  · simpa only [pow_one] using hlower
  · simpa only [pow_one] using hupper

/-- K017 的条件装配，与全类共享闭包和极限逻辑。 -/
theorem diagonalResetLaw_of_finite_bounds (a upper : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hcontinuous : ContinuousOn upper (Ioo 0 δ))
    (hfinite : ∀ p ∈ diagonalFiniteOutputs, 0 < 1 - p.2 → 1 - p.2 < δ →
      1 - p.2 - p.1 ≤ upper (1 - p.2))
    (hwitness : ∀ᶠ ε : ℝ in 𝓝[>] 0, (a ε, 1 - ε) ∈ diagonalFiniteOutputs)
    (hlower : Tendsto (fun ε => Real.log (1 / ε) ^ 2 / ε * (ε - a ε))
      (𝓝[>] 0) (𝓝 (64 / Real.exp 1 ^ 2)))
    (hupper : Tendsto (fun ε => Real.log (1 / ε) ^ 2 / ε * upper ε)
      (𝓝[>] 0) (𝓝 (64 / Real.exp 1 ^ 2))) : DiagonalResetLaw := by
  exact scaledGain_closure_tendsto_of_finite_bounds
    (diagonalFiniteOutputs_subset_finiteOutputs.trans subset_closure)
    2 (64 / Real.exp 1 ^ 2) a upper δ hδ hcontinuous hfinite hwitness hlower hupper

end TwoStateQuantumEmbedding.ResetEndpoint

#print axioms TwoStateQuantumEmbedding.ResetEndpoint.output_bound_on_closure
#print axioms TwoStateQuantumEmbedding.ResetEndpoint.scaledGain_tendsto_of_bounds
#print axioms TwoStateQuantumEmbedding.ResetEndpoint.diagonalState_is_density
#print axioms TwoStateQuantumEmbedding.ResetEndpoint.mem_diagonalFiniteOutputs_iff_unitTime
#print axioms TwoStateQuantumEmbedding.ResetEndpoint.resetGain_isGreatest
#print axioms TwoStateQuantumEmbedding.ResetEndpoint.resetGain_bounds
#print axioms TwoStateQuantumEmbedding.ResetEndpoint.scaledGain_closure_tendsto_of_finite_bounds
#print axioms TwoStateQuantumEmbedding.ResetEndpoint.resetLaw_of_finite_bounds
#print axioms TwoStateQuantumEmbedding.ResetEndpoint.diagonalResetLaw_of_finite_bounds
#print TwoStateQuantumEmbedding.ResetEndpoint.ResetLaw
#print TwoStateQuantumEmbedding.ResetEndpoint.DiagonalResetLaw
