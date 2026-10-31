import TwoStateQuantumEmbedding.ResetActualComparison
import TwoStateQuantumEmbedding.ResetDiagonalIdentity
import TwoStateQuantumEmbedding.ResetMixedBridge
import TwoStateQuantumEmbedding.ResetStationaryBudget
import TwoStateQuantumEmbedding.StationaryExistence
import TwoStateQuantumEmbedding.ResetMixedEnvelopeDefs
import TwoStateQuantumEmbedding.ResetEndpoint

noncomputable section
open Matrix Complex Set
open scoped BigOperators Matrix.Norms.Operator ComplexOrder

namespace TwoStateQuantumEmbedding.ResetActual

open PureStationary ResetEndpoint

/-- 未取正部的实际比较下界。 -/
def lowerComparison (p ν A B : ℝ) : ℝ :=
  2 * ResetEnvelope.tiltV p ^ 2 * Real.exp (-ResetEnvelope.alpha ν A) -
    ResetEnvelope.quadratic p (NormedSpace.exp (ResetEnvelope.comparisonMatrix ν A B))

theorem gain_le_envelope_of_lower {q p ν A B : ℝ}
    (hq : lowerComparison p ν A B ≤ q) : -q ≤ ResetEnvelope.envelope p ν A B := by
  unfold lowerComparison at hq
  unfold ResetEnvelope.envelope
  exact (by linarith : -q ≤ _).trans (le_max_left _ _)

theorem canonical_envelope_lower {n : ℕ} (x y z : Fin n → ℂ) (ω ν p : ℝ) (h : ℂ)
    (hs : gkslAction (ResetMixed.hamiltonian ω h) (ResetMixed.jumps x y z)
      (ResetMixed.state 1 ν 0) = 0)
    (hν0 : 0 ≤ ν) (hν : ν < 1/2) (hp0 : 0 ≤ p) (hp : p ≤ 1/2) :
    lowerComparison p ν (ResetMixed.rate z) (ResetMixed.rate x) ≤
      (1-2*p) * ResetMixed.population (ResetMixed.hamiltonian ω h)
        (ResetMixed.jumps x y z) (initialDifference p) 1 +
      2*Real.sqrt (p*(1-p)) *
        (ResetMixed.coherence (ResetMixed.hamiltonian ω h)
          (ResetMixed.jumps x y z) (initialDifference p) 1).re := by
  convert canonical_comparison x y z ω ν p 1 h hs hν0 hν hp0 hp (by norm_num) using 1 <;>
    simp [lowerComparison, ResetEnvelope.quadratic, ResetEnvelope.tiltV,
      ResetEnvelope.tiltW, ResetEnvelope.comparisonMatrix, ResetEnvelope.alpha,
      ResetEnvelope.chi, ResetEnvelope.up, ResetEnvelope.down, ResetEnvelope.lambda,
      ResetComparison.comparisonMatrix, ResetMixed.alpha, ResetMixed.chi,
      ResetMixed.rBound, ResetMixed.cBound, ResetMixed.lam, mul_comm, mul_left_comm, mul_assoc]

/-- 任意给定密度稳态进入包络，返回同一稳态的谱基而不重新选择稳态。 -/
theorem unitTime_stationary_mixed_comparison {n : ℕ} (H : QubitMatrix)
    (J : Fin n → QubitMatrix) (hH : H.IsHermitian)
    (ρ : QubitMatrix) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hstat : gkslAction H J ρ = 0)
    (hε : 1-(finiteOutput H J 1).2 < 1/4)
    (hq : (finiteOutput H J 1).1+(finiteOutput H J 1).2-1 ≤ 0) :
    ∃ (ν p A B : ℝ) (U : QubitMatrix),
      0 ≤ ν ∧ ν < 1/2 ∧ 0 ≤ p ∧ p < 1/2 ∧ 0 ≤ A ∧ 0 ≤ B ∧
      Uᴴ*U=1 ∧ U*Uᴴ=1 ∧ ρ=conjugate U (ResetMixed.state 1 ν 0) ∧
      p=normSq (U 0 1) ∧ (ρ 0 0).re=ν+(1-2*ν)*p ∧
      p+ν ≤ spectralBudget (1-(finiteOutput H J 1).2) ∧
      lowerComparison p ν A B ≤ (finiteOutput H J 1).1+(finiteOutput H J 1).2-1 ∧
      1-(finiteOutput H J 1).2-(finiteOutput H J 1).1 ≤ ResetEnvelope.envelope p ν A B := by
  obtain ⟨ν,p,U,ω,h,x,y,z,hν0,hνhalf,hp0,hp1,hU,hUU,hρU,hpn,hpop,hM,hs,hn,ha,he⟩ :=
    ResetMixedSpectral.original_mixed_normal_form H ρ J hH hρ htr hstat
  have hout := finiteOutput_mem_unitSquare H J 1 hH (by norm_num)
  have he0 : 0 ≤ 1-(finiteOutput H J 1).2 := by linarith [hout.2.2]
  have hstar0 := (density_diagonal_mem_Icc hρ htr 0).1
  have hbudget := gksl_stationary_measurement_product H J 1 hH (by norm_num) ρ hρ htr hstat
  have hstar := measurement_budget_upper hout.1.1 he0 (by linarith) hε hstar0 hbudget
  obtain ⟨_,_,hν,hp,hjoint⟩ :=
    spectral_budget_of_population he0 hε hν0 hνhalf hp0 hpop hstar
  have hc := canonical_envelope_lower x y z ω ν p h hs hν0 hν hp0 hp.le
  have hr := ResetMixedSpectral.original_mixed_readout H U J hH ω h x y z p 1
    (by norm_num) hU hUU hM hn
  have hl : lowerComparison p ν (ResetMixed.rate z) (ResetMixed.rate x) ≤
      (finiteOutput H J 1).1+(finiteOutput H J 1).2-1 := by
    rw [hr]
    exact hc
  refine ⟨ν,p,ResetMixed.rate z,ResetMixed.rate x,U,hν0,hν,hp0,hp,
    ResetMixed.rate_nonneg z,ResetMixed.rate_nonneg x,hU,hUU,hρU,hpn,hpop,hjoint,hl,?_⟩
  have hg := gain_le_envelope_of_lower hl
  linarith

/-- 任意原始生成元在时间一的真实输出，自动获得共同谱预算和真实比较矩阵。 -/
theorem unitTime_finiteOutput_mixed_comparison {n : ℕ} (H : QubitMatrix)
    (J : Fin n → QubitMatrix) (hH : H.IsHermitian)
    (hε : 1-(finiteOutput H J 1).2 < 1/4)
    (hq : (finiteOutput H J 1).1+(finiteOutput H J 1).2-1 ≤ 0) :
    ∃ ν p A B : ℝ, 0 ≤ ν ∧ ν < 1/2 ∧ 0 ≤ p ∧ p < 1/2 ∧
      0 ≤ A ∧ 0 ≤ B ∧ p+ν ≤ spectralBudget (1-(finiteOutput H J 1).2) ∧
      lowerComparison p ν A B ≤ (finiteOutput H J 1).1+(finiteOutput H J 1).2-1 ∧
      1-(finiteOutput H J 1).2-(finiteOutput H J 1).1 ≤ ResetEnvelope.envelope p ν A B := by
  obtain ⟨ρ,hρ,htr,hstat⟩ := gksl_exists_stationary_density H J hH
  obtain ⟨ν,p,A,B,U,hν0,hν,hp0,hp,hA,hB,hU,hUU,hρU,hpn,hpop,hjoint,hl,hg⟩ :=
    unitTime_stationary_mixed_comparison H J hH ρ hρ htr hstat hε hq
  exact ⟨ν,p,A,B,hν0,hν,hp0,hp,hA,hB,hjoint,hl,hg⟩

/-- 时间缩放保留指定的原密度稳态，故此版本可用于任意稳态选择的饱和序列。 -/
theorem stationary_finiteOutput_mixed_comparison {n : ℕ} (H : QubitMatrix)
    (J : Fin n → QubitMatrix) (t : ℝ) (hH : H.IsHermitian) (ht : 0 ≤ t)
    (ρ : QubitMatrix) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hstat : gkslAction H J ρ = 0)
    (hε : 1-(finiteOutput H J t).2 < 1/4)
    (hq : (finiteOutput H J t).1+(finiteOutput H J t).2-1 ≤ 0) :
    ∃ (ν p A B : ℝ) (U : QubitMatrix),
      0 ≤ ν ∧ ν < 1/2 ∧ 0 ≤ p ∧ p < 1/2 ∧ 0 ≤ A ∧ 0 ≤ B ∧
      Uᴴ*U=1 ∧ U*Uᴴ=1 ∧ ρ=conjugate U (ResetMixed.state 1 ν 0) ∧
      p=normSq (U 0 1) ∧ (ρ 0 0).re=ν+(1-2*ν)*p ∧
      p+ν ≤ spectralBudget (1-(finiteOutput H J t).2) ∧
      lowerComparison p ν A B ≤ (finiteOutput H J t).1+(finiteOutput H J t).2-1 ∧
      1-(finiteOutput H J t).2-(finiteOutput H J t).1 ≤ ResetEnvelope.envelope p ν A B := by
  have hscaled : (t • H).IsHermitian := by
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_smul, star_trivial, hH.eq]
  have hs' : gkslAction (t • H) (fun μ => Real.sqrt t • J μ) ρ = 0 := by
    rw [gkslAction_time_scaling H J ρ t ht, hstat, smul_zero]
  have hn := finiteOutput_time_normalization H J t ht
  have hε' : 1-(finiteOutput (t • H) (fun μ => Real.sqrt t • J μ) 1).2 < 1/4 := by
    simpa only [hn] using hε
  have hq' : (finiteOutput (t • H) (fun μ => Real.sqrt t • J μ) 1).1+
      (finiteOutput (t • H) (fun μ => Real.sqrt t • J μ) 1).2-1 ≤ 0 := by
    simpa only [hn] using hq
  simpa only [hn] using unitTime_stationary_mixed_comparison
    (t • H) (fun μ => Real.sqrt t • J μ) hscaled ρ hρ htr hs' hε' hq'

/-- 任意非负时间先严格吸收到生成元，阈值不依赖跳跃数、速率或频率。 -/
theorem finiteOutput_mixed_comparison {n : ℕ} (H : QubitMatrix)
    (J : Fin n → QubitMatrix) (t : ℝ) (hH : H.IsHermitian) (ht : 0 ≤ t)
    (hε : 1-(finiteOutput H J t).2 < 1/4)
    (hq : (finiteOutput H J t).1+(finiteOutput H J t).2-1 ≤ 0) :
    ∃ ν p A B : ℝ, 0 ≤ ν ∧ ν < 1/2 ∧ 0 ≤ p ∧ p < 1/2 ∧
      0 ≤ A ∧ 0 ≤ B ∧ p+ν ≤ spectralBudget (1-(finiteOutput H J t).2) ∧
      lowerComparison p ν A B ≤ (finiteOutput H J t).1+(finiteOutput H J t).2-1 ∧
      1-(finiteOutput H J t).2-(finiteOutput H J t).1 ≤ ResetEnvelope.envelope p ν A B := by
  have hscaled : (t • H).IsHermitian := by
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_smul, star_trivial, hH.eq]
  have hn := finiteOutput_time_normalization H J t ht
  have hε' : 1-(finiteOutput (t • H) (fun μ => Real.sqrt t • J μ) 1).2 < 1/4 := by
    simpa only [hn] using hε
  have hq' : (finiteOutput (t • H) (fun μ => Real.sqrt t • J μ) 1).1+
      (finiteOutput (t • H) (fun μ => Real.sqrt t • J μ) 1).2-1 ≤ 0 := by
    simpa only [hn] using hq
  simpa only [hn] using unitTime_finiteOutput_mixed_comparison
    (t • H) (fun μ => Real.sqrt t • J μ) hscaled hε' hq'

theorem lowerComparison_zero_tilt (ν A B : ℝ) :
    lowerComparison 0 ν A B = 2*Real.exp (-ResetEnvelope.alpha ν A) -
      NormedSpace.exp (ResetEnvelope.comparisonMatrix ν A B) 0 0 := by
  simp [lowerComparison, ResetEnvelope.tiltV, ResetEnvelope.tiltW,
    ResetEnvelope.quadratic, dotProduct, Matrix.mulVec, Fin.sum_univ_two]

/-- 对角读出中任一速率为零时，比较下界严格为正。 -/
theorem lowerComparison_zero_rate (ν A B : ℝ) (hz : A = 0 ∨ B = 0) :
    lowerComparison 0 ν A B = Real.exp (-ResetEnvelope.alpha ν A) := by
  have hmat : ResetEnvelope.comparisonMatrix ν A B =
      Matrix.diagonal ![-ResetEnvelope.alpha ν A,-ResetEnvelope.lambda ν A B] := by
    rcases hz with rfl | rfl <;>
      ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [ResetEnvelope.comparisonMatrix, ResetEnvelope.up, ResetEnvelope.down,
        Matrix.diagonal]
  rw [lowerComparison_zero_tilt, hmat, Matrix.exp_diagonal]
  simp [Pi.exp_def, ← Real.exp_eq_exp_ℝ]
  ring

theorem positive_rates_of_negative_diagonal_comparison {ν A B q : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hq : q < 0)
    (hc : lowerComparison 0 ν A B ≤ q) : 0 < A ∧ 0 < B := by
  have hnz : ¬(A=0 ∨ B=0) := by
    intro hz
    rw [lowerComparison_zero_rate ν A B hz] at hc
    exact (not_lt_of_ge ((Real.exp_pos _).le.trans hc)) hq
  exact ⟨lt_of_le_of_ne hA (fun h => hnz (Or.inl h.symm)),
    lt_of_le_of_ne hB (fun h => hnz (Or.inr h.symm))⟩

theorem unitTime_diagonal_comparison {n : ℕ} (H : QubitMatrix)
    (J : Fin n → QubitMatrix) (hH : H.IsHermitian) (ν : ℝ) (hν0 : 0 ≤ ν)
    (hs : gkslAction H J (diagonalState ν) = 0)
    (hε : 1-(finiteOutput H J 1).2 < 1/4)
    (hq : (finiteOutput H J 1).1+(finiteOutput H J 1).2-1 ≤ 0) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      lowerComparison 0 ν A B ≤ (finiteOutput H J 1).1+(finiteOutput H J 1).2-1 := by
  have hνe := diagonal_nu_le_error H J 1 ν hH (by norm_num) hν0 hs hq
  have hν : ν < 1/2 := by linarith
  have hdiag : diagonalState ν = ResetMixed.state 1 ν 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [diagonalState, ResetMixed.state]
  rw [hdiag] at hs
  obtain ⟨ω,h,x,y,z,hn,hsn⟩ := ResetMixed.stationary_normal_form H hH J ν hs
  have hM : conjugate (1 : QubitMatrix)ᴴ (Matrix.single 0 0 1) =
      ResetMixed.measurement 0 (2*Real.sqrt (0*(1-0))) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [conjugate, ResetMixed.measurement, Matrix.single_apply]
  have hn' : ∀ X, gkslAction (conjugate (1 : QubitMatrix)ᴴ H)
      (fun μ => conjugate (1 : QubitMatrix)ᴴ (J μ)) X =
      gkslAction (ResetMixed.hamiltonian ω h) (ResetMixed.jumps x y z) X := by
    simpa only [conjugate, Matrix.conjTranspose_one, one_mul, mul_one] using hn
  have hr := ResetMixedSpectral.original_mixed_readout H 1 J hH ω h x y z 0 1
    (by norm_num) (by simp) (by simp) hM hn'
  refine ⟨ResetMixed.rate z,ResetMixed.rate x,
    ResetMixed.rate_nonneg z,ResetMixed.rate_nonneg x,?_⟩
  rw [hr]
  exact canonical_envelope_lower x y z ω ν 0 h hsn hν0 hν (by norm_num) (by norm_num)

/-- 任意有限演化时间的对角类：同一稳态人口、精确误差关系与零倾角包络。 -/
theorem diagonal_finiteOutput_comparison {n : ℕ} (H : QubitMatrix)
    (J : Fin n → QubitMatrix) (t : ℝ) (hH : H.IsHermitian) (ht : 0 ≤ t)
    (hstat : HasDiagonalStationary H J)
    (hε : 1-(finiteOutput H J t).2 < 1/4)
    (hq : (finiteOutput H J t).1+(finiteOutput H J t).2-1 ≤ 0) :
    ∃ ν A B : ℝ, 0 ≤ ν ∧ ν ≤ 1-(finiteOutput H J t).2 ∧ ν < 1/2 ∧
      0 ≤ A ∧ 0 ≤ B ∧
      1-(finiteOutput H J t).2 = ν * (1-((finiteOutput H J t).1+(finiteOutput H J t).2-1)) ∧
      2*Real.exp (-ResetEnvelope.alpha ν A) -
        NormedSpace.exp (ResetEnvelope.comparisonMatrix ν A B) 0 0 ≤
          (finiteOutput H J t).1+(finiteOutput H J t).2-1 ∧
      1-(finiteOutput H J t).2-(finiteOutput H J t).1 ≤ ResetEnvelope.envelope 0 ν A B := by
  obtain ⟨ν,hν,hs⟩ := hstat
  have hνe := diagonal_nu_le_error H J t ν hH ht hν.1 hs hq
  have hνhalf : ν < 1/2 := by linarith
  have hid := diagonal_output_identity H J t ν hH ht hs
  have hscaled : (t • H).IsHermitian := by
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_smul, star_trivial, hH.eq]
  have hs' : gkslAction (t • H) (fun μ => Real.sqrt t • J μ) (diagonalState ν) = 0 := by
    rw [gkslAction_time_scaling H J _ t ht, hs, smul_zero]
  have hn := finiteOutput_time_normalization H J t ht
  have hε' : 1-(finiteOutput (t • H) (fun μ => Real.sqrt t • J μ) 1).2 < 1/4 := by
    simpa only [hn] using hε
  have hq' : (finiteOutput (t • H) (fun μ => Real.sqrt t • J μ) 1).1+
      (finiteOutput (t • H) (fun μ => Real.sqrt t • J μ) 1).2-1 ≤ 0 := by
    simpa only [hn] using hq
  obtain ⟨A,B,hA,hB,hc⟩ := unitTime_diagonal_comparison
    (t • H) (fun μ => Real.sqrt t • J μ) hscaled ν hν.1 hs' hε' hq'
  rw [hn] at hc
  refine ⟨ν,A,B,hν.1,hνe,hνhalf,hA,hB,hid,?_,?_⟩
  · simpa only [lowerComparison_zero_tilt] using hc
  · have hg := gain_le_envelope_of_lower hc
    linarith

#print axioms finiteOutput_mixed_comparison
#print axioms unitTime_stationary_mixed_comparison
#print axioms stationary_finiteOutput_mixed_comparison
#print axioms diagonal_output_identity
#print axioms diagonal_nu_le_error
#print axioms diagonal_finiteOutput_comparison
#print axioms positive_rates_of_negative_diagonal_comparison

end TwoStateQuantumEmbedding.ResetActual
