import TwoStateQuantumEmbedding.CanonicalBias
import TwoStateQuantumEmbedding.UnitaryBoundary
import TwoStateQuantumEmbedding.ResetFamily
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open Set Filter Matrix
open scoped Topology ComplexOrder

namespace TwoStateQuantumEmbedding.Envelope
open CanonicalBias

set_option maxRecDepth 3000
set_option maxHeartbeats 1200000

/-- 包络只由原始可达闭包的实际切片定义。 -/
def feasibleBiases (x : ℝ) : Set ℝ := {z | outputFromXZ x z ∈ Q2}
def F (x : ℝ) : ℝ := sSup (feasibleBiases x)

theorem output_coordinates (x z : ℝ) :
    (outputFromXZ x z).1 + (outputFromXZ x z).2 - 1 = x ∧
    (outputFromXZ x z).1 - (outputFromXZ x z).2 = z := by
  constructor <;> dsimp [outputFromXZ] <;> ring

theorem outputFromXZ_continuous : Continuous (fun p : ℝ × ℝ => outputFromXZ p.1 p.2) := by
  unfold outputFromXZ
  fun_prop

theorem feasible_diamond {x z : ℝ} (hz : z ∈ feasibleBiases x) :
    x ∈ Icc (-1 : ℝ) 1 ∧ |z| ≤ 1 - |x| := by
  obtain ⟨ha, hb⟩ := Q2_subset_unitSquare hz
  have hd := (TwoState.Geometry.stochastic_iff_diamond _ _).mp
    ⟨ha.1, ha.2, hb.1, hb.2⟩
  rw [(output_coordinates x z).1, (output_coordinates x z).2] at hd
  refine ⟨?_, hd⟩
  dsimp [outputFromXZ] at ha hb
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

theorem zero_feasible {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    0 ∈ feasibleBiases x := by
  have hd := diagonal_mem_Q2 (b := (1+x)/2) (by constructor <;> linarith [hx.1,hx.2])
  simpa [feasibleBiases, outputFromXZ] using hd

theorem feasibleBiases_nonempty {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    (feasibleBiases x).Nonempty := ⟨0, zero_feasible hx⟩

theorem feasibleBiases_isCompact (x : ℝ) : IsCompact (feasibleBiases x) := by
  apply (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)).of_isClosed_subset
    (Q2_isClosed.preimage (by unfold outputFromXZ; fun_prop))
  intro z hz
  have hd := (feasible_diamond hz).2
  have h := abs_le.mp (le_trans hd (by linarith [abs_nonneg x] : 1-|x| ≤ 1))
  exact h

theorem F_isGreatest {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    IsGreatest (feasibleBiases x) (F x) :=
  (feasibleBiases_isCompact x).isGreatest_sSup (feasibleBiases_nonempty hx)

theorem F_mem {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    outputFromXZ x (F x) ∈ Q2 := (F_isGreatest hx).1

theorem F_nonneg {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) : 0 ≤ F x :=
  (F_isGreatest hx).2 (zero_feasible hx)

theorem F_le_diamond {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) : F x ≤ 1-|x| :=
  (le_abs_self _).trans (feasible_diamond (F_isGreatest hx).1).2

theorem neg_feasible {x z : ℝ} (hz : z ∈ feasibleBiases x) :
    -z ∈ feasibleBiases x := by
  have hs := Q2_swap hz
  simpa [feasibleBiases, outputFromXZ, sub_eq_add_neg] using hs

/-- 实际切片是闭对称区间，包括退化为单点的情况。 -/
theorem mem_Q2_iff {x z : ℝ} : outputFromXZ x z ∈ Q2 ↔
    x ∈ Icc (-1 : ℝ) 1 ∧ |z| ≤ F x := by
  constructor
  · intro hz
    have hx := (feasible_diamond hz).1
    exact ⟨hx, abs_le.mpr ⟨by linarith [(F_isGreatest hx).2 (neg_feasible hz)],
      (F_isGreatest hx).2 hz⟩⟩
  · rintro ⟨hx, hz⟩
    by_cases hF : F x = 0
    · have hz0 : z = 0 := abs_nonpos_iff.mp (hF ▸ hz)
      simpa [hz0, feasibleBiases] using zero_feasible hx
    · have hFp : 0 < F x := lt_of_le_of_ne (F_nonneg hx) (Ne.symm hF)
      have hlo : -1 ≤ z / F x := (le_div_iff₀ hFp).mpr (by linarith [(abs_le.mp hz).1])
      have hhi : z / F x ≤ 1 := (div_le_iff₀ hFp).mpr (by linarith [(abs_le.mp hz).2])
      have hm := Q2_antidiagonal_filling (z / F x) hlo hhi (F_mem hx)
      convert hm using 1
      apply Prod.ext <;> dsimp [outputFromXZ, antidiagonalMix] <;> field_simp <;> ring

theorem Q2_envelope_iff (p : ℝ × ℝ) : p ∈ Q2 ↔
    p.1+p.2-1 ∈ Icc (-1 : ℝ) 1 ∧ |p.1-p.2| ≤ F (p.1+p.2-1) := by
  have he : outputFromXZ (p.1+p.2-1) (p.1-p.2) = p := by
    apply Prod.ext <;> dsimp [outputFromXZ] <;> ring
  rw [← mem_Q2_iff, he]

theorem F_neg_one : F (-1) = 0 := by
  have hx : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := by constructor <;> norm_num
  have hu := F_le_diamond hx
  norm_num at hu
  exact le_antisymm hu (F_nonneg hx)

/-- 非负偏置截面把整个下图转为 Q2 的连续原像。 -/
theorem F_upperSemicontinuousOn : UpperSemicontinuousOn F (Icc (-1 : ℝ) 1) := by
  rw [upperSemicontinuousOn_iff_isClosed_hypograph isClosed_Icc]
  have he : {p : ℝ × ℝ | p.1 ∈ Icc (-1 : ℝ) 1 ∧ p.2 ≤ F p.1} =
      (fun p : ℝ × ℝ => outputFromXZ p.1 (max p.2 0)) ⁻¹' Q2 := by
    ext p
    simp only [mem_ofPred_eq, mem_preimage, mem_Q2_iff, abs_of_nonneg (le_max_right p.2 0),
      max_le_iff]
    constructor
    · rintro ⟨hx, hz⟩
      exact ⟨hx, hz, F_nonneg hx⟩
    · rintro ⟨hx, hz, _⟩
      exact ⟨hx, hz⟩
  rw [he]
  exact Q2_isClosed.preimage (by unfold outputFromXZ; fun_prop)

/-- 正相位振幅阻尼跳跃；它是已验证精确重置解的一个有限参数成员。 -/
def dampingJump : QubitMatrix := !![0, 1; 0, 0]
def dampingJumps (γ : ℝ) : Fin 1 → QubitMatrix := fun _ => Real.sqrt γ • dampingJump

theorem reset_damping_jumps : ResetFamily.jumps 0 1 0 (-1) = fun _ => dampingJump := by
  funext μ
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ResetFamily.jumps, ResetFamily.jump, ResetFamily.rotation,
      ResetFamily.triangularJump, ResetFamily.conjugate, dampingJump,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem damping_output_at_time (t : ℝ) :
    finiteOutput 0 (fun _ : Fin 1 => dampingJump) t = (1, Real.exp (-t)) := by
  have he := ResetFamily.finiteOutput_exact 0 1 0 (-1) 1 t
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [reset_damping_jumps] at he
  have ht : ((-1 : ℝ) + -1) * t / 2 = -t := by ring
  simpa [ResetFamily.aProbability, ResetFamily.epsilon, ResetFamily.bCoefficient, ht] using he

/-- 从原模型的时间缩放得到 H=0、sqrt(γ)|0><1|、时间 1 的实际公式。 -/
theorem damping_output (γ : ℝ) (hγ : 0 ≤ γ) :
    finiteOutput 0 (dampingJumps γ) 1 = (1, Real.exp (-γ)) := by
  have he := finiteOutput_time_normalization (0 : QubitMatrix)
    (fun _ : Fin 1 => dampingJump) γ hγ
  unfold dampingJumps
  simpa only [smul_zero] using he.trans (damping_output_at_time γ)

theorem classical_positive_endpoint {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    (1, x) ∈ Q2 := by
  have hγ : 0 ≤ -Real.log x := neg_nonneg.mpr (Real.log_nonpos hx0.le hx1)
  have hp := finiteOutput_mem_Q2 0 (dampingJumps (-Real.log x)) 1 (by simp) (by norm_num)
  rw [damping_output _ hγ, neg_neg, Real.exp_log hx0] at hp
  exact hp

theorem classical_zero_endpoint : ((1, 0) : ℝ × ℝ) ∈ Q2 := by
  have hp : ((0, 1) : ℝ × ℝ) ∈ Q2 :=
    Q2_isClosed.mem_of_tendsto ResetFamily.curvePoint_limit
      ResetFamily.curvePoint_eventually_mem_Q2
  exact Q2_swap hp

theorem classical_endpoint {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    outputFromXZ x (1-x) ∈ Q2 := by
  have hp : ((1, x) : ℝ × ℝ) ∈ Q2 := by
    rcases eq_or_lt_of_le hx.1 with he | he
    · simpa [← he] using classical_zero_endpoint
    · exact classical_positive_endpoint he hx.2
  convert hp using 1
  apply Prod.ext <;> dsimp [outputFromXZ] <;> ring

theorem F_classical {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : F x = 1-x := by
  have hxd : x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
  apply le_antisymm
  · simpa [abs_of_nonneg hx.1] using F_le_diamond hxd
  · exact (F_isGreatest hxd).2 (classical_endpoint hx)

open GKSLAlgebra TwoState.GeneralGeometry

theorem fixedZ_nonneg (h : BlochVec) (S : M3) : 0 ≤ fixedZ h S := by
  unfold fixedZ
  positivity

theorem fixed_endpoint_mem_Q2 (h : BlochVec) (S : M3) (hS : S.PosSemidef) :
    outputFromXZ (fixedX h S) (fixedZ h S) ∈ Q2 :=
  fixed_interval_mem_Q2 h S hS _ (by rw [abs_of_nonneg (fixedZ_nonneg h S)])

theorem fixedZ_le_one (h : BlochVec) (S : M3) (hS : S.PosSemidef) : fixedZ h S ≤ 1 := by
  have hd := (feasible_diamond (fixed_endpoint_mem_Q2 h S hS)).2
  rw [abs_of_nonneg (fixedZ_nonneg h S)] at hd
  linarith [abs_nonneg (fixedX h S)]

theorem exists_fixedX {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    ∃ (h : BlochVec) (S : M3), S.PosSemidef ∧ fixedX h S = x := by
  have hp := diagonal_mem_canonicalOutputs (b := (1+x)/2)
    (by constructor <;> linarith [hx.1, hx.2])
  rw [canonicalOutputs_eq_fixedOutputs] at hp
  obtain ⟨h, S, hS, z, _, he⟩ := hp
  refine ⟨h, S, hS, ?_⟩
  have hc := congrArg (fun p : ℝ × ℝ => p.1+p.2-1) he
  rw [(output_coordinates _ _).1] at hc
  dsimp at hc
  linarith

/-- 有限生成元的正偏置端点，在开 x 邻域上取上确界。 -/
def nearbyValues (x δ : ℝ) : Set ℝ :=
  {v | ∃ (h : BlochVec) (S : M3), S.PosSemidef ∧
    |fixedX h S-x| < δ ∧ v = fixedZ h S}
def nearbySup (x δ : ℝ) : ℝ := sSup (nearbyValues x δ)

theorem nearbyValues_nonempty {x δ : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) (hδ : 0 < δ) :
    (nearbyValues x δ).Nonempty := by
  obtain ⟨h, S, hS, he⟩ := exists_fixedX hx
  exact ⟨fixedZ h S, h, S, hS, by simpa [he], rfl⟩

theorem nearbyValues_bddAbove (x δ : ℝ) : BddAbove (nearbyValues x δ) := by
  refine ⟨1, ?_⟩
  rintro v ⟨h, S, hS, _, rfl⟩
  exact fixedZ_le_one h S hS

/-- 每个固定邻域的支撑上确界控制真实闭包切片；不交换闭包与精确切片。 -/
theorem F_le_nearbySup {x δ : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) (hδ : 0 < δ) :
    F x ≤ nearbySup x δ := by
  let C : Set (ℝ × ℝ) :=
    {p | δ ≤ |p.1+p.2-1-x|} ∪ {p | p.1-p.2 ≤ nearbySup x δ}
  have hC : IsClosed C := by
    apply IsClosed.union
    · exact isClosed_le continuous_const (by fun_prop)
    · exact isClosed_le (by fun_prop) continuous_const
  have hs : fixedOutputs ⊆ C := by
    rintro p ⟨h, S, hS, z, hz, rfl⟩
    by_cases hn : |fixedX h S-x| < δ
    · apply Or.inr
      change (outputFromXZ _ _).1 - (outputFromXZ _ _).2 ≤ _
      rw [(output_coordinates _ _).2]
      exact (le_abs_self z).trans (hz.trans
        (le_csSup (nearbyValues_bddAbove x δ) ⟨h, S, hS, hn, rfl⟩))
    · apply Or.inl
      change δ ≤ |(outputFromXZ _ _).1 + (outputFromXZ _ _).2-1-x|
      rw [(output_coordinates _ _).1]
      exact le_of_not_gt hn
  have hp : outputFromXZ x (F x) ∈ closure fixedOutputs := by
    rw [← Q2_eq_closure_fixedOutputs]
    exact F_mem hx
  have hm := closure_minimal hs hC hp
  rcases hm with hm | hm
  · change δ ≤ |(outputFromXZ x (F x)).1+(outputFromXZ x (F x)).2-1-x| at hm
    rw [(output_coordinates _ _).1] at hm
    simp only [sub_self, abs_zero] at hm
    linarith
  · change (outputFromXZ x (F x)).1 - (outputFromXZ x (F x)).2 ≤ nearbySup x δ at hm
    rwa [(output_coordinates _ _).2] at hm

theorem nearbySup_upper {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ → nearbySup x r ≤ F x + ε := by
  have hu := F_upperSemicontinuousOn x hx (F x + ε) (by linarith)
  obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhdsWithin_iff.mp hu
  refine ⟨δ, hδ, fun r hr hrd => ?_⟩
  apply csSup_le (nearbyValues_nonempty hx hr)
  rintro v ⟨h, S, hS, hn, rfl⟩
  have he := mem_Q2_iff.mp (fixed_endpoint_mem_Q2 h S hS)
  have hlt : F (fixedX h S) < F x + ε :=
    hd ⟨by simpa [Metric.mem_ball, Real.dist_eq] using hn.trans hrd, he.1⟩
  have hle : fixedZ h S ≤ F (fixedX h S) :=
    (le_abs_self _).trans he.2
  exact hle.trans hlt.le

/-- 论文的右侧邻域极限，保留全部有限 h、PSD S 和严格邻域量词。 -/
theorem relaxed_variational_limit {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    Tendsto (nearbySup x) (𝓝[>] (0 : ℝ)) (𝓝 (F x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := nearbySup_upper hx (ε/2) (by linarith)
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)] with r hr hrd
  have hlo := F_le_nearbySup hx hr
  have hhi := hd r hr hrd
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hlo)]
  linarith

#print axioms F_isGreatest
#print axioms mem_Q2_iff
#print axioms F_upperSemicontinuousOn
#print axioms damping_output
#print axioms F_classical
#print axioms F_le_nearbySup
#print axioms relaxed_variational_limit

end TwoStateQuantumEmbedding.Envelope

