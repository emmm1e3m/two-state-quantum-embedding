import TwoStateQuantumEmbedding.CompactAttainment
import TwoStateQuantumEmbedding.NearSwapLocalization
import TwoStateQuantumEmbedding.SwapMatching

/-! 真实交换下边界的有限达到；闭包逼近允许第二坐标变化。 -/
noncomputable section
open Matrix Set
open scoped ComplexOrder

namespace TwoStateQuantumEmbedding.SwapFiniteAttainment
open CanonicalBloch GKSLAlgebra CompactAttainment

def smallRadius : ℝ := min (NearSwap.radius 41) (SwapMatching.beta0 ^ 2 / 8)

theorem smallRadius_pos : 0 < smallRadius := by
  apply lt_min (NearSwap.radius_pos 41 (by norm_num))
  have := SwapMatching.beta0_pos
  positivity

/-- 合法性与真实切片最小性，而非驻点条件。 -/
def IsSwapMinimizer (h : BlochVec) (K : KMatrix) (b : ℝ) : Prop :=
  K.PosSemidef ∧ canonicalOutput h K 1 = (lowerBoundary b, b)

theorem lowerBoundary_finite {b : ℝ} (hb : 0 < b) (hsmall : b < smallRadius) :
    (lowerBoundary b, b) ∈ finiteOutputs := by
  have hbη : b < NearSwap.radius 41 := hsmall.trans_le (min_le_left _ _)
  have hbm : b ≤ SwapMatching.beta0 ^ 2 / 8 := hsmall.le.trans (min_le_right _ _)
  apply lowerBoundary_finite_of_uniform_bounds Swap.slope 6 1 (NearSwap.radius 41) b
    (SwapMatching.small_b_mem_unitInterval hb hbm) hb hbη
    (SwapMatching.lowerBoundary_small_upper hb hbm)
  intro q hq hqpos hqsmall hqnear
  obtain ⟨h, K, hK, hh, htrace, hout⟩ :=
    NearSwap.finite_near_bounded_parameters 41 (by norm_num) q hq hqpos hqsmall.le hqnear
  refine ⟨(h, K), ?_, hout⟩
  exact ⟨by simpa using hh, hK, htrace⟩

theorem exists_swapMinimizer {b : ℝ} (hb : 0 < b) (hsmall : b < smallRadius) :
    ∃ (h : BlochVec) (K : KMatrix), IsSwapMinimizer h K b := by
  have hp := lowerBoundary_finite hb hsmall
  rw [finiteOutputs_eq_canonicalOutputs] at hp
  exact hp

theorem exists_bounded_swapMinimizer {b : ℝ} (hb : 0 < b) (hsmall : b < smallRadius) :
    ∃ (h : BlochVec) (K : KMatrix), IsSwapMinimizer h K b ∧ ‖h‖ ≤ 6 ∧ K.trace.re ≤ 1 := by
  have hbm : b ≤ SwapMatching.beta0 ^ 2 / 8 := hsmall.le.trans (min_le_right _ _)
  obtain ⟨h, K, hK, hh, htrace, hout⟩ :=
    NearSwap.finite_near_bounded_parameters 41 (by norm_num) (lowerBoundary b, b)
      (lowerBoundary_finite hb hsmall) hb (hsmall.le.trans (min_le_left _ _))
      (by have hu := SwapMatching.lowerBoundary_small_upper hb hbm
          dsimp
          nlinarith [sq_nonneg b])
  exact ⟨h, K, ⟨hK, hout⟩, hh, htrace⟩

/-- 同一范围内的每个真实极小元均受统一定位控制。 -/
theorem all_minimizers_localized {h : BlochVec} {K : KMatrix} {b : ℝ}
    (hb : 0 < b) (hsmall : b < smallRadius) (hmin : IsSwapMinimizer h K b) :
    NearSwap.Localized 41 b (AzimuthGauge.transverseRadius h) (h 2) (NearSwap.gaugeNoise h K) := by
  apply NearSwap.canonical_near_localization h K hmin.1 41 b (by norm_num) hb
    (hsmall.le.trans (min_le_left _ _))
  · rw [hmin.2]
  · rw [hmin.2]
    have hu := SwapMatching.lowerBoundary_small_upper hb
      (hsmall.le.trans (min_le_right _ _))
    dsimp
    nlinarith [sq_nonneg b]

theorem lowerBoundary_three_jumps {b : ℝ} (hb : 0 < b) (hsmall : b < smallRadius) :
    ∃ (h : BlochVec) (A : Fin 3 → QubitMatrix),
      (hamiltonian h).IsHermitian ∧ finiteOutput (hamiltonian h) A 1 = (lowerBoundary b, b) := by
  obtain ⟨h, K, hK, hout⟩ := exists_swapMinimizer hb hsmall
  obtain ⟨A, hA⟩ := exists_finiteOutput_for_canonical h K hK
  exact ⟨h, A, hamiltonian_hermitian h, (hA 1).trans hout⟩

#print axioms lowerBoundary_finite
#print axioms exists_bounded_swapMinimizer
#print axioms all_minimizers_localized
#print axioms lowerBoundary_three_jumps

end TwoStateQuantumEmbedding.SwapFiniteAttainment
