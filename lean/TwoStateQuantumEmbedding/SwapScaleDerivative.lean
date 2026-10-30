import TwoStateQuantumEmbedding.SwapMixedDerivatives
import TwoStateQuantumEmbedding.FirstOrderBridge
import TwoStateQuantumEmbedding.ExponentialGradient
import Mathlib.Tactic

/-! 真实指数 Frechet 导数与083的实际首阶积分逐项连接。 -/
noncomputable section
open Matrix
open scoped Topology Matrix.Norms.L2Operator

namespace TwoStateQuantumEmbedding.ActualSwapSystem
open GKSLAlgebra CanonicalBloch GKSLBounds

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def readoutOperator (s : ℝ) : (AugmentedSpace →L[ℝ] AugmentedSpace) →L[ℝ] ℝ :=
  (diagonalReadout s).comp (ContinuousLinearMap.apply ℝ AugmentedSpace (basisInitial s))

theorem hasDerivAt_readout_scale (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ) (s : ℝ) :
    HasDerivAt (fun k : ℝ => readoutOperator s
      (NormedSpace.exp (hamiltonianCLM h + k • dissipativeCLM K)))
      (firstOrderReturn h K 1 s) 0 := by
  have hi : HasDerivAt (fun k : ℝ => hamiltonianCLM h + k • dissipativeCLM K)
      (dissipativeCLM K) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (dissipativeCLM K)).const_add (hamiltonianCLM h)
  have hexp : HasFDerivAt NormedSpace.exp
      (ExponentialGradient.expDerivative (hamiltonianCLM h))
      (hamiltonianCLM h + (0 : ℝ) • dissipativeCLM K) := by
    convert ExponentialGradient.hasFDerivAt_exp_integral (hamiltonianCLM h) using 1
    apply ContinuousLinearMap.ext
    intro x
    change hamiltonianCLM h x + (0 : ℝ) • dissipativeCLM K x = hamiltonianCLM h x
    simp
  have he := hexp.comp_hasDerivAt 0 hi
  have hr := (readoutOperator s).hasFDerivAt.comp_hasDerivAt 0 he
  exact hr

theorem hasDerivAt_canonicalOutput_scale_a (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ) :
    HasDerivAt (fun k : ℝ => (canonicalOutput h (k • K) 1).1)
      (firstOrderReturn h K 1 1) 0 := by
  have heq : (fun k : ℝ => (canonicalOutput h (k • K) 1).1) =
      (fun k : ℝ => readoutOperator 1 (NormedSpace.exp (hamiltonianCLM h + k • dissipativeCLM K))) := by
    funext k
    rw [canonicalOutput_fst_eq_readout, canonicalCLM_eq_add, dissipativeCLM_real_smul]
    simp [readoutOperator]
  rw [heq]
  exact hasDerivAt_readout_scale h K 1

theorem hasDerivAt_canonicalOutput_scale_b (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ) :
    HasDerivAt (fun k : ℝ => (canonicalOutput h (k • K) 1).2)
      (firstOrderReturn h K 1 (-1)) 0 := by
  have heq : (fun k : ℝ => (canonicalOutput h (k • K) 1).2) =
      (fun k : ℝ => readoutOperator (-1) (NormedSpace.exp (hamiltonianCLM h + k • dissipativeCLM K))) := by
    funext k
    rw [canonicalOutput_snd_eq_readout, canonicalCLM_eq_add, dissipativeCLM_real_smul]
    simp [readoutOperator]
  rw [heq]
  exact hasDerivAt_readout_scale h K (-1)

theorem hasDerivAt_probabilityA_swap (y : Parameters) (hw : y 0 = Real.pi) (hh : y 1 = 0) :
    HasDerivAt (fun k : ℝ => probabilityA (k, y)) (Swap.qa 0 (jumpDirection y)) 0 := by
  have heq : (fun k : ℝ => probabilityA (k, y)) =
      (fun k : ℝ => (canonicalOutput ![Swap.frequency 0, 0, 0]
        (k • singleK (jumpDirection y)) 1).1) := by
    funext k
    have he := congrArg Prod.fst (probability_eq_canonical (k, y))
    simpa [hamiltonianVector, kossakowskiMatrix, hw, hh, Swap.frequency_zero] using he
  rw [heq]
  simpa [SwapComparison.firstOrderReturn_single_a] using
    hasDerivAt_canonicalOutput_scale_a ![Swap.frequency 0, 0, 0] (singleK (jumpDirection y))

theorem hasDerivAt_probabilityB_swap (y : Parameters) (hw : y 0 = Real.pi) (hh : y 1 = 0) :
    HasDerivAt (fun k : ℝ => probabilityB (k, y)) (Swap.qb 0 (jumpDirection y)) 0 := by
  have heq : (fun k : ℝ => probabilityB (k, y)) =
      (fun k : ℝ => (canonicalOutput ![Swap.frequency 0, 0, 0]
        (k • singleK (jumpDirection y)) 1).2) := by
    funext k
    have he := congrArg Prod.snd (probability_eq_canonical (k, y))
    simpa [hamiltonianVector, kossakowskiMatrix, hw, hh, Swap.frequency_zero] using he
  rw [heq]
  simpa [SwapComparison.firstOrderReturn_single_b] using
    hasDerivAt_canonicalOutput_scale_b ![Swap.frequency 0, 0, 0] (singleK (jumpDirection y))

theorem scaleAtZero_swap (y : Parameters) (hw : y 0 = Real.pi) (hh : y 1 = 0) :
    scaleAtZero y = Swap.qa 0 (jumpDirection y) - y 2 * Swap.qb 0 (jumpDirection y) := by
  have hab := (hasDerivAt_probabilityA_swap y hw hh).sub
    ((hasDerivAt_probabilityB_swap y hw hh).const_mul (y 2))
  have hi : HasDerivAt (fun k : ℝ => (k, y)) (1, 0) 0 :=
    (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 y)
  have hj := (analytic_objective (0, y)).differentiableAt.hasFDerivAt.comp_hasDerivAt 0 hi
  exact hj.unique hab

#print axioms hasDerivAt_readout_scale
#print axioms hasDerivAt_canonicalOutput_scale_a
#print axioms hasDerivAt_canonicalOutput_scale_b
#print axioms hasDerivAt_probabilityA_swap
#print axioms hasDerivAt_probabilityB_swap
#print axioms scaleAtZero_swap

end TwoStateQuantumEmbedding.ActualSwapSystem
