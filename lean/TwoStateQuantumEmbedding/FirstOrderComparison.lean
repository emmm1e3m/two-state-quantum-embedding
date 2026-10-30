import TwoStateQuantumEmbedding.FirstOrderBridge

noncomputable section
open Matrix Complex NormedSpace MeasureTheory
open scoped Interval ComplexOrder Matrix.Norms.L2Operator
namespace TwoStateQuantumEmbedding.SwapComparison
open GKSLAlgebra CanonicalBloch GKSLBounds
set_option maxHeartbeats 1200000

@[simp] theorem exp_hamiltonianCLM_head (h : BlochVec) (t : ℝ) (x : AugmentedSpace) :
    ((exp (t • hamiltonianCLM h)) x).1=x.1 := by
  have he := congrFun (augmentedCoords_exp_canonical h 0 t x) 0
  rw [← hamiltonianCLM_eq_canonical] at he
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, augmentedCoords,
    canonicalEvolution_head, Matrix.one_apply] using he

def firstOrderKernel (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ) (t : ℝ) :
    AugmentedSpace →L[ℝ] AugmentedSpace :=
  exp ((1-t) • hamiltonianCLM h)*dissipativeCLM K*exp (t • hamiltonianCLM h)

@[simp] theorem firstOrderKernel_head (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ)
    (t : ℝ) (x : AugmentedSpace) : (firstOrderKernel h K t x).1=0 := by
  simp [firstOrderKernel, mul_apply_eq_comp]

theorem continuous_firstOrderKernel_readout (h : BlochVec)
    (K : Matrix (Fin 3) (Fin 3) ℂ) (s : ℝ) :
    Continuous (fun t : ℝ => diagonalReadout s (firstOrderKernel h K t (basisInitial s))) := by
  let L : (AugmentedSpace →L[ℝ] AugmentedSpace) →L[ℝ] ℝ :=
    (diagonalReadout s).comp (ContinuousLinearMap.apply ℝ AugmentedSpace (basisInitial s))
  exact L.continuous.comp (continuous_duhamel_kernel (hamiltonianCLM h)
    (hamiltonianCLM h) (dissipativeCLM K) 1)

theorem norm_firstOrderKernel_sub_le (h g : BlochVec)
    (K : Matrix (Fin 3) (Fin 3) ℂ) (hK : K.PosSemidef) (ε : ℝ) (hε : 0≤ε)
    (hclose : ∀ t∈Set.Icc (0:ℝ) 1,
      ‖exp (t • hamiltonianCLM h)-exp (t • hamiltonianCLM g)‖≤ε)
    (t : ℝ) (ht : t∈Set.Icc (0:ℝ) 1) :
    ‖firstOrderKernel h K t-firstOrderKernel g K t‖≤8*dissipationSize K*ε := by
  let L := exp ((1-t) • hamiltonianCLM h)
  let L' := exp ((1-t) • hamiltonianCLM g)
  let R := exp (t • hamiltonianCLM h)
  let R' := exp (t • hamiltonianCLM g)
  let D := dissipativeCLM K
  have hD : ‖D‖≤4*dissipationSize K := norm_dissipativeCLM_le K hK
  have hd := dissipationSize_nonneg K hK
  have hL : ‖L'‖≤1 := norm_exp_hamiltonianCLM_le g (by linarith [ht.2])
  have hR : ‖R‖≤1 := norm_exp_hamiltonianCLM_le h ht.1
  have hdL : ‖L-L'‖≤ε := hclose (1-t) ⟨by linarith [ht.2],by linarith [ht.1]⟩
  have hdR : ‖R-R'‖≤ε := hclose t ht
  have hid : L*D*R-L'*D*R'=(L-L')*D*R+L'*D*(R-R') := by
    rw [sub_mul, sub_mul, mul_sub]
    abel
  change ‖L*D*R-L'*D*R'‖≤_
  rw [hid]
  calc
    ‖(L-L')*D*R+L'*D*(R-R')‖ ≤ ‖(L-L')*D*R‖+‖L'*D*(R-R')‖ := norm_add_le _ _
    _ ≤ (‖L-L'‖*‖D‖)*‖R‖+(‖L'‖*‖D‖)*‖R-R'‖ := by
      apply add_le_add
      · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (ε*(4*dissipationSize K))*1+(1*(4*dissipationSize K))*ε := by gcongr
    _ = 8*dissipationSize K*ε := by ring

/-- 真正首阶概率的统一扰动界；迹零读出保留必要的二分之一。 -/
theorem firstOrderReturn_comparison_le (h g : BlochVec)
    (K : Matrix (Fin 3) (Fin 3) ℂ) (hK : K.PosSemidef) (ε : ℝ) (hε : 0≤ε)
    (hclose : ∀ t∈Set.Icc (0:ℝ) 1,
      ‖exp (t • hamiltonianCLM h)-exp (t • hamiltonianCLM g)‖≤ε)
    (s : ℝ) (hs : |s|≤1) :
    |firstOrderReturn h K 1 s-firstOrderReturn g K 1 s|≤4*dissipationSize K*ε := by
  have hrepr (u : BlochVec) : firstOrderReturn u K 1 s =
      ∫ t in (0:ℝ)..1, diagonalReadout s (firstOrderKernel u K t (basisInitial s)) := by
    rw [firstOrderReturn_eq_integral]
    rfl
  rw [hrepr h, hrepr g, ← intervalIntegral.integral_sub
    ((continuous_firstOrderKernel_readout h K s).intervalIntegrable 0 1)
    ((continuous_firstOrderKernel_readout g K s).intervalIntegrable 0 1)]
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=(0:ℝ)) (b:=1) (C:=4*dissipationSize K*ε)
    (f:=fun t => diagonalReadout s (firstOrderKernel h K t (basisInitial s))-
      diagonalReadout s (firstOrderKernel g K t (basisInitial s))) ?_
  · simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using hn
  intro t ht
  have ht' : t∈Set.Icc (0:ℝ) 1 := by
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ)≤1)] at ht
    exact ⟨ht.1.le,ht.2⟩
  let T := firstOrderKernel h K t-firstOrderKernel g K t
  have hhead : (T (basisInitial s)).1=0 := by simp [T]
  have hr := abs_diagonalReadout_trace_zero_le s hs (T (basisInitial s)) hhead
  have hnorm := norm_firstOrderKernel_sub_le h g K hK ε hε hclose t ht'
  have he : ‖T (basisInitial s)‖≤8*dissipationSize K*ε := by
    calc
      ‖T (basisInitial s)‖≤‖T‖*‖basisInitial s‖ := T.le_opNorm _
      _ ≤ ‖T‖*1 := mul_le_mul_of_nonneg_left (norm_basisInitial_le s hs) (norm_nonneg _)
      _ ≤ 8*dissipationSize K*ε := by simpa only [mul_one] using hnorm
  change |diagonalReadout s (firstOrderKernel h K t (basisInitial s))-
    diagonalReadout s (firstOrderKernel g K t (basisInitial s))|≤_
  have heq : diagonalReadout s (T (basisInitial s))=
      diagonalReadout s (firstOrderKernel h K t (basisInitial s))-
      diagonalReadout s (firstOrderKernel g K t (basisInitial s)) := by
    change diagonalReadout s (_-_)=_
    exact map_sub (diagonalReadout s) _ _
  rw [heq] at hr
  linarith

#print axioms firstOrderReturn_comparison_le
end TwoStateQuantumEmbedding.SwapComparison

