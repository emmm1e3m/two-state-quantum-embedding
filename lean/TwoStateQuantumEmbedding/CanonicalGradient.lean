import TwoStateQuantumEmbedding.ExponentialGradient
import TwoStateQuantumEmbedding.TraceGradient
import TwoStateQuantumEmbedding.PSDOptimality

/-! 实际规范输出的 Hamiltonian 梯度、Hermitian 实迹梯度和 PSD 法向。 -/
noncomputable section
open Matrix Complex
open scoped BigOperators Matrix.Norms.Operator Topology ComplexOrder

namespace TwoStateQuantumEmbedding.CanonicalGradient
open CanonicalBloch GKSLAlgebra ExponentialGradient TraceGradient
set_option backward.isDefEq.respectTransparency false

abbrev KMatrix := Matrix (Fin 3) (Fin 3) ℂ

def kDerivative (α β : ℝ) (p : Parameters) : KMatrix →L[ℝ] ℝ :=
  (canonicalScalarDerivative α β p).comp (ContinuousLinearMap.inr ℝ BlochVec KMatrix)

def hDerivative (α β : ℝ) (p : Parameters) : BlochVec →L[ℝ] ℝ :=
  (canonicalScalarDerivative α β p).comp (ContinuousLinearMap.inl ℝ BlochVec KMatrix)

def kGradient (α β : ℝ) (p : Parameters) : KMatrix :=
  hermitianGradient (kDerivative α β p)

def hGradient (α β : ℝ) (p : Parameters) : BlochVec :=
  fun i => hDerivative α β p (Pi.single i 1)

theorem kGradient_isHermitian (α β : ℝ) (p : Parameters) :
    (kGradient α β p).IsHermitian := hermitianGradient_isHermitian _

theorem kGradient_pairing (α β : ℝ) (p : Parameters) (W : KMatrix)
    (hW : W.IsHermitian) :
    kDerivative α β p W = (kGradient α β p * W).trace.re :=
  (hermitianGradient_pairing _ W hW).symm

theorem hGradient_pairing (α β : ℝ) (p : Parameters) (v : BlochVec) :
    hDerivative α β p v = ∑ i, hGradient α β p i * v i := by
  have hv : v = ∑ i : Fin 3, v i • Pi.single i (1 : ℝ) := by
    funext j
    simp [Fin.sum_univ_three]
    fin_cases j <;> simp
  calc
    hDerivative α β p v = hDerivative α β p (∑ i, v i • Pi.single i 1) :=
      congrArg (hDerivative α β p) hv
    _ = _ := by simp [hGradient, mul_comm]

/-- 完整真实导数分解为 Hamiltonian 坐标梯度与 Hermitian 实迹梯度。 -/
theorem canonicalScalarDerivative_pairing (α β : ℝ) (p : Parameters)
    (v : BlochVec) (W : KMatrix) (hW : W.IsHermitian) :
    canonicalScalarDerivative α β p (v, W) =
      (∑ i, hGradient α β p i * v i) + (kGradient α β p * W).trace.re := by
  have he : (v, W) = (v, (0 : KMatrix)) + ((0 : BlochVec), W) := by simp
  rw [he, map_add]
  exact congrArg₂ (· + ·) (hGradient_pairing α β p v) (kGradient_pairing α β p W hW)

/-- 固定 Hamiltonian，真实输出函数对整个复矩阵空间具有严格导数。 -/
theorem hasStrictFDerivAt_scalar_K (α β : ℝ) (h : BlochVec) (K : KMatrix) :
    HasStrictFDerivAt (fun W => canonicalScalar α β (h, W))
      (kDerivative α β (h, K)) K := by
  have hp : HasStrictFDerivAt (fun W : KMatrix => (h, W))
      (ContinuousLinearMap.inr ℝ BlochVec KMatrix) K := by
    exact (hasStrictFDerivAt_const h K).prodMk (hasStrictFDerivAt_id K)
  exact (hasStrictFDerivAt_canonicalScalar α β (h, K)).comp K hp

theorem hasStrictFDerivAt_a_K (h : BlochVec) (K : KMatrix) :
    HasStrictFDerivAt (fun W => (canonicalOutput h W 1).1)
      (kDerivative (1/2) (1/2) (h, K)) K := by
  have hp : HasStrictFDerivAt (fun W : KMatrix => (h, W))
      (ContinuousLinearMap.inr ℝ BlochVec KMatrix) K := by
    exact (hasStrictFDerivAt_const h K).prodMk (hasStrictFDerivAt_id K)
  exact (hasStrictFDerivAt_canonical_a (h, K)).comp K hp

theorem hasStrictFDerivAt_b_K (h : BlochVec) (K : KMatrix) :
    HasStrictFDerivAt (fun W => (canonicalOutput h W 1).2)
      (kDerivative (1/2) (-1/2) (h, K)) K := by
  have hp : HasStrictFDerivAt (fun W : KMatrix => (h, W))
      (ContinuousLinearMap.inr ℝ BlochVec KMatrix) K := by
    exact (hasStrictFDerivAt_const h K).prodMk (hasStrictFDerivAt_id K)
  exact (hasStrictFDerivAt_canonical_b (h, K)).comp K hp

/-- 对实际 a 在固定 b 下的 PSD 局部极小，法向及互补性由真实导数推出。 -/
theorem canonical_psd_normal_of_localMin (h : BlochVec) (K : KMatrix)
    (hK : K.PosSemidef)
    (hreg : kDerivative (1/2) (-1/2) (h, K) K ≠ 0)
    (hmin : IsLocalMinOn (fun W => (canonicalOutput h W 1).1)
      {W | W.PosSemidef ∧ (canonicalOutput h W 1).2 = (canonicalOutput h K 1).2} K) :
    let μ := kDerivative (1/2) (1/2) (h, K) K /
      kDerivative (1/2) (-1/2) (h, K) K
    let S := kGradient (1/2) (1/2) (h, K) - μ • kGradient (1/2) (-1/2) (h, K)
    S.PosSemidef ∧ (S * K).trace.re = 0 ∧ S * K = 0 := by
  exact PSDOptimality.psd_normal_of_localMin hK
    (kGradient_isHermitian _ _ _) (kGradient_isHermitian _ _ _)
    (hasStrictFDerivAt_a_K h K).hasFDerivAt (hasStrictFDerivAt_b_K h K)
    (kGradient_pairing _ _ _) (kGradient_pairing _ _ _) hreg hmin

#print axioms canonicalScalarDerivative_pairing
#print axioms canonical_psd_normal_of_localMin
end TwoStateQuantumEmbedding.CanonicalGradient
