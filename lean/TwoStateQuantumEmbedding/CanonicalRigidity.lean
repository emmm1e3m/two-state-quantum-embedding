import TwoStateQuantumEmbedding.Rigidity
import TwoStateQuantumEmbedding.AffineExponential
import TwoStateQuantumEmbedding.CanonicalBloch

/-! 将已证耗散刚性接到真实规范概率与任意有限 GKSL 概率。 -/
noncomputable section
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace TwoStateQuantumEmbedding.Rigidity
open GKSLAlgebra CanonicalBloch

/-- 直接使用已证增广指数下右块，不依赖后续偏置区间模块。 -/
private theorem canonical_sum (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ) :
    (canonicalOutput h K 1).1 + (canonicalOutput h K 1).2 =
      1 + (NormedSpace.exp (blochMatrix h K)) 2 2 := by
  have he := AffineExponential.affine_evolution_spatial
    (blochMatrix h K) (drift K) 1 2 2
  change canonicalEvolution h K 1 3 3 = _ at he
  simp only [one_smul] at he
  dsimp [canonicalOutput]
  rw [he]
  ring

/-- s 是两个实际规范输出概率之和；不再保留线性读出假设。 -/
theorem canonicalOutput_dissipative_rigidity
    (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ) (hK : K.PosSemidef)
    (s : ℝ) (hsread : s = (canonicalOutput h K 1).1 + (canonicalOutput h K 1).2)
    (hs : s ≤ 1 / 16) :
    K.trace.re ≤ -Real.log (1 - 4 * s) / 2 ∧
      -Real.log (1 - 4 * s) / 2 ≤ (8 / 3) * s := by
  apply bloch_dissipative_rigidity h K hK s _ hs
  rw [hsread, canonical_sum]

/-- 任意原始有限跳跃及 Hermitian Hamiltonian 的真实单位时间概率版本。 -/
theorem finiteOutput_dissipative_rigidity {n : ℕ}
    (H : QubitMatrix) (hH : H.IsHermitian) (A : Fin n → QubitMatrix)
    (s : ℝ) (hsread : s = (finiteOutput H A 1).1 + (finiteOutput H A 1).2)
    (hs : s ≤ 1 / 16) :
    (kossakowski (fun μ => pauliCoeffs (A μ))).trace.re ≤
      -Real.log (1 - 4 * s) / 2 ∧
      -Real.log (1 - 4 * s) / 2 ≤ (8 / 3) * s := by
  rw [finiteOutput_eq_canonicalOutput H hH A] at hsread
  exact canonicalOutput_dissipative_rigidity
    (hamiltonianVector (canonicalHamiltonian H A))
    (kossakowski (fun μ => pauliCoeffs (A μ))) (kossakowski_posSemidef _)
    s hsread hs

#print axioms canonicalOutput_dissipative_rigidity
#print axioms finiteOutput_dissipative_rigidity

end TwoStateQuantumEmbedding.Rigidity
