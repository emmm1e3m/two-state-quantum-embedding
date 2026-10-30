import TwoStateQuantumEmbedding.CanonicalBias

/-! 固定实部的显式最优漂移；奇异实部无需取逆。 -/
noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder

namespace TwoStateQuantumEmbedding.OptimalDrift
open TwoState.GeneralGeometry CanonicalBias

def endpoint (S : M3) (l : V3) (sign : ℝ) : V3 :=
  (sign * 4 / Real.sqrt (l ⬝ᵥ (S.adjugate *ᵥ l))) • (S.adjugate *ᵥ l)

theorem endpoint_posSemidef (S : M3) (hS : S.PosSemidef) (l : V3)
    (hq : 0 < l ⬝ᵥ (S.adjugate *ᵥ l)) (sign : ℝ) (hsign : |sign| ≤ 1) :
    (physicalCanonical S (endpoint S l sign)).PosSemidef := by
  let A := CFC.sqrt S.adjugate
  let q := l ⬝ᵥ (S.adjugate *ᵥ l)
  have hqpos : 0 < q := hq
  have hr : Real.sqrt q ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hqpos)
  have hr2 : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hqpos.le
  have hA : A.transpose = A := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      ((CFC.sqrt_nonneg S.adjugate).posSemidef : A.PosSemidef).isHermitian.eq
  have hnorm : (A *ᵥ l) ⬝ᵥ (A *ᵥ l) = q := by
    have hh := sqrt_adjugate_dot S hS l
    change (A.transpose *ᵥ l) ⬝ᵥ (A.transpose *ᵥ l) = q at hh
    rw [hA] at hh
    exact hh
  have hsq : A * A = S.adjugate :=
    CFC.sqrt_mul_sqrt_self S.adjugate (adjugate_posSemidef S hS).nonneg
  apply (physicalCanonical_posSemidef_iff_ball S hS _).2
  refine ⟨(sign / Real.sqrt q) • (A *ᵥ l), ?_, ?_⟩
  · rw [dotProduct_smul, smul_dotProduct, hnorm]
    simp only [smul_eq_mul]
    have he : sign / Real.sqrt q * (sign / Real.sqrt q * q) = sign ^ 2 := by
      field_simp
      nlinarith [sq_nonneg sign]
    rw [he]
    have hs := abs_le.mp hsign
    nlinarith
  · change endpoint S l sign = 4 • (A *ᵥ ((sign / Real.sqrt q) • (A *ᵥ l)))
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hsq, smul_smul]
    unfold endpoint
    congr 1
    dsimp [q]
    ring

theorem endpoint_bias (S : M3) (l : V3)
    (hq : 0 < l ⬝ᵥ (S.adjugate *ᵥ l)) (sign : ℝ) :
    l ⬝ᵥ endpoint S l sign =
      sign * 4 * Real.sqrt (l ⬝ᵥ (S.adjugate *ᵥ l)) := by
  unfold endpoint
  rw [dotProduct_smul]
  simp only [smul_eq_mul]
  have hq2 := Real.mul_self_sqrt hq.le
  have hr := ne_of_gt (Real.sqrt_pos.2 hq)
  nth_rw 2 [← hq2]
  field_simp

theorem explicit_endpoint_output (h : GKSLAlgebra.BlochVec) (S : M3)
    (hS : S.PosSemidef) (hZ : 0 < fixedZ h S) (sign : ℝ) (hsign : |sign| ≤ 1) :
    let c := endpoint S (AffineExponential.biasFunctional (fixedMatrix h S)) sign
    (physicalCanonical S c).PosSemidef ∧
      CanonicalBloch.canonicalOutput h (physicalCanonical S c) 1 =
        outputFromXZ (fixedX h S) (sign * fixedZ h S) := by
  have hq : 0 < AffineExponential.biasFunctional (fixedMatrix h S) ⬝ᵥ
      (S.adjugate *ᵥ AffineExponential.biasFunctional (fixedMatrix h S)) := by
    have hs : 0 < Real.sqrt (AffineExponential.biasFunctional (fixedMatrix h S) ⬝ᵥ
        (S.adjugate *ᵥ AffineExponential.biasFunctional (fixedMatrix h S))) := by
      unfold fixedZ at hZ
      linarith
    exact Real.sqrt_pos.mp hs
  refine ⟨endpoint_posSemidef S hS _ hq sign hsign, ?_⟩
  rw [canonicalOutput_physical, endpoint_bias S _ hq sign]
  congr 1
  unfold fixedZ
  ring

#print axioms endpoint_posSemidef
#print axioms endpoint_bias
#print axioms explicit_endpoint_output

end TwoStateQuantumEmbedding.OptimalDrift
