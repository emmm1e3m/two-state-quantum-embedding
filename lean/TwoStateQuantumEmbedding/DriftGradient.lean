import TwoStateQuantumEmbedding.ExponentialGradient

/-! 实际增广生成元的漂移方向导数。 -/
noncomputable section
open NormedSpace MeasureTheory Matrix
open scoped Topology Interval Matrix.Norms.Operator

namespace TwoStateQuantumEmbedding.DriftGradient
open CanonicalBloch GKSLAlgebra ExponentialGradient
set_option backward.isDefEq.respectTransparency false

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄]

/-- 左因子消灭生成元时，也消灭指数的所有非零次项。 -/
theorem mul_exp_of_mul_zero (B Q : 𝔄) (hBQ : B * Q = 0) : B * exp Q = B := by
  let L := ContinuousLinearMap.mul ℝ 𝔄 B
  have hs := (exp_series_hasSum_exp' (𝕂 := ℝ) Q).map L.toAddMonoidHom L.continuous
  have hz : ∀ k : ℕ, k ≠ 0 → B * Q^k = 0 := by
    intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    rw [pow_succ', ← mul_assoc, hBQ, zero_mul]
  change HasSum (fun k : ℕ => L ((k.factorial : ℝ)⁻¹ • Q^k)) (B * exp Q) at hs
  have hs' : HasSum (fun k : ℕ => if k = 0 then B else 0) (B * exp Q) := by
    convert hs using 1
    funext k
    by_cases hk : k = 0
    · subst k; simp [L]
    · simp [L, hk, hz k hk]
  exact hs'.unique (hasSum_ite_eq 0 B)

def ambientGenerator (M : Matrix (Fin 3) (Fin 3) ℝ) (c : BlochVec) : AugmentedMatrix :=
  !![0, 0, 0, 0;
     c 0, M 0 0, M 0 1, M 0 2;
     c 1, M 1 0, M 1 1, M 1 2;
     c 2, M 2 0, M 2 1, M 2 2]

def driftInsertion (d : BlochVec) : AugmentedMatrix := ambientGenerator 0 d

theorem ambientGenerator_canonical (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ) :
    ambientGenerator (blochMatrix h K) (drift K) = augmentedGenerator h K := rfl

theorem ambientGenerator_head (M : Matrix (Fin 3) (Fin 3) ℝ) (c : BlochVec)
    (j : Fin 4) : ambientGenerator M c 0 j = 0 := by
  fin_cases j <;> rfl

theorem ambientGenerator_spatial (M : Matrix (Fin 3) (Fin 3) ℝ) (c : BlochVec)
    (i j : Fin 3) : ambientGenerator M c i.succ j.succ = M i j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem ambientGenerator_pow_spatial (M : Matrix (Fin 3) (Fin 3) ℝ) (c : BlochVec)
    (k : ℕ) (i j : Fin 3) : (ambientGenerator M c ^ k) i.succ j.succ = (M^k) i j := by
  induction k generalizing i j with
  | zero => simp only [pow_zero, Matrix.one_apply, Fin.succ_inj]
  | succ k ih =>
    simp only [pow_succ, Matrix.mul_apply]
    rw [Fin.sum_univ_succ]
    simp only [ambientGenerator_head, mul_zero, zero_add, ambientGenerator_spatial]
    apply Finset.sum_congr rfl
    intro l _
    rw [ih]

/-- 增广指数的空间块恰为原始 3×3 矩阵指数，未假设耗散或可逆性。 -/
theorem exp_ambientGenerator_spatial (M : Matrix (Fin 3) (Fin 3) ℝ) (c : BlochVec)
    (i j : Fin 3) : exp (ambientGenerator M c) i.succ j.succ = exp M i j := by
  let L := matrixEntryCLM i.succ j.succ
  let R := matrixEntryCLM i j
  have hq := (exp_series_hasSum_exp' (𝕂 := ℝ) (ambientGenerator M c)).map
    L.toAddMonoidHom L.continuous
  have hm := (exp_series_hasSum_exp' (𝕂 := ℝ) M).map R.toAddMonoidHom R.continuous
  apply hq.unique
  convert hm using 1
  · funext k
    change (k.factorial : ℝ)⁻¹ * (ambientGenerator M c ^ k) i.succ j.succ =
      (k.factorial : ℝ)⁻¹ * (M^k) i j
    rw [ambientGenerator_pow_spatial]
  · rfl

theorem ambientGenerator_smul (M : Matrix (Fin 3) (Fin 3) ℝ) (c : BlochVec) (r : ℝ) :
    ambientGenerator (r • M) (r • c) = r • ambientGenerator M c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ambientGenerator, Matrix.smul_apply, smul_eq_mul]

theorem exp_smul_ambientGenerator_spatial (M : Matrix (Fin 3) (Fin 3) ℝ)
    (c : BlochVec) (r : ℝ) (i j : Fin 3) :
    exp (r • ambientGenerator M c) i.succ j.succ = exp (r • M) i j := by
  rw [← ambientGenerator_smul, exp_ambientGenerator_spatial]

theorem driftInsertion_mul (Q : AugmentedMatrix) (d : BlochVec)
    (hQ : ∀ j, Q 0 j = 0) : driftInsertion d * Q = 0 := by
  ext i j
  fin_cases i <;>
    simp [driftInsertion, ambientGenerator, Matrix.mul_apply, Fin.sum_univ_succ,
      hQ, Matrix.zero_apply]

/-- 独立漂移方向的 Duhamel 核只剩一个传播子。 -/
theorem expDerivative_driftInsertion (Q : AugmentedMatrix) (d : BlochVec)
    (hQ : ∀ j, Q 0 j = 0) :
    expDerivative Q (driftInsertion d) =
      ∫ s in (0 : ℝ)..1, exp ((1-s) • Q) * driftInsertion d := by
  rw [expDerivative_apply]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [Matrix.mul_assoc, mul_exp_of_mul_zero]
  rw [mul_smul_comm, driftInsertion_mul Q d hQ, smul_zero]

/-- 增广漂移方向的严格线性映射。 -/
def driftInsertionCLM : BlochVec →L[ℝ] AugmentedMatrix :=
  LinearMap.toContinuousLinearMap {
    toFun := driftInsertion
    map_add' := by
      intro d e
      ext i j
      fin_cases i <;> fin_cases j <;> simp [driftInsertion, ambientGenerator]
    map_smul' := by
      intro r d
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [driftInsertion, ambientGenerator, Matrix.smul_apply, smul_eq_mul]
  }

theorem hasStrictFDerivAt_ambientGenerator_c (M : Matrix (Fin 3) (Fin 3) ℝ)
    (c : BlochVec) :
    HasStrictFDerivAt (ambientGenerator M) driftInsertionCLM c := by
  have he : ambientGenerator M =
      (fun d => driftInsertionCLM d + ambientGenerator M 0) := by
    funext d
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [driftInsertionCLM, driftInsertion, ambientGenerator]
  rw [he]
  exact driftInsertionCLM.hasStrictFDerivAt.add_const _

def ambientZ (M : Matrix (Fin 3) (Fin 3) ℝ) (c : BlochVec) : ℝ :=
  exp (ambientGenerator M c) 3 0

def ambientZDerivative (M : Matrix (Fin 3) (Fin 3) ℝ) (c : BlochVec) : BlochVec →L[ℝ] ℝ :=
  (measurementCLM 0 1).comp ((expDerivative (ambientGenerator M c)).comp driftInsertionCLM)

theorem hasStrictFDerivAt_ambientZ_c (M : Matrix (Fin 3) (Fin 3) ℝ) (c : BlochVec) :
    HasStrictFDerivAt (ambientZ M) (ambientZDerivative M c) c := by
  have he : ambientZ M = (fun d => measurementCLM 0 1 (exp (ambientGenerator M d))) := by
    funext d
    simp [ambientZ, measurementCLM]
  rw [he]
  exact (measurementCLM 0 1).hasStrictFDerivAt.comp c
    ((hasStrictFDerivAt_exp_integral _).comp c (hasStrictFDerivAt_ambientGenerator_c M c))

/-- 实际漂移导数的可计算积分，不以未知导数作为前提。 -/
theorem ambientZDerivative_apply (M : Matrix (Fin 3) (Fin 3) ℝ) (c d : BlochVec) :
    ambientZDerivative M c d =
      ∫ s in (0 : ℝ)..1,
        exp ((1-s) • ambientGenerator M c) 3 1 * d 0 +
        exp ((1-s) • ambientGenerator M c) 3 2 * d 1 +
        exp ((1-s) • ambientGenerator M c) 3 3 * d 2 := by
  change measurementCLM 0 1 (expDerivative (ambientGenerator M c) (driftInsertion d)) = _
  rw [expDerivative_driftInsertion _ d (ambientGenerator_head M c)]
  have hc : Continuous (fun s : ℝ => exp ((1-s) • ambientGenerator M c) * driftInsertion d) := by
    exact (((differentiable_exp_smul_const ℝ _).continuous.comp
      (continuous_const.sub continuous_id)).mul continuous_const)
  rw [← (measurementCLM 0 1).intervalIntegral_comp_comm (hc.intervalIntegrable 0 1)]
  apply intervalIntegral.integral_congr
  intro s _
  simp [measurementCLM, Matrix.mul_apply, Fin.sum_univ_succ,
    driftInsertion, ambientGenerator]
  ring

theorem ambientZ_canonical (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ) :
    ambientZ (blochMatrix h K) (drift K) =
      (canonicalOutput h K 1).1 - (canonicalOutput h K 1).2 := by
  rw [canonicalOutput_sub]
  simp [ambientZ, ambientGenerator_canonical, canonicalEvolution]

/-- 漂移导数还原到实际 Bloch 传播子 exp(tM)，因此不依赖 c。 -/
theorem ambientZDerivative_bloch (M : Matrix (Fin 3) (Fin 3) ℝ) (c d : BlochVec) :
    ambientZDerivative M c d =
      ∫ s in (0 : ℝ)..1,
        exp ((1-s) • M) 2 0 * d 0 +
        exp ((1-s) • M) 2 1 * d 1 +
        exp ((1-s) • M) 2 2 * d 2 := by
  rw [ambientZDerivative_apply]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  exact congrArg₂ (· + ·)
    (congrArg₂ (· + ·)
      (congrArg (fun r : ℝ => r * d 0) (exp_smul_ambientGenerator_spatial M c (1-s) 2 0))
      (congrArg (fun r : ℝ => r * d 1) (exp_smul_ambientGenerator_spatial M c (1-s) 2 1)))
    (congrArg (fun r : ℝ => r * d 2) (exp_smul_ambientGenerator_spatial M c (1-s) 2 2))

def ambientX (M : Matrix (Fin 3) (Fin 3) ℝ) (c : BlochVec) : ℝ :=
  exp (ambientGenerator M c) 3 3

theorem ambientX_eq (M : Matrix (Fin 3) (Fin 3) ℝ) (c : BlochVec) :
    ambientX M c = exp M 2 2 := exp_ambientGenerator_spatial M c 2 2

theorem ambientX_canonical (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ) :
    ambientX (blochMatrix h K) (drift K) =
      (canonicalOutput h K 1).1 + (canonicalOutput h K 1).2 - 1 := by
  rw [canonicalOutput_sum_sub_one]
  simp [ambientX, ambientGenerator_canonical, canonicalEvolution]

/-- 对实际环境输出 x，方向 exp(-M) 的导数严格等于 1。 -/
theorem fderiv_ambientX_exp_neg (M : Matrix (Fin 3) (Fin 3) ℝ) (c : BlochVec) :
    fderiv ℝ (fun A => ambientX A c) M (exp (-M)) = 1 := by
  simp_rw [ambientX_eq]
  exact fderiv_exp_diagonal_exp_neg M 2

/-- 方向 δc=M e_z 给出 z 的导数 x-1，直接提供非零漂移方向。 -/
theorem ambientZDerivative_column (M : Matrix (Fin 3) (Fin 3) ℝ) (c : BlochVec) :
    ambientZDerivative M c (fun i => M i 2) = ambientX M c - 1 := by
  have ht : (∫ s in (0 : ℝ)..1, exp (s • M) * M) = exp M - 1 := by
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := 1) (fun s _ => hasDerivAt_exp_smul_const M s)
      (((differentiable_exp_smul_const ℝ M).continuous.mul continuous_const).intervalIntegrable 0 1)
    simpa using hi
  have hs : (∫ s in (0 : ℝ)..1, exp ((1-s) • M) * M) = exp M - 1 := by
    calc
      _ = ∫ s in (0 : ℝ)..1, exp (s • M) * M := by
        simpa using intervalIntegral.integral_comp_sub_left
          (fun s : ℝ => exp (s • M) * M) (a := (0 : ℝ)) (b := 1) 1
      _ = _ := ht
  have hc : Continuous (fun s : ℝ => exp ((1-s) • M) * M) :=
    ((differentiable_exp_smul_const ℝ M).continuous.comp
      (continuous_const.sub continuous_id)).mul continuous_const
  rw [ambientZDerivative_bloch, ambientX_eq]
  calc
    _ = ∫ s in (0 : ℝ)..1, matrixEntryCLM 2 2 (exp ((1-s) • M) * M) := by
      apply intervalIntegral.integral_congr
      intro s _
      simp [matrixEntryCLM, Matrix.mul_apply, Fin.sum_univ_three]
    _ = matrixEntryCLM 2 2 (∫ s in (0 : ℝ)..1, exp ((1-s) • M) * M) :=
      (matrixEntryCLM 2 2).intervalIntegral_comp_comm (hc.intervalIntegrable 0 1)
    _ = _ := by rw [hs]; simp [matrixEntryCLM]

theorem ambientZDerivative_ne_zero_of_x_ne_one
    (M : Matrix (Fin 3) (Fin 3) ℝ) (c : BlochVec) (hx : ambientX M c ≠ 1) :
    ambientZDerivative M c ≠ 0 := by
  intro hz
  have hv := ambientZDerivative_column M c
  rw [hz] at hv
  simp only [_root_.zero_apply] at hv
  exact hx (by linarith)

#print axioms hasStrictFDerivAt_ambientZ_c
#print axioms ambientZDerivative_apply
#print axioms ambientZ_canonical
#print axioms ambientZDerivative_bloch
#print axioms fderiv_ambientX_exp_neg
#print axioms ambientZDerivative_column
#print axioms ambientZDerivative_ne_zero_of_x_ne_one

end TwoStateQuantumEmbedding.DriftGradient
