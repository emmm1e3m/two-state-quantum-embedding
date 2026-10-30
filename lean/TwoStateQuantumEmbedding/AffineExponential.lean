import TwoStateQuantumEmbedding.Duhamel
import TwoStateQuantumEmbedding.GeneralGeometry

noncomputable section
open Matrix NormedSpace MeasureTheory
open scoped Matrix.Norms.Operator Interval

namespace TwoStateQuantumEmbedding.AffineExponential

set_option maxRecDepth 3000
set_option maxHeartbeats 1500000

abbrev V3 := Fin 3 → ℝ
abbrev M3 := Matrix (Fin 3) (Fin 3) ℝ
abbrev M4 := Matrix (Fin 4) (Fin 4) ℝ

section Entries
variable {n : Type*} [Fintype n] [DecidableEq n]

def entryCLM (i j : n) : Matrix n n ℝ →L[ℝ] ℝ :=
  (show Matrix n n ℝ →ₗ[ℝ] ℝ from
    { toFun := fun A => A i j
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }).toContinuousLinearMap

theorem exp_entry_series (A : Matrix n n ℝ) (i j : n) :
    (exp A) i j = ∑' k : ℕ, (Nat.factorial k : ℝ)⁻¹ * (A^k) i j := by
  have hs := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A
  have he := (entryCLM i j).hasSum hs
  change HasSum (fun k : ℕ => (Nat.factorial k : ℝ)⁻¹ * (A^k) i j) ((exp A) i j) at he
  exact he.tsum_eq.symm

theorem pow_succ_zero_row (A : Matrix n n ℝ) (i : n)
    (hA : ∀ j, A i j = 0) (k : ℕ) (j : n) : (A^(k+1)) i j = 0 := by
  rw [pow_succ', Matrix.mul_apply]
  simp [hA]

theorem exp_zero_row (A : Matrix n n ℝ) (i : n)
    (hA : ∀ j, A i j = 0) (j : n) : (exp A) i j = (1 : Matrix n n ℝ) i j := by
  rw [exp_entry_series]
  rw [tsum_eq_single 0]
  · simp
  · intro k hk
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    simp [pow_succ_zero_row A i hA]

theorem exp_entry_hasDerivAt (A : Matrix n n ℝ) (i j : n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (exp (s • A)) i j) ((exp (t • A)*A) i j) t := by
  exact (entryCLM i j).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const A t)

end Entries

def affineGenerator (M : M3) (c : V3) : M4 :=
  !![0, 0, 0, 0;
     c 0, M 0 0, M 0 1, M 0 2;
     c 1, M 1 0, M 1 1, M 1 2;
     c 2, M 2 0, M 2 1, M 2 2]

@[simp] theorem affineGenerator_head (M : M3) (c : V3) (j : Fin 4) :
    affineGenerator M c 0 j = 0 := by fin_cases j <;> rfl

@[simp] theorem affineGenerator_spatial (M : M3) (c : V3) (i j : Fin 3) :
    affineGenerator M c i.succ j.succ = M i j := by
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem affineGenerator_drift (M : M3) (c : V3) (i : Fin 3) :
    affineGenerator M c i.succ 0 = c i := by fin_cases i <;> rfl

theorem affineGenerator_smul (M : M3) (c : V3) (t : ℝ) :
    affineGenerator (t • M) (t • c) = t • affineGenerator M c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [affineGenerator]

theorem affine_pow_spatial (M : M3) (c : V3) (k : ℕ) (i j : Fin 3) :
    (affineGenerator M c ^ k) i.succ j.succ = (M^k) i j := by
  induction k generalizing i j with
  | zero => simp [Matrix.one_apply]
  | succ k ih =>
    rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
    simp only [Fin.sum_univ_succ, affineGenerator_head, affineGenerator_spatial,
      mul_zero, zero_add]
    simp only [ih]

theorem affine_exp_spatial (M : M3) (c : V3) (i j : Fin 3) :
    (exp (affineGenerator M c)) i.succ j.succ = (exp M) i j := by
  rw [exp_entry_series, exp_entry_series]
  apply tsum_congr
  intro k
  rw [affine_pow_spatial]

theorem affine_evolution_spatial (M : M3) (c : V3) (t : ℝ) (i j : Fin 3) :
    (exp (t • affineGenerator M c)) i.succ j.succ = (exp (t • M)) i j := by
  rw [← affineGenerator_smul, affine_exp_spatial]

theorem affine_evolution_head (M : M3) (c : V3) (t : ℝ) (j : Fin 4) :
    (exp (t • affineGenerator M c)) 0 j = if j = 0 then 1 else 0 := by
  rw [exp_zero_row (t • affineGenerator M c) 0 (by intro j; simp)]
  simp [Matrix.one_apply, eq_comm]

def mulVecCLM (c : V3) : M3 →L[ℝ] V3 :=
  (show M3 →ₗ[ℝ] V3 from
    { toFun := fun A => A *ᵥ c
      map_add' := by intros; apply Matrix.add_mulVec
      map_smul' := by intros; apply Matrix.smul_mulVec }).toContinuousLinearMap

theorem affine_drift_hasDerivAt (M : M3) (c : V3) (i : Fin 3) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (exp (s • affineGenerator M c)) i.succ 0)
      ((exp (t • M) *ᵥ c) i) t := by
  have hd := exp_entry_hasDerivAt (affineGenerator M c) i.succ 0 t
  convert hd using 1
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ, affineGenerator_head, affineGenerator_drift,
    affine_evolution_spatial, mul_zero, zero_add]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem affine_drift_eq_integral (M : M3) (c : V3) (i : Fin 3) (t : ℝ) :
    (exp (t • affineGenerator M c)) i.succ 0 =
      ∫ s in (0 : ℝ)..t, (exp (s • M) *ᵥ c) i := by
  have hc : Continuous (fun s : ℝ => (exp (s • M) *ᵥ c) i) :=
    (continuous_apply i).comp ((mulVecCLM c).continuous.comp
      (differentiable_exp_smul_const ℝ M).continuous)
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := t)
    (fun s _ => affine_drift_hasDerivAt M c i s) (hc.intervalIntegrable 0 t)
  simpa [NormedSpace.exp_zero, Matrix.one_apply] using hf.symm

def integratedPropagator (M : M3) (t : ℝ) : M3 :=
  ∫ s in (0 : ℝ)..t, exp (s • M)

theorem affine_drift_eq_integrated_mulVec (M : M3) (c : V3) (i : Fin 3) (t : ℝ) :
    (exp (t • affineGenerator M c)) i.succ 0 =
      (integratedPropagator M t *ᵥ c) i := by
  rw [affine_drift_eq_integral]
  have hi := ((ContinuousLinearMap.proj i).comp (mulVecCLM c)).intervalIntegral_comp_comm
    (μ := volume) ((differentiable_exp_smul_const ℝ M).continuous.intervalIntegrable 0 t)
  exact hi

def biasFunctional (M : M3) : V3 := fun j => integratedPropagator M 1 2 j

theorem affine_terminal_bias (M : M3) (c : V3) :
    (exp (affineGenerator M c)) 3 0 = biasFunctional M ⬝ᵥ c := by
  simpa [biasFunctional, Matrix.mulVec, dotProduct] using
    affine_drift_eq_integrated_mulVec M c 2 1

#print axioms exp_zero_row
#print axioms affine_evolution_spatial
#print axioms affine_evolution_head
#print axioms affine_drift_eq_integral
#print axioms affine_drift_eq_integrated_mulVec
#print axioms affine_terminal_bias

end TwoStateQuantumEmbedding.AffineExponential


