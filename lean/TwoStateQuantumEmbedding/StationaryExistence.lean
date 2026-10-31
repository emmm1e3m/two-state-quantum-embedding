import TwoStateQuantumEmbedding.CPTP
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! 任意有限 GKSL 生成元的密度稳态存在性。证明使用紧凸像的严格分离和轨道的右导数。 -/

noncomputable section
open Matrix Complex Set Filter
open scoped BigOperators Matrix.Norms.Operator ComplexOrder Topology

namespace TwoStateQuantumEmbedding

/-- 紧凸不变集合上的线性向量场必在该集合内有零点。只要求原点处的轨道导数。 -/
theorem exists_zero_of_compact_convex_invariant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (L : E →L[ℝ] E) (γ : E → ℝ → E)
    (hzero : ∀ x ∈ K, γ x 0 = x)
    (hinv : ∀ x ∈ K, ∀ t : ℝ, 0 ≤ t → γ x t ∈ K)
    (hderiv : ∀ x ∈ K, HasDerivAt (γ x) (L x) 0) :
    ∃ x ∈ K, L x = 0 := by
  by_contra hex
  have hnot : (0 : E) ∉ L '' K := by
    rintro ⟨x, hx, hLx⟩
    exact hex ⟨x, hx, hLx⟩
  obtain ⟨f, u, hfu, hsep⟩ := geometric_hahn_banach_point_closed
    (hconv.linear_image L.toLinearMap) (hK.image L.continuous).isClosed hnot
  obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne f.continuous.continuousOn
  have hpos : 0 < f (L x) := by
    have hu : 0 < u := by simpa only [map_zero] using hfu
    exact hu.trans (hsep _ ⟨x, hx, rfl⟩)
  have hd : HasDerivAt (fun t : ℝ => f (γ x t)) (f (L x)) 0 :=
    f.hasFDerivAt.comp_hasDerivAt 0 (hderiv x hx)
  have hnonpos : f (L x) ≤ 0 := by
    apply le_of_tendsto hd.tendsto_slope_zero_right
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [zero_add, hzero x hx, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht.le)
      (sub_nonpos.mpr (hmax (hinv x hx t ht.le)))
  exact (not_lt_of_ge hnonpos) hpos

local instance : Module ℝ QubitMatrix :=
  (TNOperatorSpace.instNormedSpaceRealMatrixComplex (Fin 2)).toModule

/-- 任意有限跳跃数与 Hermitian Hamiltonian 的原始 GKSL 作用都有密度稳态。 -/
theorem gksl_exists_stationary_density {n : ℕ} (H : QubitMatrix)
    (A : Fin n → QubitMatrix) (hH : H.IsHermitian) :
    ∃ ρ : QubitMatrix, ρ.PosSemidef ∧ ρ.trace = 1 ∧ gkslAction H A ρ = 0 := by
  let L : QubitMatrix →L[ℝ] QubitMatrix :=
    (gkslContinuousLinearMap H A).restrictScalars ℝ
  have hγzero (ρ : QubitMatrix) (_hρ : ρ ∈ densityMatrices 2) :
      expSemigroup (gkslLinearMap H A) 0 ρ = ρ := by
    rw [expSemigroup_zero]
    rfl
  have hγinv (ρ : QubitMatrix) (hρ : ρ ∈ densityMatrices 2)
      (t : ℝ) (ht : 0 ≤ t) :
      expSemigroup (gkslLinearMap H A) t ρ ∈ densityMatrices 2 := by
    rw [← gkslSuperoperatorEvolution_toLinearMap_eq_expSemigroup]
    exact IsChannel.map_densityMatrices _ (gkslSuperoperatorEvolution_isChannel H A t hH ht) ρ hρ
  have hγderiv (ρ : QubitMatrix) (_hρ : ρ ∈ densityMatrices 2) :
      HasDerivAt (fun t : ℝ => expSemigroup (gkslLinearMap H A) t ρ) (L ρ) 0 := by
    convert hasDerivAt_expSemigroup_apply (gkslLinearMap H A) ρ 0 using 1
    simp [expSemigroup_zero, L, gkslContinuousLinearMap, gkslLinearMap]
    rfl
  obtain ⟨ρ, hρ, hLρ⟩ := exists_zero_of_compact_convex_invariant
    (densityMatrices 2) densityMatrices_isCompact densityMatrices_isConvex
    (densityMatrices_nonempty (by norm_num : 0 < 2)) L
    (fun ρ t => expSemigroup (gkslLinearMap H A) t ρ)
    hγzero hγinv hγderiv
  exact ⟨ρ, hρ.1, hρ.2, hLρ⟩

#check @gksl_exists_stationary_density
#print axioms exists_zero_of_compact_convex_invariant
#print axioms gksl_exists_stationary_density

end TwoStateQuantumEmbedding





