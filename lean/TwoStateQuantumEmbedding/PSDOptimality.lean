import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! 有限维半正定互补性：结论适用于复 Kossakowski 矩阵；尚不假设任何 GKSL 极值性质。 -/

noncomputable section
open Matrix
open scoped MatrixOrder ComplexOrder

namespace TwoStateQuantumEmbedding.PSDNormal

variable {n : Type*} [Fintype n] [DecidableEq n]

abbrev euclideanOperator (S : Matrix n n ℂ) :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) S

/-- 两个半正定矩阵的迹配对为零，必然给出矩阵乘积为零。 -/
theorem mul_eq_zero_of_psd_trace_eq_zero {S K : Matrix n n ℂ}
    (hS : S.PosSemidef) (hK : K.PosSemidef) (htr : (S * K).trace = 0) :
    S * K = 0 := by
  obtain ⟨A, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hS.nonneg
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hK.nonneg
  change (Aᴴ * A) * (Bᴴ * B) = 0
  change ((Aᴴ * A) * (Bᴴ * B)).trace = 0 at htr
  have hnorm : ((A * Bᴴ)ᴴ * (A * Bᴴ)).trace = 0 := by
    calc
      ((A * Bᴴ)ᴴ * (A * Bᴴ)).trace = (B * ((Aᴴ * A) * Bᴴ)).trace := by
        simp only [conjTranspose_mul, conjTranspose_conjTranspose, mul_assoc]
      _ = (((Aᴴ * A) * Bᴴ) * B).trace := trace_mul_comm _ _
      _ = ((Aᴴ * A) * (Bᴴ * B)).trace := by rw [mul_assoc]
      _ = 0 := htr
  have hab : A * Bᴴ = 0 := trace_conjTranspose_mul_self_eq_zero_iff.mp hnorm
  calc
    (Aᴴ * A) * (Bᴴ * B) = Aᴴ * ((A * Bᴴ) * B) := by simp only [mul_assoc]
    _ = 0 := by rw [hab, zero_mul, mul_zero]

/-- Hermitian 矩阵的迹配对为实数。 -/
theorem trace_mul_im_eq_zero {S K : Matrix n n ℂ}
    (hS : S.IsHermitian) (hK : K.IsHermitian) : (S * K).trace.im = 0 := by
  have hc : star ((S * K).trace) = (S * K).trace := by
    rw [← trace_conjTranspose, conjTranspose_mul, hS.eq, hK.eq, trace_mul_comm]
  have hi := congrArg Complex.im hc
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

/-- 实迹内积的互补性版本，与 Hermitian 梯度约定直接匹配。 -/
theorem mul_eq_zero_of_psd_re_trace_eq_zero {S K : Matrix n n ℂ}
    (hS : S.PosSemidef) (hK : K.PosSemidef) (htr : (S * K).trace.re = 0) :
    S * K = 0 := by
  apply mul_eq_zero_of_psd_trace_eq_zero hS hK
  apply Complex.ext
  · exact htr
  · exact trace_mul_im_eq_zero hS.isHermitian hK.isHermitian

/-- 在子空间上有下奇异值间隙时，严格小于该间隙的算子范数扰动不能降低相应秩。 -/
theorem rank_lower_bound_of_norm_lt {S S₀ : Matrix n n ℂ}
    (W : Submodule ℂ (EuclideanSpace ℂ n)) {γ : ℝ}
    (hgap : ∀ v ∈ W, γ * ‖v‖ ≤ ‖euclideanOperator S₀ v‖)
    (hclose : ‖euclideanOperator (S - S₀)‖ < γ) :
    Module.finrank ℂ W ≤ S.rank := by
  let f : W →ₗ[ℂ] EuclideanSpace ℂ n :=
    (euclideanOperator S).toLinearMap.comp W.subtype
  have hinj : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).2
    intro v hv
    apply Subtype.ext
    change (v : EuclideanSpace ℂ n) = 0
    by_contra hv0
    have hnv : 0 < ‖(v : EuclideanSpace ℂ n)‖ := norm_pos_iff.mpr hv0
    have hSv : euclideanOperator S (v : EuclideanSpace ℂ n) = 0 := hv
    have heq : euclideanOperator (S - S₀) (v : EuclideanSpace ℂ n) =
        -euclideanOperator S₀ (v : EuclideanSpace ℂ n) := by
      change ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) (S - S₀)) _ = _
      rw [map_sub, _root_.sub_apply, hSv, zero_sub]
    have hbound := (euclideanOperator (S - S₀)).le_opNorm
      (v : EuclideanSpace ℂ n)
    rw [heq, norm_neg] at hbound
    have hg := hgap (v : EuclideanSpace ℂ n) v.property
    have hlt := mul_lt_mul_of_pos_right hclose hnv
    linarith
  have hrange : Module.finrank ℂ W ≤
      Module.finrank ℂ (LinearMap.range (euclideanOperator S).toLinearMap) := by
    rw [← LinearMap.finrank_range_of_inj hinj]
    exact Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
  have hrank : S.rank =
      Module.finrank ℂ (LinearMap.range (euclideanOperator S).toLinearMap) := by
    exact S.rank_eq_finrank_range_toLin (PiLp.basisFun 2 ℂ n) (PiLp.basisFun 2 ℂ n)
  rwa [← hrank] at hrange

/-- 非零复矩阵的矩阵秩严格为正。 -/
theorem matrix_rank_pos {K : Matrix n n ℂ} (hK : K ≠ 0) : 0 < K.rank := by
  by_contra h
  have hr : K.rank = 0 := Nat.eq_zero_of_not_pos h
  have hrange : LinearMap.range K.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp hr
  have hlin : K.mulVecLin = 0 := LinearMap.range_eq_bot.mp hrange
  apply hK
  ext i j
  have hv := congrArg (fun f : (n → ℂ) →ₗ[ℂ] (n → ℂ) => f (Pi.single j 1) i) hlin
  simpa using hv

/-- 三维中，零乘积与二维稳定间隙迫使所有非零互补矩阵恰为秩一。 -/
theorem rank_one_of_complementarity_and_gap {S S₀ K : Matrix (Fin 3) (Fin 3) ℂ}
    (W : Submodule ℂ (EuclideanSpace ℂ (Fin 3))) {γ : ℝ}
    (hW : 2 ≤ Module.finrank ℂ W)
    (hgap : ∀ v ∈ W, γ * ‖v‖ ≤ ‖euclideanOperator S₀ v‖)
    (hclose : ‖euclideanOperator (S - S₀)‖ < γ)
    (hK : K ≠ 0) (hSK : S * K = 0) : K.rank = 1 := by
  have hSrank : 2 ≤ S.rank := hW.trans (rank_lower_bound_of_norm_lt W hgap hclose)
  have hsum := Matrix.rank_add_rank_le_card_of_mul_eq_zero hSK
  have hpos := matrix_rank_pos hK
  simp only [Fintype.card_fin] at hsum
  omega

/-- 将实迹 PSD 互补性与真实算子范数间隙直接组合。 -/
theorem rank_one_of_psd_trace_and_gap {S S₀ K : Matrix (Fin 3) (Fin 3) ℂ}
    (W : Submodule ℂ (EuclideanSpace ℂ (Fin 3))) {γ : ℝ}
    (hW : 2 ≤ Module.finrank ℂ W)
    (hgap : ∀ v ∈ W, γ * ‖v‖ ≤ ‖euclideanOperator S₀ v‖)
    (hclose : ‖euclideanOperator (S - S₀)‖ < γ)
    (hS : S.PosSemidef) (hK : K.PosSemidef) (hK0 : K ≠ 0)
    (htr : (S * K).trace.re = 0) : K.rank = 1 :=
  rank_one_of_complementarity_and_gap W hW hgap hclose hK0
    (mul_eq_zero_of_psd_re_trace_eq_zero hS hK htr)

/-- 正二次型间隙蕴含下奇异值间隙，因此可直接使用正谱子空间。 -/
theorem norm_gap_of_quadratic_gap {S₀ : Matrix n n ℂ}
    (W : Submodule ℂ (EuclideanSpace ℂ n)) {γ : ℝ}
    (hgap : ∀ v ∈ W,
      γ * ‖v‖ ^ 2 ≤ (inner ℂ v (euclideanOperator S₀ v)).re) :
    ∀ v ∈ W, γ * ‖v‖ ≤ ‖euclideanOperator S₀ v‖ := by
  intro v hv
  by_cases hv0 : v = 0
  · simp [hv0]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hi := re_inner_le_norm (𝕜 := ℂ) v (euclideanOperator S₀ v)
  have hg := hgap v hv
  refine le_of_mul_le_mul_left (a := ‖v‖) ?_ hn
  calc
    ‖v‖ * (γ * ‖v‖) = γ * ‖v‖ ^ 2 := by ring
    _ ≤ ‖v‖ * ‖euclideanOperator S₀ v‖ := hg.trans hi

/-- 两个正特征值所对应的二维正谱子空间可作为本定理的 W；间隙条件是实际二次型下界。 -/
theorem rank_one_of_psd_trace_and_quadratic_gap
    {S S₀ K : Matrix (Fin 3) (Fin 3) ℂ}
    (W : Submodule ℂ (EuclideanSpace ℂ (Fin 3))) {γ : ℝ}
    (hW : 2 ≤ Module.finrank ℂ W)
    (hgap : ∀ v ∈ W,
      γ * ‖v‖ ^ 2 ≤ (inner ℂ v (euclideanOperator S₀ v)).re)
    (hclose : ‖euclideanOperator (S - S₀)‖ < γ)
    (hS : S.PosSemidef) (hK : K.PosSemidef) (hK0 : K ≠ 0)
    (htr : (S * K).trace.re = 0) : K.rank = 1 :=
  rank_one_of_psd_trace_and_gap W hW (norm_gap_of_quadratic_gap W hgap)
    hclose hS hK hK0 htr

/-- PSD 锥相对于 Hermitian 空间上的实迹配对自对偶。 -/
theorem psd_of_nonneg_re_trace_tests {S : Matrix n n ℂ} (hS : S.IsHermitian)
    (htest : ∀ W : Matrix n n ℂ, W.PosSemidef → 0 ≤ (S * W).trace.re) :
    S.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hS
  intro v
  have hr := htest (Matrix.vecMulVec v (star v)) (Matrix.posSemidef_vecMulVec_self_star v)
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm] at hr
  apply Complex.nonneg_iff.mpr
  refine ⟨hr, ?_⟩
  have hi := congrArg Complex.im (hS.star_dotProduct_mulVec_comm v v)
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

/-- 对整个 PSD 锥的真实一阶变分不等式与径向互补性给出 PSD 法向和零乘积。 -/
theorem psd_complementarity_of_variational_inequality {S K : Matrix n n ℂ}
    (hS : S.IsHermitian) (hK : K.PosSemidef)
    (htr : (S * K).trace.re = 0)
    (hvar : ∀ W : Matrix n n ℂ, W.PosSemidef → 0 ≤ (S * (W - K)).trace.re) :
    S.PosSemidef ∧ S * K = 0 := by
  have hpos : S.PosSemidef := by
    apply psd_of_nonneg_re_trace_tests hS
    intro W hW
    have hw := hvar W hW
    simpa [mul_sub, trace_sub, htr] using hw
  exact ⟨hpos, mul_eq_zero_of_psd_re_trace_eq_zero hpos hK htr⟩

#print axioms mul_eq_zero_of_psd_trace_eq_zero
#print axioms mul_eq_zero_of_psd_re_trace_eq_zero
#print axioms rank_lower_bound_of_norm_lt
#print axioms rank_one_of_psd_trace_and_gap
#print axioms rank_one_of_psd_trace_and_quadratic_gap
#print axioms psd_complementarity_of_variational_inequality

end TwoStateQuantumEmbedding.PSDNormal




/-! 锥边界处的约束法向：先证明真实单侧约束局部极小的二维隐函数引理。 -/

noncomputable section
open Filter Set
open scoped Topology

namespace TwoStateQuantumEmbedding.ConeIFT

/-- 非零的一维连续线性映射可逆；这里不把隐函数的可逆性作为额外假设。 -/
theorem scalar_isInvertible {L : ℝ →L[ℝ] ℝ} (hL : L 1 ≠ 0) : L.IsInvertible := by
  have hformula : ∀ t : ℝ, L t = t * L 1 := by
    intro t
    simpa using L.map_smul t (1 : ℝ)
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := (L 1)⁻¹ • ContinuousLinearMap.id ℝ ℝ)
  · apply ContinuousLinearMap.ext
    intro t
    change L ((L 1)⁻¹ * t) = t
    rw [hformula ((L 1)⁻¹ * t)]
    field_simp
  · apply ContinuousLinearMap.ext
    intro t
    change (L 1)⁻¹ * L t = t
    rw [hformula t]
    field_simp

/-- 在半平面 t≥0 内保持真实等式约束的局部极小，导出消去径向变量后的单侧法向不等式。 -/
theorem constrained_halfspace_normal
    {f g : ℝ × ℝ → ℝ} {f' g' : (ℝ × ℝ) →L[ℝ] ℝ}
    (hf : HasFDerivAt f f' (0, 0))
    (hg : HasStrictFDerivAt g g' (0, 0))
    (hreg : g' (0, 1) ≠ 0)
    (hmin : IsLocalMinOn f {p | 0 ≤ p.1 ∧ g p = g (0, 0)} (0, 0)) :
    0 ≤ f' (1, 0) - (f' (0, 1) / g' (0, 1)) * g' (1, 0) := by
  have hinv : (g' ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    apply scalar_isInvertible
    simpa using hreg
  let ψ : ℝ → ℝ := hg.implicitFunctionOfProdDomain hinv
  have hψ0 : ψ 0 = 0 :=
    (hg.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv).self_of_nhds.mp rfl
  let L : ℝ →L[ℝ] ℝ :=
    -(g' ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).inverse ∘L
      (g' ∘L ContinuousLinearMap.inl ℝ ℝ ℝ)
  have hψ : HasDerivAt ψ (L 1) 0 :=
    (hg.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv).hasFDerivAt.hasDerivAt
  let c : ℝ → ℝ × ℝ := fun t => (t, ψ t)
  have hc0 : c 0 = (0, 0) := by simp [c, hψ0]
  have hc : HasDerivAt c (1, L 1) 0 := (hasDerivAt_id 0).prodMk hψ
  have hgcurve : ∀ᶠ t in 𝓝 (0 : ℝ), g (c t) = g (0, 0) :=
    hg.eventually_apply_implicitFunctionOfProdDomain hinv
  have hgder : g' (1, L 1) = 0 := by
    have hd := hg.hasFDerivAt.comp_hasDerivAt_of_eq 0 hc hc0.symm
    have hdconst : HasDerivAt (fun _ : ℝ => g (0, 0)) (g' (1, L 1)) 0 :=
      hd.congr_of_eventuallyEq (hgcurve.mono fun t ht => ht.symm)
    exact hdconst.unique (hasDerivAt_const 0 (g (0, 0)))
  have hctend : Tendsto c (𝓝[Ici (0 : ℝ)] 0)
      (𝓝[{p | 0 ≤ p.1 ∧ g p = g (0, 0)}] (0, 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa [hc0] using hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [hgcurve.filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with t hgt ht
      exact ⟨ht, hgt⟩
  have hfcurve : IsLocalMinOn (f ∘ c) (Ici 0) 0 := by
    change ∀ᶠ t in 𝓝[Ici (0 : ℝ)] 0, (f ∘ c) 0 ≤ (f ∘ c) t
    simpa [Function.comp_def, hc0] using hctend.eventually hmin
  have htangent : (1 : ℝ) ∈ posTangentConeAt (Ici (0 : ℝ)) 0 := by
    have hseg : segment ℝ (0 : ℝ) (1 : ℝ) ⊆ Ici (0 : ℝ) :=
      (convex_Ici (0 : ℝ)).segment_subset (by simp) (by norm_num)
    have ht := sub_mem_posTangentConeAt_of_segment_subset hseg
    simpa using ht
  have hfder := hf.comp_hasDerivAt_of_eq 0 hc hc0.symm
  have hsign : 0 ≤ f' (1, L 1) := by
    simpa using hfcurve.hasFDerivWithinAt_nonneg hfder.hasFDerivAt.hasFDerivWithinAt htangent
  have heval (T : (ℝ × ℝ) →L[ℝ] ℝ) :
      T (1, L 1) = T (1, 0) + L 1 * T (0, 1) := by
    have hv : (1, L 1) = ((1, 0) : ℝ × ℝ) + L 1 • ((0, 1) : ℝ × ℝ) := by
      ext <;> simp
    rw [hv, map_add, map_smul]
    rfl
  rw [heval] at hgder hsign
  have hslope : L 1 = -(g' (1, 0)) / g' (0, 1) := by
    apply (eq_div_iff hreg).mpr
    linarith
  rw [hslope] at hsign
  convert hsign using 1 <;> ring

section Cone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- 凸组合后作正径向缩放；原点映到 K。 -/
def radialSegment (K W : E) (p : ℝ × ℝ) : E :=
  (1 + p.2) • ((1 - p.1) • K + p.1 • W)

def radialSegmentDeriv (K W : E) : (ℝ × ℝ) →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (W - K) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight K

@[simp] theorem radialSegment_zero (K W : E) : radialSegment K W (0, 0) = K := by
  simp [radialSegment]

theorem radialSegment_hasStrictFDerivAt (K W : E) :
    HasStrictFDerivAt (radialSegment K W) (radialSegmentDeriv K W) (0, 0) := by
  have hfst : HasStrictFDerivAt (fun p : ℝ × ℝ => p.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (0, 0) := hasStrictFDerivAt_fst
  have hsnd : HasStrictFDerivAt (fun p : ℝ × ℝ => p.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) (0, 0) := hasStrictFDerivAt_snd
  have h := (hsnd.const_add 1).smul
    ((((hasStrictFDerivAt_const (1 : ℝ) ((0, 0) : ℝ × ℝ)).sub hfst).smul_const K).add
      (hfst.smul_const W))
  convert h using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro p
    simp [radialSegmentDeriv, ContinuousLinearMap.smulRight_apply]
    module

/-- 在任意实范数空间的凸锥上，从实际等式约束局部极小推出完整的一阶锥法向。 -/
theorem cone_normal_of_localMin
    {C : Set E} {a b : E → ℝ} {K : E} {a' b' : E →L[ℝ] ℝ}
    (hconv : Convex ℝ C)
    (hcone : ∀ (r : ℝ), 0 ≤ r → ∀ x ∈ C, r • x ∈ C)
    (hK : K ∈ C)
    (ha : HasFDerivAt a a' K)
    (hb : HasStrictFDerivAt b b' K)
    (hreg : b' K ≠ 0)
    (hmin : IsLocalMinOn a {x | x ∈ C ∧ b x = b K} K) :
    (a' - (a' K / b' K) • b') K = 0 ∧
      ∀ W ∈ C, 0 ≤ (a' - (a' K / b' K) • b') W := by
  have hradial : (a' - (a' K / b' K) • b') K = 0 := by
    simp only [_root_.sub_apply, _root_.smul_apply, smul_eq_mul]
    field_simp
    ring
  refine ⟨hradial, ?_⟩
  intro W hW
  let q : ℝ × ℝ → E := radialSegment K W
  let D : (ℝ × ℝ) →L[ℝ] E := radialSegmentDeriv K W
  have hq : HasStrictFDerivAt q D (0, 0) := radialSegment_hasStrictFDerivAt K W
  have hq0 : q (0, 0) = K := radialSegment_zero K W
  have ha0 : HasFDerivAt a a' (q (0, 0)) := by simpa [hq0] using ha
  have hb0 : HasStrictFDerivAt b b' (q (0, 0)) := by simpa [hq0] using hb
  have haf : HasFDerivAt (a ∘ q) (a' ∘L D) (0, 0) := ha0.comp (0, 0) hq.hasFDerivAt
  have hbf : HasStrictFDerivAt (b ∘ q) (b' ∘L D) (0, 0) := hb0.comp (0, 0) hq
  have hD1 : D (1, 0) = W - K := by simp [D, radialSegmentDeriv]
  have hD2 : D (0, 1) = K := by simp [D, radialSegmentDeriv]
  have hlocal : IsLocalMinOn (a ∘ q)
      {p | 0 ≤ p.1 ∧ (b ∘ q) p = (b ∘ q) (0, 0)} (0, 0) := by
    have ht : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0), p.1 < 1 :=
      (isOpen_lt continuous_fst continuous_const).mem_nhds (by norm_num)
    have hs : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0), -1 < p.2 :=
      (isOpen_lt continuous_const continuous_snd).mem_nhds (by norm_num)
    have hmap : Tendsto q
        (𝓝[{p | 0 ≤ p.1 ∧ (b ∘ q) p = (b ∘ q) (0, 0)}] (0, 0))
        (𝓝[{x | x ∈ C ∧ b x = b K}] K) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · simpa [hq0] using hq.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [ht.filter_mono nhdsWithin_le_nhds,
          hs.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with p hpt hps hp
        refine ⟨?_, ?_⟩
        · apply hcone (1 + p.2) (by linarith)
          exact hconv hK hW (by linarith) hp.1 (by ring)
        · simpa [Function.comp_def, hq0] using hp.2
    change ∀ᶠ p in 𝓝[{p | 0 ≤ p.1 ∧ (b ∘ q) p = (b ∘ q) (0, 0)}] (0, 0),
      (a ∘ q) (0, 0) ≤ (a ∘ q) p
    simpa [Function.comp_def, hq0] using hmap.eventually hmin
  have hn := constrained_halfspace_normal haf hbf (by simpa [hD2] using hreg) hlocal
  simp only [ContinuousLinearMap.comp_apply, hD1, hD2, map_sub] at hn
  simp only [_root_.sub_apply, _root_.smul_apply, smul_eq_mul]
  have hr : a' K - a' K / b' K * b' K = 0 := by
    field_simp
    ring
  nlinarith

end Cone

#print axioms constrained_halfspace_normal
#print axioms cone_normal_of_localMin

end TwoStateQuantumEmbedding.ConeIFT

namespace TwoStateQuantumEmbedding.PSDOptimality

open Matrix PSDNormal ConeIFT
open scoped MatrixOrder ComplexOrder
open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- 对真实 PSD 约束极小值，由非零径向约束导数推出 PSD 对偶法向；没有 KKT 假设。 -/
theorem psd_normal_of_localMin
    {a b : Matrix n n ℂ → ℝ} {K A B : Matrix n n ℂ}
    {a' b' : Matrix n n ℂ →L[ℝ] ℝ}
    (hK : K.PosSemidef) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (ha : HasFDerivAt a a' K) (hb : HasStrictFDerivAt b b' K)
    (haPair : ∀ W : Matrix n n ℂ, W.IsHermitian → a' W = (A * W).trace.re)
    (hbPair : ∀ W : Matrix n n ℂ, W.IsHermitian → b' W = (B * W).trace.re)
    (hreg : b' K ≠ 0)
    (hmin : IsLocalMinOn a {W | W.PosSemidef ∧ b W = b K} K) :
    let S := A - (a' K / b' K) • B
    S.PosSemidef ∧ (S * K).trace.re = 0 ∧ S * K = 0 := by
  let μ := a' K / b' K
  let S := A - μ • B
  have hconv : Convex ℝ {W : Matrix n n ℂ | W.PosSemidef} := by
    intro X hX Y hY r s hr hs hrs
    exact (hX.smul hr).add (hY.smul hs)
  have hcone : ∀ r : ℝ, 0 ≤ r →
      ∀ W : Matrix n n ℂ, W.PosSemidef → (r • W).PosSemidef := by
    intro r hr W hW
    exact hW.smul hr
  have hnormal := cone_normal_of_localMin (E := Matrix n n ℂ)
    (C := {W : Matrix n n ℂ | W.PosSemidef}) (a := a) (b := b)
    (K := K) (a' := a') (b' := b') hconv hcone hK ha hb hreg hmin
  have hS : S.IsHermitian := by
    simp only [S, Matrix.IsHermitian, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_smul, star_trivial, hA.eq, hB.eq]
  have hpair (W : Matrix n n ℂ) (hW : W.IsHermitian) :
      (a' - μ • b') W = (S * W).trace.re := by
    simp [S, _root_.sub_apply, _root_.smul_apply, smul_eq_mul, haPair W hW, hbPair W hW,
      Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul,
      RCLike.smul_re]
  have htr : (S * K).trace.re = 0 := by
    rw [← hpair K hK.isHermitian]
    exact hnormal.1
  have hpos : S.PosSemidef := by
    apply psd_of_nonneg_re_trace_tests hS
    intro W hW
    rw [← hpair W hW.isHermitian]
    exact hnormal.2 W hW
  exact ⟨hpos, htr, mul_eq_zero_of_psd_re_trace_eq_zero hpos hK htr⟩

/-- 将真实约束极小、PSD 法向与二维谱隙合并，得到精确秩一。 -/
theorem minimizer_rank_one_of_quadratic_gap
    {a b : Matrix (Fin 3) (Fin 3) ℂ → ℝ}
    {K A B S₀ : Matrix (Fin 3) (Fin 3) ℂ}
    {a' b' : Matrix (Fin 3) (Fin 3) ℂ →L[ℝ] ℝ}
    (hK : K.PosSemidef) (hK0 : K ≠ 0)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (ha : HasFDerivAt a a' K) (hb : HasStrictFDerivAt b b' K)
    (haPair : ∀ W : Matrix (Fin 3) (Fin 3) ℂ, W.IsHermitian → a' W = (A * W).trace.re)
    (hbPair : ∀ W : Matrix (Fin 3) (Fin 3) ℂ, W.IsHermitian → b' W = (B * W).trace.re)
    (hreg : b' K ≠ 0)
    (hmin : IsLocalMinOn a {W | W.PosSemidef ∧ b W = b K} K)
    (P : Submodule ℂ (EuclideanSpace ℂ (Fin 3))) {γ : ℝ}
    (hP : 2 ≤ Module.finrank ℂ P)
    (hgap : ∀ v ∈ P, γ * ‖v‖ ^ 2 ≤ (inner ℂ v (euclideanOperator S₀ v)).re)
    (hclose : ‖euclideanOperator (A - (a' K / b' K) • B - S₀)‖ < γ) :
    K.rank = 1 := by
  have hn := psd_normal_of_localMin hK hA hB ha hb haPair hbPair hreg hmin
  exact rank_one_of_psd_trace_and_quadratic_gap P hP hgap hclose hn.1 hK hK0 hn.2.1

#print axioms psd_normal_of_localMin
#print axioms minimizer_rank_one_of_quadratic_gap

end TwoStateQuantumEmbedding.PSDOptimality


