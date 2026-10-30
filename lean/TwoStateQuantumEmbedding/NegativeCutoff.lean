import TwoStateQuantumEmbedding.CanonicalRigidity
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Tactic

noncomputable section
open scoped RealInnerProductSpace Matrix Matrix.Norms.L2Operator ComplexOrder
open NormedSpace Matrix
namespace TwoStateQuantumEmbedding.NegativeCutoff
open DissipativeFlow Rigidity
abbrev E := EuclideanSpace ℝ (Fin 3)

def crossE (u v : E) : E := euclideanVector3 ((fun i => u i) ⨯₃ (fun i => v i))

lemma crossE_norm_sq (u v : E) :
    ‖crossE u v‖ ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u,v⟫ ^ 2 := by
  rw [crossE, euclideanVector3_norm_sq, cross_dot_cross]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  rw [dotProduct_comm (fun i => v i) (fun i => u i)]
  ring

lemma crossE_norm_le (u v : E) : ‖crossE u v‖ ≤ ‖u‖ * ‖v‖ := by
  have h := crossE_norm_sq u v
  have hn := mul_nonneg (norm_nonneg u) (norm_nonneg v)
  nlinarith [sq_nonneg ⟪u,v⟫, norm_nonneg (crossE u v)]

lemma projection_residual_sq (u x : E) (hu : ‖u‖ = 1) :
    ‖x - ⟪u,x⟫ • u‖ ^ 2 = ‖x‖ ^ 2 - ⟪u,x⟫ ^ 2 := by
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, hu]
  simp only [inner_smul_right, real_inner_comm x u, one_pow, mul_one, sq_abs]
  ring

lemma crossE_normalized (y x : E) (hy : y ≠ 0) :
    ‖crossE y x‖ = ‖y‖ * ‖x - ⟪(‖y‖⁻¹ • y),x⟫ • (‖y‖⁻¹ • y)‖ := by
  have hyn : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hu : ‖‖y‖⁻¹ • y‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg y), inv_mul_cancel₀ hyn]
  have h := projection_residual_sq (‖y‖⁻¹ • y) x hu
  have he := crossE_norm_sq y x
  have heq : (‖y‖ * ‖x - ⟪‖y‖⁻¹ • y,x⟫ • (‖y‖⁻¹ • y)‖)^2 = ‖crossE y x‖^2 := by
    rw [mul_pow, h, he]
    simp only [inner_smul_left, starRingEnd_apply, star_trivial]
    field_simp

  nlinarith [norm_nonneg (crossE y x),
    mul_nonneg (norm_nonneg y) (norm_nonneg (x - ⟪‖y‖⁻¹ • y,x⟫ • (‖y‖⁻¹ • y)))]

lemma canonical_cross_bound (Ω S : RealMatrix3) (hΩ : Ωᵀ = -Ω)
    (hS : S.PosSemidef) {t : ℝ} (ht : 0 ≤ t) (u v : E) :
    ‖crossE (Matrix.toEuclideanCLM (𝕜 := ℝ) (exp (t • (Ω - canonicalD S))) u)
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (exp (t • (Ω - canonicalD S))) v)‖ ≤
      Real.exp (-2 * S.trace * t) * ‖crossE u v‖ := by
  let : NormedAlgebra ℚ RealMatrix3 := .restrictScalars ℚ ℝ _
  let B := exp (t • (Ω - canonicalD S))
  have hd : B.det = Real.exp (t * (-4 * S.trace)) := by
    dsimp [B]
    rw [det_exp_three_smul, canonical_trace Ω S hΩ]
  have hi : ‖B⁻¹‖ ≤ Real.exp ((2 * S.trace) * t) := by
    dsimp [B]
    rw [Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_exp]
    simpa only [neg_smul] using
      matrix_inverse_norm Ω (canonicalD S) hΩ (2*S.trace) (canonicalD_upper S hS) ht
  have ha := norm_cross_mulVec_le B (by rw [hd]; exact (Real.exp_pos _).ne')
    (fun i => u i) (fun i => v i)
  change ‖crossE (Matrix.toEuclideanCLM (𝕜 := ℝ) B u) (Matrix.toEuclideanCLM (𝕜 := ℝ) B v)‖ ≤
    |B.det| * ‖B⁻¹‖ * ‖crossE u v‖ at ha
  rw [hd, abs_of_pos (Real.exp_pos _)] at ha
  have hb := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hi (Real.exp_pos (t * (-4 * S.trace))).le) (norm_nonneg (crossE u v))
  have he : Real.exp (t * (-4 * S.trace)) * Real.exp (2 * S.trace * t) =
      Real.exp (-2 * S.trace * t) := by rw [← Real.exp_add]; congr 1; ring
  exact ha.trans (by simpa only [he] using hb)



lemma rankOne_approximation (F : E →L[ℝ] E) (ε : ℝ) (hε : 0 < ε)
    (hF : ‖F‖ ≤ 1)
    (harea : ∀ v x, ‖crossE (F v) (F x)‖ ≤ ε^2 * ‖crossE v x‖) :
    ∃ u w : E, ‖u‖ = 1 ∧ ‖w‖ ≤ 1 ∧
      ‖F - InnerProductSpace.rankOne ℝ u w‖ ≤ ε := by
  by_cases hsmall : ‖F‖ ≤ ε
  · refine ⟨zAxis, 0, zAxis_norm, by simp, ?_⟩
    simpa using hsmall
  obtain ⟨v, hv, hvF⟩ := F.exists_lt_apply_of_lt_opNorm (lt_of_not_ge hsmall)
  have hFv : F v ≠ 0 := by intro he; simp [he] at hvF; linarith
  have hn : ‖F v‖ ≠ 0 := norm_ne_zero_iff.mpr hFv
  let u : E := ‖F v‖⁻¹ • F v
  let w : E := ContinuousLinearMap.adjoint F u
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hn]
  have hw : ‖w‖ ≤ 1 := by
    have hw' := (ContinuousLinearMap.adjoint F).le_opNorm u
    simpa only [LinearIsometryEquiv.norm_map, hu, mul_one] using hw' |>.trans (by simpa only [LinearIsometryEquiv.norm_map, hu, mul_one] using hF)
  refine ⟨u, w, hu, hw, ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ hε.le
  intro x
  have hr : (F - InnerProductSpace.rankOne ℝ u w) x = F x - ⟪u,F x⟫ • u := by
    simp only [_root_.sub_apply, InnerProductSpace.rankOne_apply, w,
      ContinuousLinearMap.adjoint_inner_left]
  rw [hr]
  have hc := harea v x
  rw [crossE_normalized (F v) (F x) hFv] at hc
  change ‖F v‖ * ‖F x - ⟪u,F x⟫ • u‖ ≤ ε^2 * ‖crossE v x‖ at hc
  have hc' := mul_le_mul_of_nonneg_left (crossE_norm_le v x) (sq_nonneg ε)
  have hc'' : ε^2 * (‖v‖ * ‖x‖) ≤ ε^2 * ‖x‖ := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left (norm_nonneg x) hv.le) (sq_nonneg ε)
  have hb := hc.trans (hc'.trans hc'')
  have hnon := norm_nonneg (F x - ⟪u,F x⟫ • u)
  have hs : ε * ‖F x - ⟪u,F x⟫ • u‖ ≤ ε^2 * ‖x‖ :=
    (mul_le_mul_of_nonneg_right hvF.le hnon).trans hb
  nlinarith

lemma rankOne_readout_interval (u w e : E) (hu : ‖u‖=1)
    (hw : ‖w‖ ≤ 1) (he : ‖e‖=1) :
    |2 * (⟪e,u⟫ * ⟪w,e⟫) - ⟪w,u⟫| ≤ 1 := by
  let q : E := (2 * ⟪e,u⟫) • e - u
  have hq : ‖q‖ = 1 := by
    have hs : ‖q‖^2 = 1 := by
      dsimp [q]
      rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow,
        he, hu, inner_smul_left]
      simp only [starRingEnd_apply, star_trivial, sq_abs]
      ring
    nlinarith [norm_nonneg q]
  have hi := abs_real_inner_le_norm w q
  rw [hq, mul_one] at hi
  have hread : ⟪w,q⟫ = 2*(⟪e,u⟫ * ⟪w,e⟫)-⟪w,u⟫ := by
    simp only [q, inner_sub_right, inner_smul_right]
    ring
  rw [hread] at hi
  exact hi.trans hw

lemma rankOne_pow (u w : E) (m : ℕ) :
    (InnerProductSpace.rankOne ℝ u w)^(m+1) =
      (⟪w,u⟫^m) • InnerProductSpace.rankOne ℝ u w := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih, smul_mul_assoc, ContinuousLinearMap.mul_def,
      InnerProductSpace.rankOne_comp_rankOne, smul_smul, pow_succ]

lemma norm_pow_sub_pow_le (A R : E →L[ℝ] E) (hA : ‖A‖ ≤ 1) (hR : ‖R‖ ≤ 1)
    (ε : ℝ) (hε : 0 ≤ ε) (hAR : ‖A-R‖ ≤ ε) (n : ℕ) :
    ‖A^n - R^n‖ ≤ n * ε := by
  induction n with
  | zero => simp
  | succ n ih =>
    have heq : A^(n+1)-R^(n+1) = (A^n-R^n)*A+R^n*(A-R) := by
      simp only [pow_succ, sub_mul, mul_sub]
      abel
    rw [heq]
    calc
      _ ≤ ‖A^n-R^n‖*‖A‖+‖R^n‖*‖A-R‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ n*ε*1+1*ε := by
        gcongr
        exact (norm_pow_le R n).trans (by simpa using pow_le_pow_left₀ (norm_nonneg R) hR n)
      _ = (n+1:ℕ)*ε := by push_cast; ring




lemma power_loss_bound (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (m : ℕ) :
    (m+1:ℕ) * x^m * (1-x) ≤ 1 := by
  have hs : (m+1:ℕ) * x^m ≤ ∑ j ∈ Finset.range (m+1), x^j := by
    calc
      _ = ∑ j ∈ Finset.range (m+1), x^m := by simp
      _ ≤ ∑ j ∈ Finset.range (m+1), x^j := by
        apply Finset.sum_le_sum
        intro j hj
        exact pow_le_pow_of_le_one hx0 hx1 (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  have hm := mul_le_mul_of_nonneg_right hs (sub_nonneg.mpr hx1)
  rw [geom_sum_mul_neg] at hm
  nlinarith [pow_nonneg hx0 (m+1)]

lemma odd_power_product_lower (r p : ℝ) (hr : |r| ≤ 1)
    (hp : |2*p-r| ≤ 1) (m : ℕ) (hm : Odd m) :
    -(1 / (2 * (m+1:ℕ) : ℝ)) ≤ r^m * p := by
  have hp' := abs_le.mp hp
  have hgeom := power_loss_bound |r| (abs_nonneg r) hr m
  have hn : (0:ℝ) < (m+1:ℕ) := by positivity
  have hb : -(|r|^m * (1-|r|) / 2) ≤ r^m*p := by
    rcases le_total 0 r with hpos | hneg
    · rw [abs_of_nonneg hpos]
      have hh := mul_nonneg (pow_nonneg hpos m) (by linarith [hp'.1] : 0 ≤ p-(r-1)/2)
      nlinarith
    · rw [abs_of_nonpos hneg]
      have he : r^m = -((-r)^m) := by rw [hm.neg_pow, neg_neg]
      rw [he]
      have hh := mul_nonneg (pow_nonneg (neg_nonneg.mpr hneg) m)
        (by linarith [hp'.2] : 0 ≤ (r+1)/2-p)
      nlinarith
  have hbound : |r|^m * (1-|r|) / 2 ≤ 1/(2*(m+1:ℕ):ℝ) := by
    apply (le_div_iff₀ (by positivity : (0:ℝ)<2*(m+1:ℕ))).mpr
    nlinarith
  linarith

lemma rankOne_even_readout_lower (u w e : E) (hu : ‖u‖=1)
    (hw : ‖w‖≤1) (he : ‖e‖=1) (m : ℕ) (hm : Odd m) :
    -(1/(2*(m+1:ℕ):ℝ)) ≤
      ⟪e, ((InnerProductSpace.rankOne ℝ u w)^(m+1)) e⟫ := by
  have hr : |⟪w,u⟫| ≤ 1 := by
    exact (abs_real_inner_le_norm w u).trans (by simpa only [hu, mul_one] using hw)
  have hh := odd_power_product_lower ⟪w,u⟫ (⟪e,u⟫*⟪w,e⟫) hr
    (rankOne_readout_interval u w e hu hw he) m hm
  rw [rankOne_pow]
  simpa only [_root_.smul_apply, InnerProductSpace.rankOne_apply,
    inner_smul_right, mul_comm] using hh




lemma contractive_even_readout (F : E →L[ℝ] E) (ε : ℝ) (hε : 0<ε)
    (hF : ‖F‖≤1)
    (harea : ∀ v x, ‖crossE (F v) (F x)‖ ≤ ε^2 * ‖crossE v x‖)
    (e : E) (he : ‖e‖=1) (m : ℕ) (hm : Odd m) :
    -(1/(2*(m+1:ℕ):ℝ)) - (m+1:ℕ)*ε ≤ ⟪e,(F^(m+1)) e⟫ := by
  obtain ⟨u,w,hu,hw,happrox⟩ := rankOne_approximation F ε hε hF harea
  let R := InnerProductSpace.rankOne ℝ u w
  have hR : ‖R‖≤1 := by simpa only [R, InnerProductSpace.norm_rankOne, hu, one_mul] using hw
  have hdiff := norm_pow_sub_pow_le F R hF hR ε hε.le happrox (m+1)
  have hread := rankOne_even_readout_lower u w e hu hw he m hm
  have hi := abs_real_inner_le_norm e ((F^(m+1)-R^(m+1)) e)
  have hpoint := (F^(m+1)-R^(m+1)).le_opNorm e
  rw [he, mul_one] at hpoint
  rw [he, one_mul] at hi
  have hb := hi.trans (hpoint.trans hdiff)
  simp only [_root_.sub_apply, inner_sub_right] at hb
  have hh := (abs_le.mp hb).1
  change -(1/(2*(m+1:ℕ):ℝ)) ≤ ⟪e,(R^(m+1)) e⟫ at hread
  linarith

lemma exp_reciprocal_pow (M : RealMatrix3) (n : ℕ) (hn : n ≠ 0) :
    (exp ((1/(n:ℝ)) • M))^n = exp M := by
  rw [← Matrix.exp_nsmul]
  have hcast : (n:ℝ) ≠ 0 := by exact_mod_cast hn
  congr 1
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  simp [hcast]

lemma canonical_even_readout (Ω S : RealMatrix3) (hΩ : Ωᵀ = -Ω)
    (hS : S.PosSemidef) (e : E) (he : ‖e‖=1) (m : ℕ) (hm : Odd m) :
    -(1/(2*(m+1:ℕ):ℝ)) - (m+1:ℕ)*Real.exp (-S.trace/(m+1:ℕ)) ≤
      ⟪e,Matrix.toEuclideanCLM (𝕜:=ℝ) (exp (Ω-canonicalD S)) e⟫ := by
  let n := m+1
  let F := Matrix.toEuclideanCLM (𝕜:=ℝ) (exp ((1/(n:ℝ)) • (Ω-canonicalD S)))
  have hn : (0:ℝ)<n := by dsimp [n]; positivity
  have ht : (0:ℝ)≤1/(n:ℝ) := by positivity
  have hF : ‖F‖≤1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa only [one_mul] using
      matrix_contraction Ω (canonicalD S) hΩ (canonicalD_posSemidef S hS) x ht
  have harea (v x : E) : ‖crossE (F v) (F x)‖ ≤
      (Real.exp (-S.trace/(n:ℝ)))^2 * ‖crossE v x‖ := by
    have hh := canonical_cross_bound Ω S hΩ hS ht v x
    have heq : Real.exp (-2*S.trace*(1/(n:ℝ))) = (Real.exp (-S.trace/(n:ℝ)))^2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    simpa only [heq] using hh
  have hh := contractive_even_readout F (Real.exp (-S.trace/(n:ℝ)))
    (Real.exp_pos _) hF harea e he m hm
  have hpow : F^(m+1) = Matrix.toEuclideanCLM (𝕜:=ℝ) (exp (Ω-canonicalD S)) := by
    dsimp [F]
    rw [← map_pow, exp_reciprocal_pow _ n (by dsimp [n]; omega)]
  rw [hpow] at hh
  exact hh




lemma logarithmic_cutoff (d x δ N : ℝ) (hδ : 0<δ) (hN : 0<N)
    (hindex : 1 ≤ δ*N) (hx : x ≤ -δ)
    (hlower : -(1/(2*N))-N*Real.exp (-d/N) ≤ x) :
    d ≤ N * Real.log (2*N/δ) := by
  have hfrac : 1/(2*N) ≤ δ/2 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*N)).mpr
    nlinarith
  have hexp : δ/(2*N) ≤ Real.exp (-d/N) := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*N)).mpr
    linarith
  have hlog := Real.log_le_log (by positivity : (0:ℝ)<δ/(2*N)) hexp
  rw [Real.log_exp] at hlog
  have hi : δ/(2*N) = (2*N/δ)⁻¹ := by field_simp
  rw [hi, Real.log_inv] at hlog
  have hh := (le_div_iff₀ hN).mp hlog
  nlinarith

open GKSLAlgebra CanonicalBloch

lemma canonicalOutput_readout (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ) :
    (canonicalOutput h K 1).1 + (canonicalOutput h K 1).2 - 1 =
      ⟪zAxis,Matrix.toEuclideanCLM (𝕜:=ℝ) (exp (blochMatrix h K)) zAxis⟫ := by
  rw [zAxis_readout]
  have he := AffineExponential.affine_evolution_spatial (blochMatrix h K) (drift K) 1 2 2
  change canonicalEvolution h K 1 3 3 = _ at he
  simp only [one_smul] at he
  dsimp [canonicalOutput]
  rw [he]
  ring

/-- 任意有限规范 GKSL 的偶根耗散界。n=m+1 为任意满足 δn≥1 的偶数。 -/
theorem canonicalOutput_trace_bound_index (h : BlochVec)
    (K : Matrix (Fin 3) (Fin 3) ℂ) (hK : K.PosSemidef)
    (δ : ℝ) (hδ : 0<δ) (m : ℕ) (hm : Odd m)
    (hindex : 1 ≤ δ*(m+1:ℕ))
    (hx : (canonicalOutput h K 1).1 + (canonicalOutput h K 1).2 - 1 ≤ -δ) :
    K.trace.re ≤ (m+1:ℕ) * Real.log (2*(m+1:ℕ)/δ) := by
  have hl := canonical_even_readout (crossMatrix h) (K.map Complex.re)
    (crossMatrix_skew h) (realPart_posSemidef K hK) zAxis zAxis_norm m hm
  rw [← blochMatrix_eq_canonical, trace_realPart, ← canonicalOutput_readout] at hl
  exact logarithmic_cutoff _ _ δ (m+1:ℕ) hδ (by positivity) hindex hx hl

/-- 一个只依赖负区间阈值的显式偶次根次数。 -/
def cutoffIndex (δ : ℝ) : ℕ := 2 * (Nat.ceil (1/δ) + 1)

/-- 全负区间的显式有限耗散截断，无 Hamiltonian 范数限制。 -/
theorem canonicalOutput_trace_bound (h : BlochVec)
    (K : Matrix (Fin 3) (Fin 3) ℂ) (hK : K.PosSemidef)
    (δ : ℝ) (hδ : 0<δ)
    (hx : (canonicalOutput h K 1).1 + (canonicalOutput h K 1).2 - 1 ≤ -δ) :
    K.trace.re ≤ (cutoffIndex δ : ℝ) * Real.log (2*(cutoffIndex δ : ℝ)/δ) := by
  let m := 2 * Nat.ceil (1/δ) + 1
  have hm : Odd m := ⟨Nat.ceil (1/δ), rfl⟩
  have hmindex : m+1 = cutoffIndex δ := by dsimp [m, cutoffIndex]; omega
  have hi : 1 ≤ δ * (m+1:ℕ) := by
    have hc := Nat.le_ceil (1/δ)
    have hc' := mul_le_mul_of_nonneg_left hc hδ.le
    have hh : δ * (1/δ) = 1 := by field_simp
    rw [hh] at hc'
    dsimp [m]
    push_cast
    nlinarith [show (0:ℝ)≤(Nat.ceil (1/δ):ℕ) by positivity]
  simpa only [hmindex] using canonicalOutput_trace_bound_index h K hK δ hδ m hm hi hx

/-- 同一截断应用于原始 Hermitian Hamiltonian 和任意有限个跳跃算子的实际输出。 -/
theorem finiteOutput_trace_bound {n : ℕ} (H : QubitMatrix) (hH : H.IsHermitian)
    (A : Fin n → QubitMatrix) (δ : ℝ) (hδ : 0<δ)
    (hx : (finiteOutput H A 1).1 + (finiteOutput H A 1).2 - 1 ≤ -δ) :
    (kossakowski (fun μ => pauliCoeffs (A μ))).trace.re ≤
      (cutoffIndex δ : ℝ) * Real.log (2*(cutoffIndex δ : ℝ)/δ) := by
  rw [finiteOutput_eq_canonicalOutput H hH A] at hx
  exact canonicalOutput_trace_bound (hamiltonianVector (canonicalHamiltonian H A))
    (kossakowski (fun μ => pauliCoeffs (A μ))) (kossakowski_posSemidef _) δ hδ hx

#print axioms canonical_cross_bound
#print axioms rankOne_approximation
#print axioms canonical_even_readout
#print axioms canonicalOutput_trace_bound
#print axioms finiteOutput_trace_bound

end TwoStateQuantumEmbedding.NegativeCutoff


