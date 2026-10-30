import TwoStateQuantumEmbedding.SwapMatching
import TwoStateQuantumEmbedding.CanonicalRigidity
import TwoStateQuantumEmbedding.AzimuthGauge
import TwoStateQuantumEmbedding.FirstOrderPSD
import TwoStateQuantumEmbedding.ActualSwapComparison

/-! 从实际全圈数比较到原始概率闭包和 Bouligand 正切锥。 -/
noncomputable section
open Filter Matrix Complex
open scoped Topology BigOperators ComplexOrder
namespace TwoStateQuantumEmbedding.SwapCone
open GKSLAlgebra CanonicalBloch GKSLBounds
set_option maxHeartbeats 1200000

lemma cross_conj (v : PauliVec) : Swap.cross (star v) = -Swap.cross v := by
  simp [Swap.cross, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

lemma qa_conj (j : ℕ) (v : PauliVec) : Swap.qa j (star v) = Swap.qb j v := by
  simp [Swap.qa, Swap.qb, Swap.energy, cross_conj, Complex.normSq_conj]

lemma qb_conj (j : ℕ) (v : PauliVec) : Swap.qb j (star v) = Swap.qa j v := by
  simp [Swap.qa, Swap.qb, Swap.energy, cross_conj, Complex.normSq_conj]
  ring

lemma all_frequency_reverse (j : ℕ) (v : PauliVec) :
    Swap.slope * Swap.qa j v ≤ Swap.qb j v := by
  simpa only [qa_conj, qb_conj] using Swap.all_frequency_sharp j (star v)

/-- 所有 PSD 噪声矩阵都满足两个参考迹不等式，不限制跳跃数或秩。 -/
theorem reference_trace_sharp (j : ℕ) (K : Matrix (Fin 3) (Fin 3) ℂ)
    (hK : K.PosSemidef) :
    Swap.slope * (Swap.matrixQb j * K).trace.re ≤ (Swap.matrixQa j * K).trace.re ∧
    Swap.slope * (Swap.matrixQa j * K).trace.re ≤ (Swap.matrixQb j * K).trace.re := by
  obtain ⟨v, rfl⟩ := exists_kossakowski_factor K hK
  rw [SwapComparison.kossakowski_eq_swap, Swap.trace_Qa_kossakowski,
    Swap.trace_Qb_kossakowski]
  simp only [Complex.ofReal_re]
  constructor
  · simpa only [Finset.mul_sum] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ => Swap.all_frequency_sharp j (v i))
  · simpa only [Finset.mul_sum] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ => all_frequency_reverse j (v i))

/-- 保留共同酉概率的有理配方；最终常数严格小于 2600。 -/
lemma remainder_absorption {a b p d s A B : ℝ}
    (hp : 0 ≤ p) (hd : 0 ≤ d) (hds : d ≤ (8/3)*s)
    (hAB : Swap.slope * B ≤ A)
    (ha : |a-p-A| ≤ 34*d*Real.sqrt p+8*d^2)
    (hb : |b-p-B| ≤ 34*d*Real.sqrt p+8*d^2) :
    Swap.slope*b ≤ a+2600*s^2 := by
  have hr := Swap.slope_pos
  have hrsmall := SwapMatching.slope_lt_one_sixteenth
  have hsq := Real.sq_sqrt hp
  have hroot := Real.sqrt_nonneg p
  have hRa := (abs_le.mp ha).1
  have hRb := mul_le_mul_of_nonneg_left (abs_le.mp hb).2 hr.le
  have hdp : 0 ≤ d*Real.sqrt p := mul_nonneg hd hroot
  have hgap : (15/16:ℝ)*p ≤ (1-Swap.slope)*p := by nlinarith
  have herr : (1+Swap.slope)*(34*d*Real.sqrt p+8*d^2) ≤
      (289/8:ℝ)*d*Real.sqrt p+(17/2:ℝ)*d^2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1/16-Swap.slope by linarith)
      (show 0 ≤ 34*d*Real.sqrt p+8*d^2 by positivity)]
  have hbase : (15/16:ℝ)*p-(289/8:ℝ)*d*Real.sqrt p-(17/2:ℝ)*d^2 ≤
      a-Swap.slope*b := by nlinarith
  have hcomplete : -(85561/240:ℝ)*d^2 ≤ a-Swap.slope*b := by
    nlinarith [sq_nonneg (15*Real.sqrt p-289*d)]
  have hdsq : d^2 ≤ (64/9:ℝ)*s^2 := by
    have hh := mul_self_le_mul_self hd hds
    nlinarith
  nlinarith [sq_nonneg s]

/-- 连续闭半空间的并保存局部外界；有限实现的小区间留出闭包余量。 -/
lemma closure_local_quadratic {S : Set (ℝ × ℝ)} {r C δ δ' : ℝ}
    (hδ : δ' < δ)
    (hS : ∀ z ∈ S, z.1+z.2 ≤ δ → r*z.2 ≤ z.1+C*(z.1+z.2)^2)
    {z : ℝ × ℝ} (hz : z ∈ closure S) (hs : z.1+z.2 ≤ δ') :
    r*z.2 ≤ z.1+C*(z.1+z.2)^2 := by
  let T : Set (ℝ × ℝ) := {z | δ ≤ z.1+z.2} ∪
    {z | r*z.2 ≤ z.1+C*(z.1+z.2)^2}
  have hclosed : IsClosed T := by
    apply IsClosed.union
    · exact isClosed_le continuous_const (continuous_fst.add continuous_snd)
    · apply isClosed_le <;> fun_prop
  have hsubset : S ⊆ T := by
    intro x hx
    by_cases hsmall : x.1+x.2 ≤ δ
    · exact Or.inr (hS x hx hsmall)
    · exact Or.inl (le_of_lt (lt_of_not_ge hsmall))
  have ht := closure_minimal hsubset hclosed hz
  rcases ht with hout | hin
  · exact False.elim (by dsimp at hout; linarith)
  · exact hin

/-- 直接展开正切锥的滤子定义：二阶误差在任意正缩放切向极限中消失。 -/
lemma local_quadratic_tangent {S : Set (ℝ × ℝ)} {r C δ u v : ℝ}
    (hδ : 0 < δ)
    (hS : ∀ z ∈ S, z.1+z.2 ≤ δ → r*z.2 ≤ z.1+C*(z.1+z.2)^2)
    (hv : (u,v) ∈ posTangentConeAt S (0,0)) : r*v ≤ u := by
  obtain ⟨ι, l, hl, c, d, hd, hmem, hlim⟩ := exists_fun_of_mem_tangentConeAt hv
  have : l.NeBot := hl
  have hd1 : Tendsto (fun i => (d i).1) l (𝓝 0) := by simpa using hd.fst_nhds
  have hd2 : Tendsto (fun i => (d i).2) l (𝓝 0) := by simpa using hd.snd_nhds
  have hc1 : Tendsto (fun i => (c i : ℝ)*(d i).1) l (𝓝 u) := by
    simpa [NNReal.smul_def] using hlim.fst_nhds
  have hc2 : Tendsto (fun i => (c i : ℝ)*(d i).2) l (𝓝 v) := by
    simpa [NNReal.smul_def] using hlim.snd_nhds
  have hsum : Tendsto (fun i => (d i).1+(d i).2) l (𝓝 0) := by
    simpa using hd1.add hd2
  have hsmall : ∀ᶠ i in l, (d i).1+(d i).2 ≤ δ :=
    (hsum.eventually (eventually_lt_nhds hδ)).mono (fun _ hi => hi.le)
  have hrem : Tendsto (fun i => C*((c i : ℝ)*(d i).1+(c i : ℝ)*(d i).2)*
      ((d i).1+(d i).2)) l (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul (hc1.add hc2)).mul hsum
  have hle : ∀ᶠ i in l, r*((c i : ℝ)*(d i).2) ≤
      (c i : ℝ)*(d i).1+C*((c i : ℝ)*(d i).1+(c i : ℝ)*(d i).2)*
      ((d i).1+(d i).2) := by
    filter_upwards [hmem, hsmall] with i hi hsi
    have hx := hS (d i) (by simpa only [Prod.mk_zero_zero, zero_add] using hi) hsi
    have hh := mul_le_mul_of_nonneg_left hx (c i).coe_nonneg
    nlinarith only [hh]
  have hh := le_of_tendsto_of_tendsto (tendsto_const_nhds.mul hc2) (hc1.add hrem) hle
  simpa using hh

lemma swap_mem_posTangent {S : Set (ℝ × ℝ)} {u v : ℝ}
    (hv : (u,v) ∈ posTangentConeAt S (0,0)) :
    (v,u) ∈ posTangentConeAt (Prod.swap ⁻¹' S) (0,0) := by
  obtain ⟨ι, l, hl, c, d, hd, hmem, hlim⟩ := exists_fun_of_mem_tangentConeAt hv
  have : l.NeBot := hl
  apply mem_tangentConeAt_of_seq l c (fun i => (d i).swap)
  · change Tendsto (fun i => ((d i).2, (d i).1)) l (𝓝 (0,0))
    exact hd.snd_nhds.prodMk_nhds hd.fst_nhds
  · filter_upwards [hmem] with i hi
    simpa only [Prod.mk_zero_zero, zero_add, Set.mem_preimage, Prod.swap_swap] using hi
  · change Tendsto (fun i => (c i • (d i).2, c i • (d i).1)) l (𝓝 (v,u))
    exact hlim.snd_nhds.prodMk_nhds hlim.fst_nhds

lemma cone_inequalities_nonneg {u v : ℝ}
    (hu : Swap.slope*v ≤ u) (hv : Swap.slope*u ≤ v) : 0 ≤ u ∧ 0 ≤ v := by
  have hr := Swap.slope_pos
  have hr1 := Swap.slope_lt_one
  have hsum : 0 ≤ u+v := by
    by_contra! hn
    have hh := mul_pos (show 0 < 1-Swap.slope by linarith) (neg_pos.mpr hn)
    nlinarith
  constructor <;> nlinarith

/-- 双向局部二次界与已构造的所有内侧方向，给出真正正切锥的精确集合等式。 -/
lemma tangent_eq_of_local_quadratic {C δ : ℝ} (hδ : 0 < δ)
    (hQ : ∀ z ∈ Q2, z.1+z.2 ≤ δ →
      Swap.slope*z.2 ≤ z.1+C*(z.1+z.2)^2 ∧
      Swap.slope*z.1 ≤ z.2+C*(z.1+z.2)^2) :
    posTangentConeAt Q2 (0,0) =
      {z : ℝ × ℝ | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ Swap.slope*z.2 ≤ z.1 ∧ Swap.slope*z.1 ≤ z.2} := by
  ext z
  constructor
  · intro hz
    have ha := local_quadratic_tangent hδ (fun x hx hs => (hQ x hx hs).1) hz
    have hb := local_quadratic_tangent hδ (S := Prod.swap ⁻¹' Q2)
      (r := Swap.slope) (C := C) (fun x hx hs => by
        have hh := (hQ x.swap hx (by simpa [add_comm] using hs)).2
        simpa [add_comm] using hh) (swap_mem_posTangent hz)
    exact ⟨(cone_inequalities_nonneg ha hb).1, (cone_inequalities_nonneg ha hb).2, ha, hb⟩
  · rintro ⟨_, _, ha, hb⟩
    exact SwapMatching.all_allowed_directions_mem_posTangent ha hb

/-- 任意合法规范生成元的二次外界；B1、B2 和全圈数谱界均实际调用。 -/
theorem canonical_quadratic_outer (h : BlochVec) (K : Matrix (Fin 3) (Fin 3) ℂ)
    (hK : K.PosSemidef)
    (hs : (canonicalOutput h K 1).1+(canonicalOutput h K 1).2 ≤ 1/64) :
    Swap.slope*(canonicalOutput h K 1).2 ≤ (canonicalOutput h K 1).1+
      2600*((canonicalOutput h K 1).1+(canonicalOutput h K 1).2)^2 ∧
    Swap.slope*(canonicalOutput h K 1).1 ≤ (canonicalOutput h K 1).2+
      2600*((canonicalOutput h K 1).1+(canonicalOutput h K 1).2)^2 := by
  let s := (canonicalOutput h K 1).1+(canonicalOutput h K 1).2
  obtain ⟨hx,K',j,_,hK',_,hout,_,_,_,ha,hb⟩ :=
    SwapComparison.canonical_near_swap_comparison_all_axes h K hK s rfl hs
  have hr := Rigidity.canonicalOutput_dissipative_rigidity ![hx,0,h 2] K' hK'
    s (by rw [hout]) (by dsimp [s]; linarith)
  have hd : dissipationSize K' ≤ (8/3)*s := by
    have ht : dissipationSize K'=K'.trace.re := by
      simp [dissipationSize, Matrix.trace, Complex.re_sum]
    rw [ht]
    exact hr.1.trans hr.2
  have hp := SwapComparison.unitaryProbability_nonneg ![hx,0,h 2] (t := 1) (by norm_num)
  have hdn := dissipationSize_nonneg K' hK'
  have hsharp := reference_trace_sharp j K' hK'
  exact ⟨remainder_absorption hp hdn hd hsharp.1 ha hb,
    remainder_absorption hp hdn hd hsharp.2 hb ha⟩

/-- 原始 finiteOutputs 包括任意非负演化时间；时间归一化在正式等价中完成。 -/
theorem finiteOutputs_quadratic_outer {z : ℝ × ℝ} (hz : z ∈ finiteOutputs)
    (hs : z.1+z.2 ≤ 1/64) :
    Swap.slope*z.2 ≤ z.1+2600*(z.1+z.2)^2 ∧
    Swap.slope*z.1 ≤ z.2+2600*(z.1+z.2)^2 := by
  rw [finiteOutputs_eq_canonicalOutputs] at hz
  obtain ⟨h,K,hK,rfl⟩ := hz
  exact canonical_quadratic_outer h K hK hs

/-- 主稿的原始闭包结论；此类型没有 B2、逼近或有限达到的假设。 -/
theorem Q2_quadratic_outer {a b : ℝ} (hz : (a,b) ∈ Q2) (hs : a+b ≤ 1/256) :
    Swap.slope*b ≤ a+2600*(a+b)^2 ∧ Swap.slope*a ≤ b+2600*(a+b)^2 := by
  have hfirst : ∀ z ∈ finiteOutputs, z.1+z.2 ≤ (1/64:ℝ) →
      Swap.slope*z.2 ≤ z.1+2600*(z.1+z.2)^2 :=
    fun z hz hs => (finiteOutputs_quadratic_outer hz hs).1
  have hsecond : ∀ z ∈ Prod.swap ⁻¹' finiteOutputs, z.1+z.2 ≤ (1/64:ℝ) →
      Swap.slope*z.2 ≤ z.1+2600*(z.1+z.2)^2 := by
    intro z hz hs
    have hh := (finiteOutputs_quadratic_outer hz (by simpa [add_comm] using hs)).2
    simpa [add_comm] using hh
  constructor
  · exact closure_local_quadratic (δ' := (1/256:ℝ)) (by norm_num) hfirst hz hs
  · have hzswap : (b,a) ∈ closure (Prod.swap ⁻¹' finiteOutputs) := by
      have hh := mem_closure_image continuous_swap.continuousAt hz
      simpa only [Set.image_swap_eq_preimage_swap, Prod.swap_prod_mk] using hh
    have hh := closure_local_quadratic (δ' := (1/256:ℝ)) (by norm_num)
      hsecond hzswap (by simpa [add_comm] using hs)
    simpa [add_comm] using hh

/-- 与论文的减法写法完全相同。 -/
theorem Q2_quadratic_outer_sub {a b : ℝ} (hz : (a,b) ∈ Q2) (hs : a+b ≤ 1/256) :
    Swap.slope*b-2600*(a+b)^2 ≤ a ∧ Swap.slope*a-2600*(a+b)^2 ≤ b := by
  obtain ⟨ha,hb⟩ := Q2_quadratic_outer hz hs
  constructor <;> linarith

/-- 原始 Q2 在交换端点的精确 Bouligand 正切锥，包含正坐标约束。 -/
theorem Q2_posTangentConeAt_zero :
    posTangentConeAt Q2 (0,0) =
      {z : ℝ × ℝ | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ Swap.slope*z.2 ≤ z.1 ∧ Swap.slope*z.1 ≤ z.2} := by
  apply tangent_eq_of_local_quadratic (C := 2600) (δ := 1/256) (by norm_num)
  intro z hz hs
  exact Q2_quadratic_outer hz hs

theorem mem_Q2_posTangentConeAt_zero_iff (u v : ℝ) :
    (u,v) ∈ posTangentConeAt Q2 (0,0) ↔
      0 ≤ u ∧ 0 ≤ v ∧ Swap.slope*v ≤ u ∧ Swap.slope*u ≤ v := by
  rw [Q2_posTangentConeAt_zero]
  rfl

#print axioms reference_trace_sharp
#print axioms remainder_absorption
#print axioms closure_local_quadratic
#print axioms local_quadratic_tangent
#print axioms tangent_eq_of_local_quadratic
#print axioms canonical_quadratic_outer
#print axioms finiteOutputs_quadratic_outer
#print axioms Q2_quadratic_outer
#print axioms Q2_quadratic_outer_sub
#print axioms Q2_posTangentConeAt_zero
#print axioms mem_Q2_posTangentConeAt_zero_iff
#check @Q2_quadratic_outer
#check Q2_posTangentConeAt_zero
#check mem_Q2_posTangentConeAt_zero_iff
end TwoStateQuantumEmbedding.SwapCone
