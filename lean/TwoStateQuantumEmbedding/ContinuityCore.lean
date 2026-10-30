import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

open Set Filter Topology

namespace QuantumEmbedding.Continuity

/-- 固定横坐标的对称填充区域。这里尚未定义 GKSL 可达集合。 -/
def region (D : Set ℝ) (F : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ D ∧ |p.2| ≤ F p.1}

/-- 闭填充区域与严格切片内部性足以推出包络连续；连续性不是前提。 -/
theorem continuousOn_subset_of_closed_strictInterior
    (D E : Set ℝ) (F : ℝ → ℝ) (hED : E ⊆ D)
    (hF : ∀ x ∈ D, 0 ≤ F x)
    (hclosed : IsClosed (region D F))
    (hinterior : ∀ x ∈ E, ∀ z, |z| < F x →
      (x, z) ∈ interior (region D F)) :
    ContinuousOn F E := by
  intro x hx
  change Tendsto F (𝓝[E] x) (𝓝 (F x))
  apply tendsto_order.2
  constructor
  · intro a ha
    by_cases ha0 : a < 0
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact ha0.trans_le (hF y (hED hy))
    · obtain ⟨r, har, hr⟩ := exists_between ha
      have hr0 : 0 ≤ r := le_trans (le_of_not_gt ha0) har.le
      have hpoint : (x, r) ∈ interior (region D F) :=
        hinterior x hx r (by simpa [abs_of_nonneg hr0] using hr)
      have hcont : Continuous (fun y : ℝ => (y, r)) :=
        continuous_id.prodMk continuous_const
      have hevent : ∀ᶠ y in 𝓝 x, (y, r) ∈ region D F :=
        hcont.continuousAt.preimage_mem_nhds
          (mem_interior_iff_mem_nhds.mp hpoint)
      filter_upwards [hevent.filter_mono nhdsWithin_le_nhds] with y hy
      exact har.trans_le (by simpa [region, abs_of_nonneg hr0] using hy.2)
  · intro b hb
    have hb0 : 0 ≤ b := le_trans (hF x (hED hx)) hb.le
    have hpoint : (x, b) ∈ (region D F)ᶜ := by
      intro h
      have : b ≤ F x := by simpa [abs_of_nonneg hb0] using h.2
      exact (not_le_of_gt hb) this
    have hcont : Continuous (fun y : ℝ => (y, b)) :=
      continuous_id.prodMk continuous_const
    have hevent : ∀ᶠ y in 𝓝 x, (y, b) ∈ (region D F)ᶜ :=
      hcont.continuousAt.preimage_mem_nhds (hclosed.isOpen_compl.mem_nhds hpoint)
    filter_upwards [hevent.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with y hy hDy
    by_contra hlt
    exact hy ⟨hED hDy, by simpa [abs_of_nonneg hb0] using le_of_not_gt hlt⟩

/-- 上一定理在整个横坐标域上的版本。 -/
theorem continuousOn_of_closed_strictInterior
    (D : Set ℝ) (F : ℝ → ℝ)
    (hF : ∀ x ∈ D, 0 ≤ F x)
    (hclosed : IsClosed (region D F))
    (hinterior : ∀ x ∈ D, ∀ z, |z| < F x →
      (x, z) ∈ interior (region D F)) :
    ContinuousOn F D :=
  continuousOn_subset_of_closed_strictInterior D D F Subset.rfl hF hclosed hinterior

/-- 切片端点不可能是二维内部点，不需要预先知道 F 连续。 -/
theorem endpoint_not_interior
    (D : Set ℝ) (F : ℝ → ℝ) {x z : ℝ}
    (hx : x ∈ D) (hz : |z| = F x) :
    (x, z) ∉ interior (region D F) := by
  intro hpoint
  have hcont : Continuous (fun t : ℝ => (x, t)) :=
    continuous_const.prodMk continuous_id
  have hpre : {t : ℝ | (x, t) ∈ region D F} ∈ 𝓝 z :=
    hcont.continuousAt.preimage_mem_nhds
      (mem_interior_iff_mem_nhds.mp hpoint)
  have heq : {t : ℝ | (x, t) ∈ region D F} = Icc (-F x) (F x) := by
    ext t
    simp [region, hx, abs_le]
  rw [heq] at hpre
  have hzint : z ∈ interior (Icc (-F x) (F x)) :=
    mem_interior_iff_mem_nhds.mpr hpre
  rw [interior_Icc] at hzint
  have hlt : |z| < F x := abs_lt.mpr hzint
  exact (ne_of_lt hlt) hz

/-- 在闭填充区域中，严格切片全部内部当且仅当不存在额外竖直边界。 -/
theorem frontier_eq_abs_graph
    (D : Set ℝ) (F : ℝ → ℝ)
    (hclosed : IsClosed (region D F))
    (hinterior : ∀ x ∈ D, ∀ z, |z| < F x →
      (x, z) ∈ interior (region D F)) :
    frontier (region D F) = {p | p.1 ∈ D ∧ |p.2| = F p.1} := by
  rw [hclosed.frontier_eq]
  ext p
  constructor
  · rintro ⟨hp, hn⟩
    refine ⟨hp.1, le_antisymm hp.2 ?_⟩
    by_contra h
    exact hn (hinterior p.1 hp.1 p.2 (lt_of_not_ge h))
  · rintro ⟨hx, hz⟩
    exact ⟨⟨hx, hz.le⟩, endpoint_not_interior D F hx hz⟩

/-- 将绝对值边界精确写成上下两张图像。 -/
theorem frontier_eq_two_graphs
    (D : Set ℝ) (F : ℝ → ℝ)
    (hF : ∀ x ∈ D, 0 ≤ F x)
    (hclosed : IsClosed (region D F))
    (hinterior : ∀ x ∈ D, ∀ z, |z| < F x →
      (x, z) ∈ interior (region D F)) :
    frontier (region D F) =
      {p | p.1 ∈ D ∧ p.2 = F p.1} ∪
      {p | p.1 ∈ D ∧ p.2 = -F p.1} := by
  rw [frontier_eq_abs_graph D F hclosed hinterior]
  ext p
  constructor
  · rintro ⟨hx, hz⟩
    rcases le_total 0 p.2 with hz0 | hz0
    · exact Or.inl ⟨hx, by simpa [abs_of_nonneg hz0] using hz⟩
    · right
      refine ⟨hx, ?_⟩
      rw [abs_of_nonpos hz0] at hz
      linarith
  · rintro (⟨hx, hz⟩ | ⟨hx, hz⟩)
    · exact ⟨hx, by simp [hz, abs_of_nonneg (hF p.1 hx)]⟩
    · exact ⟨hx, by simp [hz, abs_of_nonneg (hF p.1 hx)]⟩

/-- 一个真实矩形即给严格切片点的二维内部性。 -/
theorem interior_of_rectangle
    {Q : Set (ℝ × ℝ)} {a b r x z : ℝ}
    (hax : a < x) (hxb : x < b) (hzr : |z| < r)
    (hrect : Icc a b ×ˢ Icc (-r) r ⊆ Q) :
    (x, z) ∈ interior Q := by
  apply mem_interior_iff_mem_nhds.mpr
  have hbox : Ioo a b ×ˢ Ioo (-r) r ∈ 𝓝 (x, z) :=
    (isOpen_Ioo.prod isOpen_Ioo).mem_nhds ⟨⟨hax, hxb⟩, abs_lt.mp hzr⟩
  apply Filter.mem_of_superset hbox
  intro p hp
  exact hrect ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩

/-- 连通参数带的介值性质与合法漂移填充产生真实矩形。 -/
theorem rectangle_of_connected_parameters
    {P : Type*} [TopologicalSpace P]
    (Q : Set (ℝ × ℝ)) (X Z : P → ℝ) (U : Set P)
    {pminus pplus : P} {r : ℝ}
    (hU : IsPreconnected U) (hm : pminus ∈ U) (hp : pplus ∈ U)
    (hX : ContinuousOn X U)
    (hZ : ∀ p ∈ U, r ≤ Z p)
    (hfill : ∀ p ∈ U, ∀ z, |z| ≤ Z p → (X p, z) ∈ Q) :
    Icc (X pminus) (X pplus) ×ˢ Icc (-r) r ⊆ Q := by
  intro q hq
  obtain ⟨p, hpU, hpX⟩ := hU.intermediate_value hm hp hX hq.1
  have hz : |q.2| ≤ Z p := (abs_le.mpr hq.2).trans (hZ p hpU)
  simpa [hpX] using hfill p hpU q.2 hz

/-- 这是条件参数桥接定理；尚需从 GKSL 矩条件排除得到 hcover。 -/
theorem continuity_frontier_of_parametric_coverage
    {P : Type*} [TopologicalSpace P]
    (D : Set ℝ) (F : ℝ → ℝ) (X Z : P → ℝ)
    (hF : ∀ x ∈ D, 0 ≤ F x)
    (hclosed : IsClosed (region D F))
    (hfill : ∀ p z, |z| ≤ Z p → (X p, z) ∈ region D F)
    (hcover : ∀ x ∈ D, ∀ r, 0 < r → r < F x →
      ∃ (U : Set P) (pm pp : P), IsPreconnected U ∧ pm ∈ U ∧ pp ∈ U ∧
        X pm < x ∧ x < X pp ∧ ContinuousOn X U ∧ ∀ p ∈ U, r ≤ Z p) :
    ContinuousOn F D ∧
      frontier (region D F) =
        {p | p.1 ∈ D ∧ p.2 = F p.1} ∪
        {p | p.1 ∈ D ∧ p.2 = -F p.1} := by
  have hi : ∀ x ∈ D, ∀ z, |z| < F x →
      (x, z) ∈ interior (region D F) := by
    intro x hx z hz
    obtain ⟨r, hzr, hrF⟩ := exists_between hz
    have hr : 0 < r := (abs_nonneg z).trans_lt hzr
    obtain ⟨U, pm, pp, hU, hm, hp, hxm, hxp, hX, hZ⟩ :=
      hcover x hx r hr hrF
    apply interior_of_rectangle hxm hxp hzr
    exact rectangle_of_connected_parameters (region D F) X Z U hU hm hp hX hZ
      (fun p _ z hz => hfill p z hz)
  exact ⟨continuousOn_of_closed_strictInterior D F hF hclosed hi,
    frontier_eq_two_graphs D F hF hclosed hi⟩

/-- 非局部极小在每个参数邻域内给出严格更小的输出。 -/
theorem exists_lower_of_not_localMin
    {P : Type*} [TopologicalSpace P] (X : P → ℝ) {p : P}
    (hmin : ¬ IsLocalMin X p) {U : Set P} (hU : U ∈ 𝓝 p) :
    ∃ q ∈ U, X q < X p := by
  by_contra h
  push Not at h
  apply hmin
  change ∀ᶠ q in 𝓝 p, X p ≤ X q
  filter_upwards [hU] with q hq
  exact h q hq

/-- 非局部极大在每个参数邻域内给出严格更大的输出。 -/
theorem exists_upper_of_not_localMax
    {P : Type*} [TopologicalSpace P] (X : P → ℝ) {p : P}
    (hmax : ¬ IsLocalMax X p) {U : Set P} (hU : U ∈ 𝓝 p) :
    ∃ q ∈ U, X p < X q := by
  by_contra h
  push Not at h
  apply hmax
  change ∀ᶠ q in 𝓝 p, X q ≤ X p
  filter_upwards [hU] with q hq
  exact h q hq

/-- 有限达到、参数连续及无局部极值给包络连续与完整边界。
    参数空间可以取合法生成元的子空间；GKSL 的这些前提仍须另证。 -/
theorem continuity_frontier_of_attainment_no_extrema
    {P : Type*} [TopologicalSpace P] [LocallyConnectedSpace P]
    (D : Set ℝ) (F : ℝ → ℝ) (X Z : P → ℝ)
    (hF : ∀ x ∈ D, 0 ≤ F x)
    (hclosed : IsClosed (region D F)) (hX : Continuous X) (hZ : Continuous Z)
    (hfill : ∀ p z, |z| ≤ Z p → (X p, z) ∈ region D F)
    (hattain : ∀ x ∈ D, 0 < F x → ∃ p, X p = x ∧ Z p = F x ∧
      ¬ IsLocalMin X p ∧ ¬ IsLocalMax X p) :
    ContinuousOn F D ∧
      frontier (region D F) =
        {p | p.1 ∈ D ∧ p.2 = F p.1} ∪
        {p | p.1 ∈ D ∧ p.2 = -F p.1} := by
  apply continuity_frontier_of_parametric_coverage D F X Z hF hclosed hfill
  intro x hx r hr hrF
  obtain ⟨p, hpX, hpZ, hpmin, hpmax⟩ := hattain x hx (hr.trans hrF)
  have hband : {q | r < Z q} ∈ 𝓝 p :=
    (isOpen_lt continuous_const hZ).mem_nhds (by simpa [hpZ] using hrF)
  obtain ⟨U, hUnhds, hUconn, hUsub⟩ :=
    locallyConnectedSpace_iff_connected_subsets.mp inferInstance p _ hband
  obtain ⟨pm, hm, hmx⟩ := exists_lower_of_not_localMin X hpmin hUnhds
  obtain ⟨pp, hp, hpx⟩ := exists_upper_of_not_localMax X hpmax hUnhds
  refine ⟨U, pm, pp, hUconn, hm, hp, ?_, ?_, hX.continuousOn, ?_⟩
  · simpa [hpX] using hmx
  · simpa [hpX] using hpx
  · intro q hq
    exact (hUsub hq).le

/-- 针对负行列式区间的版本：只在目标子域 E 要求有限达到。
    这避免对 x=0 的重置闭包端点加入错误的有限达到前提。 -/
theorem continuityOn_subset_of_attainment_no_extrema
    {P : Type*} [TopologicalSpace P] [LocallyConnectedSpace P]
    (D E : Set ℝ) (F : ℝ → ℝ) (X Z : P → ℝ) (hED : E ⊆ D)
    (hF : ∀ x ∈ D, 0 ≤ F x)
    (hclosed : IsClosed (region D F)) (hX : Continuous X) (hZ : Continuous Z)
    (hfill : ∀ p z, |z| ≤ Z p → (X p, z) ∈ region D F)
    (hattain : ∀ x ∈ E, 0 < F x → ∃ p, X p = x ∧ Z p = F x ∧
      ¬ IsLocalMin X p ∧ ¬ IsLocalMax X p) :
    ContinuousOn F E ∧ (∀ x ∈ E, ∀ z, |z| < F x →
      (x, z) ∈ interior (region D F)) := by
  have hi : ∀ x ∈ E, ∀ z, |z| < F x →
      (x, z) ∈ interior (region D F) := by
    intro x hx z hz
    obtain ⟨r, hzr, hrF⟩ := exists_between hz
    have hr : 0 < r := (abs_nonneg z).trans_lt hzr
    obtain ⟨p, hpX, hpZ, hpmin, hpmax⟩ := hattain x hx (hr.trans hrF)
    have hband : {q | r < Z q} ∈ 𝓝 p :=
      (isOpen_lt continuous_const hZ).mem_nhds (by simpa [hpZ] using hrF)
    obtain ⟨U, hUnhds, hUconn, hUsub⟩ :=
      locallyConnectedSpace_iff_connected_subsets.mp inferInstance p _ hband
    obtain ⟨pm, hm, hmx⟩ := exists_lower_of_not_localMin X hpmin hUnhds
    obtain ⟨pp, hp, hpx⟩ := exists_upper_of_not_localMax X hpmax hUnhds
    apply interior_of_rectangle (by simpa [hpX] using hmx)
      (by simpa [hpX] using hpx) hzr
    exact rectangle_of_connected_parameters (region D F) X Z U hUconn hm hp hX.continuousOn
      (fun q hq => (hUsub hq).le) (fun q _ z hz => hfill q z hz)
  exact ⟨continuousOn_subset_of_closed_strictInterior D E F hED hF hclosed hi, hi⟩

/-- 连续尾段逼近零即覆盖整个左侧区间，不要求曲线单调。 -/
theorem continuous_curve_covers_left_interval
    (X : ℝ → ℝ) (T : ℝ) (hX : ContinuousOn X (Ici T))
    (hlim : Tendsto X atTop (𝓝 0)) : Ico (X T) 0 ⊆ X '' Ici T := by
  exact isPreconnected_Ici.intermediate_value_Ico (by simp)
    (le_principal_iff.mpr (eventually_ge_atTop T)) hX hlim

/-- 重置端点桥接：合法连续曲线的偏置趋于 -1，推出包络零点左极限。
    曲线的 GKSL 实现及具体指数公式尚需独立形式化。 -/
theorem envelope_left_limit_of_reset_curve
    (F X Z : ℝ → ℝ) (Lbase : ℝ)
    (hX : ContinuousOn X (Ici Lbase))
    (hxneg : ∀ L ≥ Lbase, X L < 0)
    (hXlim : Tendsto X atTop (𝓝 0))
    (hZlim : Tendsto Z atTop (𝓝 (-1)))
    (hfill : ∀ L ≥ Lbase, |Z L| ≤ F (X L))
    (hupper : ∀ x < 0, F x ≤ 1) :
    Tendsto F (𝓝[<] 0) (𝓝 1) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hz : ∀ᶠ L in atTop, Z L < -a :=
      (tendsto_order.mp hZlim).2 (-a) (by linarith)
    obtain ⟨T, hT⟩ := eventually_atTop.mp hz
    let T' := max T Lbase
    have hTbase : Lbase ≤ T' := le_max_right _ _
    have hTT : T ≤ T' := le_max_left _ _
    have hXT : X T' < 0 := hxneg T' hTbase
    have hXtail : ContinuousOn X (Ici T') :=
      hX.mono (Ici_subset_Ici.mpr hTbase)
    have hcoverage := continuous_curve_covers_left_interval X T' hXtail hXlim
    have hnear : ∀ᶠ x in 𝓝 (0 : ℝ), X T' < x := Ioi_mem_nhds hXT
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with x hlow hneg
    obtain ⟨L, hL, hLX⟩ := hcoverage ⟨hlow.le, hneg⟩
    have hZL : Z L < -a := hT L (hTT.trans hL)
    have hFL := hfill L (hTbase.trans hL)
    have habs : -Z L ≤ |Z L| := neg_le_abs _
    rw [hLX] at hFL
    linarith
  · intro b hb
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hupper x hx).trans_lt hb

/-- KKT 方向归约后待排除的三阶实矩阵；该方向归约本身尚未形式化。 -/
def reducedMatrix (L d a b r : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-d, a, r; b, -(L - d), 0; -r, 0, -L]

/-- 秩二实部极小条件给出的归一化矩积分。 -/
noncomputable def normalizedMoment : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-1 / 4, 0, 0; 0, -1 / 4, 0; 0, 0, 1 / 4]

/-- 直接矩阵行列式展开，不通过数值测试代替恒等式。 -/
theorem reducedMatrix_det (L d a b r s : ℝ) :
    Matrix.det (s • (1 : Matrix (Fin 3) (Fin 3) ℝ) - reducedMatrix L d a b r) =
      (s + L) * (s ^ 2 + L * s + d * (L - d) - a * b) +
        r ^ 2 * (s + L - d) := by
  simp [Matrix.det_fin_three, reducedMatrix]
  ring

/-- 第二个交换矩的左端。 -/
theorem reducedMatrix_trace_second (L d a b r : ℝ) :
    Matrix.trace (normalizedMoment * (reducedMatrix L d a b r) ^ 2) =
      (d * (L - d) - a * b) / 2 := by
  simp [Matrix.trace_fin_three, normalizedMoment, reducedMatrix, pow_two]
  ring

/-- 第一交换矩与线性指数余式的精确消元。 -/
theorem reducedMatrix_first_moment (L d a b r b1 : ℝ) :
    (reducedMatrix L d a b r *
      (((L - 1 / 2) * b1) • (1 : Matrix (Fin 3) (Fin 3) ℝ) +
        b1 • reducedMatrix L d a b r)) 2 2 = b1 * (L / 2 - r ^ 2) := by
  norm_num [reducedMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
  ring

/-- 正的一次指数系数和第一矩强迫 r²=L/2。 -/
theorem coupling_of_first_moment {L d a b r b1 : ℝ} (hb1 : 0 < b1)
    (hmoment : (reducedMatrix L d a b r *
      (((L - 1 / 2) * b1) • (1 : Matrix (Fin 3) (Fin 3) ℝ) +
        b1 • reducedMatrix L d a b r)) 2 2 = 0) : r ^ 2 = L / 2 := by
  rw [reducedMatrix_first_moment] at hmoment
  have h := (mul_eq_zero.mp hmoment).resolve_left (ne_of_gt hb1)
  linarith

/-- 第二交换矩右端的直接三阶矩阵乘法。 -/
theorem reducedMatrix_second_moment (L d a b r b1 : ℝ) :
    ((reducedMatrix L d a b r) ^ 2 *
      (((L - 1 / 2) * b1) • (1 : Matrix (Fin 3) (Fin 3) ℝ) +
        b1 • reducedMatrix L d a b r)) 2 2 =
      b1 * ((L - 1 / 2) * (L ^ 2 - r ^ 2) + r ^ 2 * (d + 2 * L) - L ^ 3) := by
  norm_num [reducedMatrix, Matrix.mul_apply, Fin.sum_univ_succ, pow_two, Matrix.one_apply]
  ring

/-- 两个交换矩合并，给出余下平面行列式。 -/
theorem determinant_of_second_moment {L d a b r b1 alpha : ℝ}
    (hr : r ^ 2 = L / 2) (hab : alpha * b1 = 1 / 2)
    (hmoment : Matrix.trace (normalizedMoment * (reducedMatrix L d a b r) ^ 2) =
      alpha * (((reducedMatrix L d a b r) ^ 2 *
        (((L - 1 / 2) * b1) • (1 : Matrix (Fin 3) (Fin 3) ℝ) +
          b1 • reducedMatrix L d a b r)) 2 2)) :
    d * (L - d) - a * b = L * d / 2 + L / 4 := by
  rw [reducedMatrix_trace_second, reducedMatrix_second_moment, hr] at hmoment
  rw [← mul_assoc, hab] at hmoment
  nlinarith [hmoment]

/-- 矩消元后的完整特征行列式，包括特殊谱点的精确值。 -/
theorem reducedMatrix_polynomial {L d a b r : ℝ}
    (hr : r ^ 2 = L / 2) (hN : d * (L - d) - a * b = L * d / 2 + L / 4) :
    (∀ s : ℝ,
      Matrix.det (s • (1 : Matrix (Fin 3) (Fin 3) ℝ) - reducedMatrix L d a b r) =
        s ^ 3 + 2 * L * s ^ 2 + (L ^ 2 + L * d / 2 + 3 * L / 4) * s +
          d * L * (L - 1) / 2 + 3 * L ^ 2 / 4) ∧
      Matrix.det ((1 - L) • (1 : Matrix (Fin 3) (Fin 3) ℝ) -
        reducedMatrix L d a b r) = 1 - L / 4 := by
  have hdet : ∀ s : ℝ,
      Matrix.det (s • (1 : Matrix (Fin 3) (Fin 3) ℝ) - reducedMatrix L d a b r) =
        (s + L) * (s ^ 2 + L * s + (L * d / 2 + L / 4)) +
          (L / 2) * (s + L - d) := by
    intro s
    rw [reducedMatrix_det, hr]
    have hinner : s ^ 2 + L * s + d * (L - d) - a * b =
        s ^ 2 + L * s + (L * d / 2 + L / 4) := by linarith [hN]
    rw [hinner]
  constructor
  · intro s
    rw [hdet]
    ring
  · rw [hdet]
    ring

/-- 用正项级数核验谱排除中使用的有理指数下界。 -/
theorem exp_five_gt : (115 : ℝ) < Real.exp 5 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 5) 8
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-- 048 中 V≥4 分支的指数增长矛盾；不借助浮点计算。 -/
theorem quadratic_lt_exp_of_four_le {V : ℝ} (hV : 4 ≤ V) :
    2 * V ^ 2 + 13 * V + 31 < Real.exp (V + 1) := by
  let s := V - 4
  have hs : 0 ≤ s := by dsimp [s]; linarith
  have hpolypos : 0 < 1 + s + s ^ 2 / 2 := by positivity
  have hm1 : 115 * (1 + s + s ^ 2 / 2) <
      Real.exp 5 * (1 + s + s ^ 2 / 2) :=
    mul_lt_mul_of_pos_right exp_five_gt hpolypos
  have hm2 : Real.exp 5 * (1 + s + s ^ 2 / 2) ≤
      Real.exp 5 * Real.exp s :=
    mul_le_mul_of_nonneg_left (Real.quadratic_le_exp_of_nonneg hs) (Real.exp_pos 5).le
  have hp : 2 * V ^ 2 + 13 * V + 31 ≤ 115 * (1 + s + s ^ 2 / 2) := by
    dsimp [s] at hs ⊢
    nlinarith [sq_nonneg (V - 4)]
  have heq : Real.exp 5 * Real.exp s = Real.exp (V + 1) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [s]
    ring
  exact heq ▸ hp.trans_lt (hm1.trans_le hm2)

/-- 一个简单指数上界替代手稿中的对数求导步骤。 -/
theorem exp_two_mul_lt_square {t : ℝ} (ht : 0 < t) (htop : t < 1 / 2) :
    Real.exp (2 * t) < (1 + 2 * t) ^ 2 := by
  have ht1 : t < 1 := by linarith
  have hden : 0 < 1 - t := by linarith
  have hfrac : (1 : ℝ) / (1 - t) < 1 + 2 * t := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith [mul_pos ht (show 0 < 1 / 2 - t by linarith)]
  have he : Real.exp t < 1 + 2 * t :=
    (Real.exp_bound_div_one_sub_of_interval ht.le ht1).trans_lt hfrac
  rw [show 2 * t = t + t by ring, Real.exp_add]
  nlinarith [Real.exp_pos t]

/-- 高频谱余项的最后完整矛盾链：输入均为明确的谱标量关系。 -/
theorem no_high_frequency_remainder
    {V t w : ℝ} (hV : 0 < V) (ht : 0 < t) (hw : 2 * Real.pi < w)
    (hrel : 4 * w ^ 2 = V * (1 / t - V - 2))
    (hupper : w ^ 2 < (V + 3) ^ 2 / 4 + (t + 1) ^ 2 / 2 +
      3 * (V + t + 4) / 4)
    (hmod : (1 + 2 * t) ^ 2 * Real.exp (V + 1 - 2 * t) = 4 + 2 * V + V / t) :
    False := by
  have hw6 : 6 < w := by linarith [Real.pi_gt_three]
  have hw0 : 0 < w := by linarith
  have hrelmul : 4 * w ^ 2 * t = V * (1 - t * (V + 2)) := by
    have h := congrArg (fun a : ℝ => a * t) hrel
    field_simp [ne_of_gt ht] at h
    nlinarith [h]
  have hfactor : 0 < 1 - t * (V + 2) := by
    apply (mul_pos_iff_of_pos_left hV).mp
    rw [← hrelmul]
    positivity
  have hthalf : t < 1 / 2 := by
    nlinarith [mul_pos ht hV]
  have ht2 : t ^ 2 < 1 / 4 := by
    nlinarith [mul_pos ht (show 0 < 1 / 2 - t by linarith)]
  have hrel' : 4 * w ^ 2 = V / t - V ^ 2 - 2 * V := by
    convert hrel using 1
    ring
  have hquot : V / t < 2 * V ^ 2 + 11 * V + 27 := by
    nlinarith [hrel', hupper]
  have hexp : Real.exp (V + 1) < 4 + 2 * V + V / t := by
    calc
      Real.exp (V + 1) =
          Real.exp (V + 1 - 2 * t) * Real.exp (2 * t) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ < Real.exp (V + 1 - 2 * t) * (1 + 2 * t) ^ 2 :=
        mul_lt_mul_of_pos_left (exp_two_mul_lt_square ht hthalf) (Real.exp_pos _)
      _ = 4 + 2 * V + V / t := by simpa [mul_comm] using hmod
  have hexpupper : Real.exp (V + 1) < 2 * V ^ 2 + 13 * V + 31 := by
    linarith
  have hV4 : V < 4 := by
    by_contra h
    exact (not_lt_of_gt (quadratic_lt_exp_of_four_le (le_of_not_gt h))) hexpupper
  have hV2 : V ^ 2 < 16 := by
    nlinarith [mul_pos hV (show 0 < 4 - V by linarith)]
  have hwupper : w ^ 2 < 79 / 4 := by
    nlinarith [hupper]
  nlinarith [sq_nonneg (w - 6)]

/-- 正弦相位关系排除第一整圈，允许任意更高圈数。 -/
theorem frequency_gt_two_pi
    {u w : ℝ} (hu : 3 < u) (hw : 0 < w) (hsin : 0 < Real.sin w)
    (hphase : w * Real.cos w = (u - 1) / 2 * Real.sin w) :
    2 * Real.pi < w := by
  have hprod : Real.sin w < w * Real.cos w := by
    nlinarith [mul_pos (show 0 < (u - 1) / 2 - 1 by linarith) hsin]
  by_contra h
  have hw2 : w ≤ 2 * Real.pi := le_of_not_gt h
  by_cases hhalf : w < Real.pi / 2
  · have hc : 0 < Real.cos w :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hhalf⟩
    have ht := Real.lt_tan hw hhalf
    rw [Real.tan_eq_sin_div_cos] at ht
    have := (lt_div_iff₀ hc).mp ht
    linarith
  · by_cases hwpi : w ≤ Real.pi
    · have hc := Real.cos_nonpos_of_pi_div_two_le_of_le
        (le_of_not_gt hhalf) (show w ≤ Real.pi + Real.pi / 2 by linarith [Real.pi_pos])
      have := mul_nonpos_of_nonneg_of_nonpos hw.le hc
      linarith
    · have hs := Real.sin_nonpos_of_nonpos_of_neg_pi_le
        (show w - 2 * Real.pi ≤ 0 by linarith)
        (show -Real.pi ≤ w - 2 * Real.pi by linarith)
      rw [Real.sin_sub_two_pi] at hs
      linarith

/-- 048 复谱分支的标量关系不相容：包含三角函数、指数及多圈排除。
    从矩阵 KKT 与 Hermite 余式推出这些输入关系的桥接尚未形式化。 -/
theorem no_complex_spectral_solution
    {u y w : ℝ} (hy : 1 / 2 < y) (hw : 0 < w)
    (hsine : Real.sin w / w = Real.exp (y - u / 2) / (y - 1 / 2))
    (hphase : w * Real.cos w = (u - 1) / 2 * Real.sin w)
    (hpoly : (1 - y) * ((u - 2) ^ 2 + 4 * w ^ 2) = 4 - u - y)
    (hupper : w ^ 2 < u ^ 2 / 4 + y ^ 2 / 2 + 3 * (u + y) / 4)
    (hmod : (u - 1) ^ 2 / 4 + w ^ 2 =
      (y - 1 / 2) ^ 2 * Real.exp (u - 2 * y)) : False := by
  have hT : 0 < y - 1 / 2 := by linarith
  have hsratio : 0 < Real.sin w / w := by
    rw [hsine]
    exact div_pos (Real.exp_pos _) hT
  have hsin : 0 < Real.sin w := (div_pos_iff_of_pos_right hw).mp hsratio
  have he : Real.exp (y - u / 2) < y - 1 / 2 := by
    apply (div_lt_one hT).mp
    rw [← hsine]
    exact (div_lt_one hw).mpr (Real.sin_lt hw)
  have hu : 3 < u := by
    linarith [Real.add_one_le_exp (y - u / 2)]
  have hwfreq : 2 * Real.pi < w := frequency_gt_two_pi hu hw hsin hphase
  have hlog : y - u / 2 < Real.log (y - 1 / 2) :=
    (Real.lt_log_iff_exp_lt hT).mpr he
  have hlogtwo : (1 / 2 : ℝ) < Real.log 2 := by
    apply (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 2)).mpr
    have h := Real.exp_bound_div_one_sub_of_interval'
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    norm_num at h ⊢
    exact h
  have hlogscaled := Real.log_le_sub_one_of_pos
    (show 0 < 2 * (y - 1 / 2) by positivity)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hT)] at hlogscaled
  have hy1 : 1 < y := by
    by_contra h
    have hyn : y ≤ 1 := le_of_not_gt h
    have hn := mul_nonneg (show 0 ≤ 1 - y by linarith)
      (show 0 ≤ (u - 2) ^ 2 + 4 * w ^ 2 by positivity)
    nlinarith [hpoly]
  have ht : 0 < y - 1 := by linarith
  have hrel : 4 * w ^ 2 = (u - 3) * (1 / (y - 1) - (u - 3) - 2) := by
    field_simp [ne_of_gt ht]
    nlinarith [hpoly]
  have hrel' : 4 * w ^ 2 = (u - 3) / (y - 1) - (u - 3) ^ 2 - 2 * (u - 3) := by
    convert hrel using 1
    ring
  have hmod' : (1 + 2 * (y - 1)) ^ 2 *
      Real.exp ((u - 3) + 1 - 2 * (y - 1)) =
      4 + 2 * (u - 3) + (u - 3) / (y - 1) := by
    rw [show (u - 3) + 1 - 2 * (y - 1) = u - 2 * y by ring]
    nlinarith [hmod, hrel']
  apply no_high_frequency_remainder (show 0 < u - 3 by linarith) ht hwfreq hrel
    (hmod := hmod')
  convert hupper using 1
  ring

end QuantumEmbedding.Continuity

#print axioms QuantumEmbedding.Continuity.continuousOn_of_closed_strictInterior
#print axioms QuantumEmbedding.Continuity.frontier_eq_two_graphs
#print axioms QuantumEmbedding.Continuity.rectangle_of_connected_parameters
#print axioms QuantumEmbedding.Continuity.continuity_frontier_of_parametric_coverage
#print axioms QuantumEmbedding.Continuity.no_high_frequency_remainder
#print axioms QuantumEmbedding.Continuity.no_complex_spectral_solution
#print axioms QuantumEmbedding.Continuity.continuity_frontier_of_attainment_no_extrema
#print axioms QuantumEmbedding.Continuity.continuityOn_subset_of_attainment_no_extrema
#print axioms QuantumEmbedding.Continuity.reducedMatrix_polynomial
#print axioms QuantumEmbedding.Continuity.determinant_of_second_moment
#print axioms QuantumEmbedding.Continuity.envelope_left_limit_of_reset_curve
