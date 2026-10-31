import TwoStateQuantumEmbedding.ResetPositiveComparison

noncomputable section
open Set Filter Matrix
open scoped Topology Matrix.Norms.Operator

namespace TwoStateQuantumEmbedding.ResetComparison
set_option backward.isDefEq.respectTransparency false

/-- 合作线性微分不等式的负锥不变性。 -/
theorem cooperative_nonpos (a r c ell : ℝ) (hr : 0 ≤ r) (hc : 0 ≤ c)
    (f g fd gd : ℝ → ℝ)
    (hf : ∀ s, 0 ≤ s → HasDerivAt f (fd s) s)
    (hg : ∀ s, 0 ≤ s → HasDerivAt g (gd s) s)
    (hf_le : ∀ s, 0 ≤ s → fd s ≤ -a * f s + r * g s)
    (hg_le : ∀ s, 0 ≤ s → gd s ≤ c * f s - ell * g s)
    (hf0 : f 0 ≤ 0) (hg0 : g 0 ≤ 0) {t : ℝ} (ht : 0 ≤ t) : f t ≤ 0 ∧ g t ≤ 0 := by
  let L := fenceRate a r c ell
  have hL := fenceRate_bounds a r c ell hr hc
  have hbump (ε s : ℝ) : HasDerivAt (fun x : ℝ => ε * Real.exp (L * x))
      (L * (ε * Real.exp (L * s))) s := by
    convert (((hasDerivAt_id s).const_mul L).exp).const_mul ε using 1 <;>
      simp only [id_eq, mul_one] <;> ring
  have hb (ε : ℝ) (hε : 0 < ε) :
      f t ≤ ε * Real.exp (L * t) ∧ g t ≤ ε * Real.exp (L * t) := by
    let F : Fin 2 → ℝ → ℝ := ![fun s => f s - ε * Real.exp (L * s),
      fun s => g s - ε * Real.exp (L * s)]
    let Fd : Fin 2 → ℝ → ℝ := ![fun s => fd s - L * (ε * Real.exp (L * s)),
      fun s => gd s - L * (ε * Real.exp (L * s))]
    have hFd : ∀ i s, s ∈ Icc (0 : ℝ) t → HasDerivAt (F i) (Fd i s) s := by
      intro i s hs; fin_cases i
      · exact (hf s hs.1).fun_sub (hbump ε s)
      · exact (hg s hs.1).fun_sub (hbump ε s)
    have hinit : ∀ i, F i 0 ≤ 0 := by
      intro i; fin_cases i <;> simp [F] <;> linarith
    have hboundary : ∀ s ∈ Ico (0 : ℝ) t, (∀ i, F i s ≤ 0) →
        ∀ i, F i s = 0 → Fd i s < 0 := by
      intro s hs hfs i heq
      have hδ : 0 < ε * Real.exp (L * s) := mul_pos hε (Real.exp_pos _)
      have hf' := hfs 0
      have hg' := hfs 1
      dsimp [F] at hf' hg'
      fin_cases i
      · dsimp [F, Fd] at heq ⊢
        have heq' : f s = ε * Real.exp (L * s) := by linarith
        have hb' := hf_le s hs.1
        rw [heq'] at hb'
        have hmul := mul_le_mul_of_nonneg_left (show g s ≤ ε * Real.exp (L * s) by linarith) hr
        have hstrict := mul_pos hL.1 hδ
        change 0 < (L + a - r) * (ε * Real.exp (L * s)) at hstrict
        nlinarith only [hb', hmul, hstrict]
      · dsimp [F, Fd] at heq ⊢
        have heq' : g s = ε * Real.exp (L * s) := by linarith
        have hb' := hg_le s hs.1
        rw [heq'] at hb'
        have hmul := mul_le_mul_of_nonneg_left (show f s ≤ ε * Real.exp (L * s) by linarith) hc
        have hstrict := mul_pos hL.2 hδ
        change 0 < (L + ell - c) * (ε * Real.exp (L * s)) at hstrict
        nlinarith only [hb', hmul, hstrict]
    have hh := finite_fence F Fd hFd hinit hboundary t ⟨ht, le_rfl⟩
    exact ⟨sub_nonpos.mp (hh 0), sub_nonpos.mp (hh 1)⟩
  have hcont : ContinuousWithinAt (fun ε : ℝ => ε * Real.exp (L * t)) (Ioi 0) 0 := by fun_prop
  constructor
  · have hh := continuousWithinAt_const.closure_le (by simp : (0 : ℝ) ∈ closure (Ioi 0))
      hcont (fun ε hε => (hb ε hε).1)
    simpa using hh
  · have hh := continuousWithinAt_const.closure_le (by simp : (0 : ℝ) ∈ closure (Ioi 0))
      hcont (fun ε hε => (hb ε hε).2)
    simpa using hh

/-- 任意时间相关上解都能与真实合作系统比较。 -/
theorem cooperative_supersolution (a r c ell : ℝ) (hr : 0 ≤ r) (hc : 0 ≤ c)
    (X Z U V Ud Vd : ℝ → ℝ)
    (hX : ∀ s, 0 ≤ s → HasDerivAt X (-a * X s + r * Z s) s)
    (hZ : ∀ s, 0 ≤ s → HasDerivAt Z (c * X s - ell * Z s) s)
    (hU : ∀ s, 0 ≤ s → HasDerivAt U (Ud s) s)
    (hV : ∀ s, 0 ≤ s → HasDerivAt V (Vd s) s)
    (hUb : ∀ s, 0 ≤ s → -a * U s + r * V s ≤ Ud s)
    (hVb : ∀ s, 0 ≤ s → c * U s - ell * V s ≤ Vd s)
    (hX0 : X 0 ≤ U 0) (hZ0 : Z 0 ≤ V 0) {t : ℝ} (ht : 0 ≤ t) :
    X t ≤ U t ∧ Z t ≤ V t := by
  have hh := cooperative_nonpos a r c ell hr hc (fun s => X s - U s) (fun s => Z s - V s)
    (fun s => (-a * X s + r * Z s) - Ud s)
    (fun s => (c * X s - ell * Z s) - Vd s)
    (fun s hs => (hX s hs).fun_sub (hU s hs))
    (fun s hs => (hZ s hs).fun_sub (hV s hs))
    (fun s hs => by linarith [hUb s hs])
    (fun s hs => by linarith [hVb s hs])
    (sub_nonpos.mpr hX0) (sub_nonpos.mpr hZ0) ht
  exact ⟨sub_nonpos.mp hh.1, sub_nonpos.mp hh.2⟩

theorem scalar_forcing_supersolution (a : ℝ) (X W F Wd : ℝ → ℝ)
    (hX : ∀ s, 0 ≤ s → HasDerivAt X (-a * X s + F s) s)
    (hW : ∀ s, 0 ≤ s → HasDerivAt W (Wd s) s)
    (hWb : ∀ s, 0 ≤ s → -a * W s + F s ≤ Wd s)
    (h0 : X 0 ≤ W 0) {t : ℝ} (ht : 0 ≤ t) : X t ≤ W t := by
  have hh := cooperative_nonpos a 0 0 0 le_rfl le_rfl
    (fun s => X s - W s) (fun _ => 0)
    (fun s => (-a * X s + F s) - Wd s) (fun _ => 0)
    (fun s hs => (hX s hs).fun_sub (hW s hs))
    (fun s _ => hasDerivAt_const s 0)
    (fun s hs => by linarith [hWb s hs])
    (fun _ _ => by simp) (sub_nonpos.mpr h0) le_rfl ht
  exact sub_nonpos.mp hh.1

theorem decay_hasDerivAt (a s : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (-a * t)) (-a * Real.exp (-a * s)) s := by
  simpa [mul_comm] using ((hasDerivAt_id s).const_mul (-a)).exp

/-- 双指数上解保留初始相干的快衰减，避免大速率时的虚假放大。 -/
theorem matrix_weighted_barrier_of_identities (a r c ell k v w d P Q : ℝ)
    (hr : 0 ≤ r) (hc : 0 ≤ c) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hd : 0 ≤ d) (hQ : 0 ≤ Q) (hA : 0 < a - k) (hB : 0 < ell - k)
    (hP : v + d ≤ P)
    (hd_eq : (ell - k) * d = r * w)
    (hQ_eq : (ell - k) * Q = c * P)
    (hP_eq : (a - k) * (P - v - d) = r * Q) :
    ∀ t, 0 ≤ t →
      comparisonFlow a r c ell v w t 0 ≤ P * Real.exp (-k * t) ∧
      comparisonFlow a r c ell v w t 1 ≤ w * Real.exp (-ell * t) + Q * Real.exp (-k * t) ∧
      comparisonFlow a r c ell v w t 0 - v * Real.exp (-a * t) ≤
        (P - v) * Real.exp (-k * t) := by
  let X := fun s => comparisonFlow a r c ell v w s 0
  let Z := fun s => comparisonFlow a r c ell v w s 1
  let U := fun s => P * Real.exp (-k * s) - d * Real.exp (-ell * s)
  let V := fun s => w * Real.exp (-ell * s) + Q * Real.exp (-k * s)
  let Ud := fun s => -k * P * Real.exp (-k * s) + ell * d * Real.exp (-ell * s)
  let Vd := fun s => -ell * w * Real.exp (-ell * s) - k * Q * Real.exp (-k * s)
  have hX := comparisonFlow_deriv_zero a r c ell v w
  have hZ := comparisonFlow_deriv_one a r c ell v w
  have hX0 : X 0 = v := by simp [X, comparisonFlow_zero]
  have hZ0 : Z 0 = w := by simp [Z, comparisonFlow_zero]
  have hU (s : ℝ) : HasDerivAt U (Ud s) s := by
    convert ((decay_hasDerivAt k s).const_mul P).fun_sub
      ((decay_hasDerivAt ell s).const_mul d) using 1 <;> dsimp [U, Ud] <;> ring
  have hV (s : ℝ) : HasDerivAt V (Vd s) s := by
    convert ((decay_hasDerivAt ell s).const_mul w).fun_add
      ((decay_hasDerivAt k s).const_mul Q) using 1 <;> dsimp [V, Vd] <;> ring
  have he (s : ℝ) (hs : 0 ≤ s) : Real.exp (-ell * s) ≤ Real.exp (-k * s) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hB.le hs]
  have hfirst : (a - k) * P - r * Q = (a - k) * (v + d) := by
    nlinarith only [hP_eq]
  have hfast : (ell - a) * d - r * w = -(a - k) * d := by
    nlinarith only [hd_eq]
  have hUb (s : ℝ) (hs : 0 ≤ s) : -a * U s + r * V s ≤ Ud s := by
    have heq : Ud s - (-a * U s + r * V s) =
        (a - k) * (v * Real.exp (-k * s) + d * (Real.exp (-k * s) - Real.exp (-ell * s))) := by
      calc
        _ = ((a - k) * P - r * Q) * Real.exp (-k * s) +
            ((ell - a) * d - r * w) * Real.exp (-ell * s) := by dsimp [Ud, U, V]; ring
        _ = _ := by rw [hfirst, hfast]; ring
    have hh := mul_nonneg hA.le (add_nonneg (mul_nonneg hv (Real.exp_pos (-k * s)).le)
      (mul_nonneg hd (sub_nonneg.mpr (he s hs))))
    rw [← heq] at hh
    exact sub_nonneg.mp hh
  have hVb (s : ℝ) : c * U s - ell * V s ≤ Vd s := by
    have heq : Vd s - (c * U s - ell * V s) = c * d * Real.exp (-ell * s) := by
      calc
        _ = ((ell - k) * Q - c * P) * Real.exp (-k * s) + c * d * Real.exp (-ell * s) := by
          dsimp [Vd, U, V]; ring
        _ = _ := by rw [hQ_eq]; ring
    have hh := mul_nonneg (mul_nonneg hc hd) (Real.exp_pos (-ell * s)).le
    rw [← heq] at hh
    exact sub_nonneg.mp hh
  have hcompare (s : ℝ) (hs : 0 ≤ s) : X s ≤ U s ∧ Z s ≤ V s := by
    apply cooperative_supersolution a r c ell hr hc X Z U V Ud Vd
      (fun s _ => hX s) (fun s _ => hZ s) (fun s _ => hU s) (fun s _ => hV s)
      hUb (fun s _ => hVb s)
    · rw [hX0]; dsimp [U]; simp only [mul_zero, Real.exp_zero, mul_one]; linarith
    · rw [hZ0]; dsimp [V]; simp only [mul_zero, Real.exp_zero, mul_one]; linarith
    · exact hs
  let W := fun s => v * Real.exp (-a * s) + (P - v) * Real.exp (-k * s) - d * Real.exp (-ell * s)
  let Wd := fun s => -a * v * Real.exp (-a * s) - k * (P - v) * Real.exp (-k * s) +
    ell * d * Real.exp (-ell * s)
  have hW (s : ℝ) : HasDerivAt W (Wd s) s := by
    convert (((decay_hasDerivAt a s).const_mul v).fun_add
      ((decay_hasDerivAt k s).const_mul (P - v))).fun_sub
      ((decay_hasDerivAt ell s).const_mul d) using 1 <;> dsimp [W, Wd] <;> ring
  have hfeedback : (a - k) * (P - v) - r * Q = (a - k) * d := by
    nlinarith only [hP_eq]
  have hWb (s : ℝ) (hs : 0 ≤ s) : -a * W s + r * Z s ≤ Wd s := by
    have heq : Wd s - (-a * W s + r * V s) =
        (a - k) * d * (Real.exp (-k * s) - Real.exp (-ell * s)) := by
      calc
        _ = ((a - k) * (P - v) - r * Q) * Real.exp (-k * s) +
            ((ell - a) * d - r * w) * Real.exp (-ell * s) := by dsimp [Wd, W, V]; ring
        _ = _ := by rw [hfeedback, hfast]; ring
    have hh := mul_nonneg (mul_nonneg hA.le hd) (sub_nonneg.mpr (he s hs))
    rw [← heq] at hh
    have hz := mul_le_mul_of_nonneg_left (hcompare s hs).2 hr
    linarith
  have hW0 : X 0 ≤ W 0 := by
    rw [hX0]; dsimp [W]; simp only [mul_zero, Real.exp_zero, mul_one]; linarith
  intro t ht
  have hpop := scalar_forcing_supersolution a X W (fun s => r * Z s) Wd
    (fun s _ => hX s) (fun s _ => hW s) hWb hW0 ht
  have hp := (hcompare t ht).1
  have hz := (hcompare t ht).2
  have hdrop := mul_nonneg hd (Real.exp_pos (-ell * t)).le
  refine ⟨?_, hz, ?_⟩
  · change X t ≤ _
    dsimp [U] at hp
    linarith
  · change X t - v * Real.exp (-a * t) ≤ _
    dsimp [W] at hpop
    linarith

def feedbackRatio (a r c ell k : ℝ) : ℝ := r * c / ((a - k) * (ell - k))

def populationWeight (a r c ell k v w : ℝ) : ℝ :=
  (v + r * w / (ell - k)) / (1 - feedbackRatio a r c ell k)

def coherenceWeight (a r c ell k v w : ℝ) : ℝ :=
  c * populationWeight a r c ell k v w / (ell - k)

def populationFeedbackWeight (a r c ell k v w : ℝ) : ℝ :=
  r * w / (ell - k) + feedbackRatio a r c ell k * populationWeight a r c ell k v w

/-- 任意非负初值的加权反馈界，初始相干仅带 `ell-k` 分母。 -/
theorem weighted_matrix_bounds (a r c ell k v w : ℝ)
    (hr : 0 ≤ r) (hc : 0 ≤ c) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hA : k < a) (hB : k < ell) (hη : feedbackRatio a r c ell k < 1)
    {t : ℝ} (ht : 0 ≤ t) :
    comparisonFlow a r c ell v w t 0 ≤ populationWeight a r c ell k v w * Real.exp (-k * t) ∧
    comparisonFlow a r c ell v w t 1 ≤ w * Real.exp (-ell * t) +
      coherenceWeight a r c ell k v w * Real.exp (-k * t) ∧
    comparisonFlow a r c ell v w t 0 - v * Real.exp (-a * t) ≤
      populationFeedbackWeight a r c ell k v w * Real.exp (-k * t) := by
  let η := feedbackRatio a r c ell k
  let d := r * w / (ell - k)
  let P := populationWeight a r c ell k v w
  let Q := coherenceWeight a r c ell k v w
  have hAp : 0 < a - k := sub_pos.mpr hA
  have hBp : 0 < ell - k := sub_pos.mpr hB
  have hη0 : 0 ≤ η := div_nonneg (mul_nonneg hr hc) (mul_nonneg hAp.le hBp.le)
  have hden : 0 < 1 - η := sub_pos.mpr hη
  have hd : 0 ≤ d := div_nonneg (mul_nonneg hr hw) hBp.le
  have hP0 : 0 ≤ P := div_nonneg (add_nonneg hv hd) hden.le
  have hQ0 : 0 ≤ Q := div_nonneg (mul_nonneg hc hP0) hBp.le
  have hnorm : (1 - η) * P = v + d := by
    change (1 - η) * ((v + d) / (1 - η)) = v + d
    field_simp [ne_of_gt hden]
  have hP : v + d ≤ P := by nlinarith [mul_nonneg hη0 hP0]
  have hd_eq : (ell - k) * d = r * w := by
    dsimp [d]; field_simp [ne_of_gt hBp]
  have hQ_eq : (ell - k) * Q = c * P := by
    change (ell - k) * (c * P / (ell - k)) = c * P
    field_simp [ne_of_gt hBp]
  have hrel : (a - k) * η = r * c / (ell - k) := by
    dsimp [η, feedbackRatio]
    field_simp [ne_of_gt hAp, ne_of_gt hBp]
  have hdiff : P - v - d = η * P := by nlinarith only [hnorm]
  have hP_eq : (a - k) * (P - v - d) = r * Q := by
    rw [hdiff, ← mul_assoc, hrel]
    dsimp [Q, coherenceWeight, P]
    ring
  have hh := matrix_weighted_barrier_of_identities a r c ell k v w d P Q
    hr hc hv hw hd hQ0 hAp hBp hP hd_eq hQ_eq hP_eq t ht
  refine ⟨hh.1, hh.2.1, ?_⟩
  have heq : P - v = populationFeedbackWeight a r c ell k v w := by
    change P - v = d + η * P
    linarith only [hdiff]
  rw [← heq]
  exact hh.2.2

/-- 初值 `(1,0)` 的实际矩阵指数人口反馈界。 -/
theorem weighted_population_feedback_unit (a r c ell k : ℝ)
    (hr : 0 ≤ r) (hc : 0 ≤ c) (hA : k < a) (hB : k < ell)
    (hη : feedbackRatio a r c ell k < 1) {t : ℝ} (ht : 0 ≤ t) :
    comparisonFlow a r c ell 1 0 t 0 - Real.exp (-a * t) ≤
      (feedbackRatio a r c ell k / (1 - feedbackRatio a r c ell k)) * Real.exp (-k * t) := by
  have hh := (weighted_matrix_bounds a r c ell k 1 0 hr hc (by norm_num) le_rfl hA hB hη ht).2.2
  simpa [populationFeedbackWeight, populationWeight, div_eq_mul_inv] using hh

/-- 同时用于概率包络的二次型版本。 -/
theorem weighted_quadratic_bound (a r c ell k v w : ℝ)
    (hr : 0 ≤ r) (hc : 0 ≤ c) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hA : k < a) (hB : k < ell) (hη : feedbackRatio a r c ell k < 1)
    {t : ℝ} (ht : 0 ≤ t) :
    dotProduct ![v,w] (NormedSpace.exp (t • comparisonMatrix a r c ell) *ᵥ ![v,w]) -
      2 * v ^ 2 * Real.exp (-a * t) ≤
      -v ^ 2 * Real.exp (-a * t) +
      (v * populationFeedbackWeight a r c ell k v w + w ^ 2 +
        w * coherenceWeight a r c ell k v w) * Real.exp (-k * t) := by
  obtain ⟨hX, hZ, hF⟩ := weighted_matrix_bounds a r c ell k v w hr hc hv hw hA hB hη ht
  have hp := mul_le_mul_of_nonneg_left hF hv
  have hq := mul_le_mul_of_nonneg_left hZ hw
  have he : Real.exp (-ell * t) ≤ Real.exp (-k * t) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_pos.mpr hB).le ht]
  have hww := mul_le_mul_of_nonneg_left he (sq_nonneg w)
  change dotProduct ![v,w] (comparisonFlow a r c ell v w t) - _ ≤ _
  simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  nlinarith only [hp, hq, hww]

#print axioms cooperative_nonpos
#print axioms cooperative_supersolution
#print axioms matrix_weighted_barrier_of_identities
#print axioms weighted_matrix_bounds
#print axioms weighted_population_feedback_unit
#print axioms weighted_quadratic_bound

end TwoStateQuantumEmbedding.ResetComparison
