import TwoStateQuantumEmbedding.CPTP
import TwoStateQuantumEmbedding.CanonicalBloch
import TwoStateQuantumEmbedding.ExponentialGradient
import TwoStateQuantumEmbedding.UnitaryBoundary

/-! 有界规范参数的紧像；全体近优生成元的统一定位由后续接口接入。 -/
noncomputable section
open Matrix Set
open scoped ComplexOrder MatrixOrder Matrix.Norms.Frobenius

namespace TwoStateQuantumEmbedding.CompactAttainment
open CanonicalBloch GKSLAlgebra

abbrev KMatrix := Matrix (Fin 3) (Fin 3) ℂ

def traceBall (D : ℝ) : Set KMatrix := {K | K.PosSemidef ∧ K.trace.re ≤ D}

theorem psd_trace_norm (K : KMatrix) (hK : K.PosSemidef) :
    ‖K.trace‖ = K.trace.re := by
  simpa using congrArg Complex.re (Complex.norm_of_nonneg' hK.trace_nonneg)

theorem traceBall_isCompact (D : ℝ) : IsCompact (traceBall D) := by
  let : ProperSpace KMatrix := FiniteDimensional.proper_rclike ℂ _
  apply Metric.isCompact_of_isClosed_isBounded
  · exact Matrix.posSemidef_is_closed.inter
      (isClosed_le (Complex.continuous_re.comp continuous_id.matrix_trace) continuous_const)
  · apply (posSemidef_trace_bounded_isBounded (D := 3) D).subset
    intro K hK
    exact ⟨hK.1, by rw [psd_trace_norm K hK.1]; exact hK.2⟩

def parameterBox (C D : ℝ) : Set (BlochVec × KMatrix) :=
  Metric.closedBall 0 C ×ˢ traceBall D

theorem parameterBox_isCompact (C D : ℝ) : IsCompact (parameterBox C D) :=
  (isCompact_closedBall 0 C).prod (traceBall_isCompact D)

theorem continuous_canonicalOutput :
    Continuous (fun p : BlochVec × KMatrix => canonicalOutput p.1 p.2 1) := by
  have hA := fun p : BlochVec × KMatrix =>
    (ExponentialGradient.hasStrictFDerivAt_canonical_a p).hasFDerivAt.continuousAt
  have hB := fun p : BlochVec × KMatrix =>
    (ExponentialGradient.hasStrictFDerivAt_canonical_b p).hasFDerivAt.continuousAt
  exact (continuous_iff_continuousAt.mpr hA).prodMk
    (continuous_iff_continuousAt.mpr hB)

def boundedOutputs (C D : ℝ) : Set (ℝ × ℝ) :=
  (fun p : BlochVec × KMatrix => canonicalOutput p.1 p.2 1) '' parameterBox C D

theorem boundedOutputs_isCompact (C D : ℝ) : IsCompact (boundedOutputs C D) :=
  (parameterBox_isCompact C D).image continuous_canonicalOutput

/-- 紧参数像中的闭包点确有同一有限生成元实现，不限跳跃矩阵的秩。 -/
theorem closure_boundedOutputs_finite {C D : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ closure (boundedOutputs C D)) : p ∈ finiteOutputs := by
  rw [(boundedOutputs_isCompact C D).isClosed.closure_eq] at hp
  obtain ⟨⟨h, K⟩, hparam, hout⟩ := hp
  rw [finiteOutputs_eq_canonicalOutputs]
  exact ⟨h, K, hparam.2.1, hout⟩

/-- 真正的全体附近有限输出定位足以把原Q2闭包点提升为有限达到。 -/
theorem finite_attainment_of_local_bounded_outputs {p : ℝ × ℝ} (hp : p ∈ Q2)
    (C D : ℝ) (U : Set (ℝ × ℝ)) (hU : U ∈ nhds p)
    (hbounded : U ∩ finiteOutputs ⊆ boundedOutputs C D) : p ∈ finiteOutputs := by
  apply closure_boundedOutputs_finite (C := C) (D := D)
  apply closure_mono hbounded
  change p ∈ closure finiteOutputs at hp
  rw [mem_closure_iff_nhds] at hp ⊢
  intro V hV
  obtain ⟨q, hqV, hqF⟩ := hp (V ∩ U) (Filter.inter_mem hV hU)
  exact ⟨q, hqV.1, hqV.2, hqF⟩

/-- 40/41 严格余量处理第二概率会变化的任意闭包逼近点。 -/
theorem lowerBoundary_finite_of_uniform_bounds (r C D η b : ℝ)
    (hb : b ∈ Icc (0 : ℝ) 1) (hbpos : 0 < b) (hbη : b < η)
    (hupper : lowerBoundary b ≤ r * b + 40 * b ^ 2)
    (hlocal : ∀ q ∈ finiteOutputs, 0 < q.2 → q.2 < η →
      q.1 ≤ r * q.2 + 41 * q.2 ^ 2 → q ∈ boundedOutputs C D) :
    (lowerBoundary b, b) ∈ finiteOutputs := by
  let U : Set (ℝ × ℝ) := {q | 0 < q.2} ∩
    ({q | q.2 < η} ∩ {q | q.1 < r * q.2 + 41 * q.2 ^ 2})
  have hopen : IsOpen U := by
    apply IsOpen.inter (isOpen_lt continuous_const continuous_snd)
    apply IsOpen.inter (isOpen_lt continuous_snd continuous_const)
    exact isOpen_lt continuous_fst (by fun_prop)
  have hmem : (lowerBoundary b, b) ∈ U := by
    refine ⟨hbpos, hbη, ?_⟩
    change lowerBoundary b < r * b + 41 * b ^ 2
    nlinarith [sq_pos_of_pos hbpos]
  apply finite_attainment_of_local_bounded_outputs (lowerBoundary_mem_Q2 hb)
    C D U (hopen.mem_nhds hmem)
  rintro q ⟨⟨hq0, hqη, hqa⟩, hq⟩
  exact hlocal q hq hq0 hqη hqa.le

#print axioms traceBall_isCompact
#print axioms closure_boundedOutputs_finite
#print axioms finite_attainment_of_local_bounded_outputs
#print axioms lowerBoundary_finite_of_uniform_bounds

end TwoStateQuantumEmbedding.CompactAttainment
