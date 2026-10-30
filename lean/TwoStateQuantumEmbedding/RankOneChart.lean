import TwoStateQuantumEmbedding.ActualSwapSystem
import Mathlib.LinearAlgebra.Matrix.Rank

/-! 真实 PSD 秩一矩阵的完整复方向坐标图。 -/
noncomputable section
open Matrix Complex Filter
open scoped Topology ComplexOrder

namespace TwoStateQuantumEmbedding.RankOneChart
open GKSLAlgebra

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

abbrev CoefficientMatrix := Matrix (Fin 3) (Fin 3) ℂ
abbrev Directions := Fin 4 → ℝ

def scale (K : CoefficientMatrix) : ℝ := (K 2 2).re
def xRatio (K : CoefficientMatrix) : ℂ := -(K 0 2) / K 2 2
def yRatio (K : CoefficientMatrix) : ℂ := -(K 1 2) / K 2 2
def chart (K : CoefficientMatrix) : Directions :=
  ![(xRatio K).re, (xRatio K).im, (yRatio K).re, (yRatio K).im]
def direction (u : Directions) : PauliVec := Swap.rankOneDirection (u 0) (u 1) (u 2) (u 3)

/-- 秩一的实际线性代数含义给出全部 2×2 子式恒等式。 -/
theorem rank_one_minor (K : CoefficientMatrix) (hr : K.rank = 1) (i j : Fin 3) :
    K i j * K 2 2 = K i 2 * K 2 j := by
  let B : Matrix (Fin 2) (Fin 2) ℂ := K.submatrix ![i,2] ![j,2]
  have hb : B.rank ≤ 1 := by
    simpa [B, hr] using Matrix.rank_submatrix_le K ![i,2] ![j,2]
  have hd : B.det = 0 := by
    by_contra h
    have hh := Matrix.rank_of_det_ne_zero h
    norm_num at hh
    omega
  have hm : K i j * K 2 2 - K i 2 * K 2 j = 0 := by
    rw [Matrix.det_fin_two] at hd
    exact hd
  exact sub_eq_zero.mp hm

theorem hermitian_diagonal_real (K : CoefficientMatrix) (hK : K.IsHermitian) (i : Fin 3) :
    ((K i i).re : ℂ) = K i i := by
  have hh := congrArg Complex.im (hK.apply i i)
  simp only [Complex.star_def, Complex.conj_im] at hh
  have hi : (K i i).im = 0 := by linarith
  apply Complex.ext <;> simp [hi]

theorem diagonal_ne_zero (K : CoefficientMatrix) (hk : 0 < scale K) : K 2 2 ≠ 0 := by
  intro hz
  have : scale K = 0 := by simp [scale, hz]
  linarith

theorem direction_chart (K : CoefficientMatrix) (hk : K 2 2 ≠ 0) :
    direction (chart K) = fun i => -(K i 2) / K 2 2 := by
  funext i
  fin_cases i
  · exact Complex.re_add_im (xRatio K)
  · exact Complex.re_add_im (yRatio K)
  · simp [direction, chart, Swap.rankOneDirection, hk]

/-- 不额外选择跳跃相位，直接从 K 恢复负实 Z 系数规范。 -/
theorem factorization (K : CoefficientMatrix) (hK : K.PosSemidef)
    (hr : K.rank = 1) (hk : 0 < scale K) :
    K = scale K • singleK (direction (chart K)) := by
  have hn := diagonal_ne_zero K hk
  have hd : (scale K : ℂ) = K 2 2 := hermitian_diagonal_real K hK.isHermitian 2
  have hs : star (K 2 2) = K 2 2 := hK.isHermitian.apply 2 2
  ext i j
  change K i j = (scale K : ℂ) *
    (direction (chart K) i * star (direction (chart K) j))
  rw [direction_chart K hn, hd]
  simp only [star_div₀, star_neg, hs, hK.isHermitian.apply 2 j]
  field_simp
  linear_combination rank_one_minor K hr i j

theorem scale_of_representation (k : ℝ) (u : Directions) :
    scale (k • singleK (direction u)) = k := by
  simp [scale, singleK, direction, Swap.rankOneDirection, Matrix.smul_apply]

theorem xRatio_of_representation (k : ℝ) (hk : k ≠ 0) (u : Directions) :
    xRatio (k • singleK (direction u)) = (u 0 : ℂ) + (u 1 : ℂ)*I := by
  have hc : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  simp [xRatio, singleK, direction, Swap.rankOneDirection, Matrix.smul_apply]
  field_simp

theorem yRatio_of_representation (k : ℝ) (hk : k ≠ 0) (u : Directions) :
    yRatio (k • singleK (direction u)) = (u 2 : ℂ) + (u 3 : ℂ)*I := by
  have hc : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  simp [yRatio, singleK, direction, Swap.rankOneDirection, Matrix.smul_apply]
  field_simp

theorem chart_of_representation (k : ℝ) (hk : k ≠ 0) (u : Directions) :
    chart (k • singleK (direction u)) = u := by
  funext i
  fin_cases i <;>
    simp [chart, xRatio_of_representation k hk, yRatio_of_representation k hk,
      Complex.mul_re, Complex.mul_im]

/-- 坐标图中的尺度与四个实方向全部唯一。 -/
theorem representation_unique {k l : ℝ} (hk : 0 < k) (hl : 0 < l) (u v : Directions)
    (he : k • singleK (direction u) = l • singleK (direction v)) : k = l ∧ u = v := by
  constructor
  · simpa only [scale_of_representation] using congrArg scale he
  · simpa only [chart_of_representation k hk.ne', chart_of_representation l hl.ne'] using
      congrArg chart he

theorem existsUnique_representation (K : CoefficientMatrix) (hK : K.PosSemidef)
    (hr : K.rank = 1) (hk : 0 < scale K) :
    ∃! p : ℝ × Directions, 0 < p.1 ∧ K = p.1 • singleK (direction p.2) := by
  refine ⟨(scale K, chart K), ⟨hk, factorization K hK hr hk⟩, ?_⟩
  rintro ⟨k,u⟩ ⟨hp, he⟩
  obtain ⟨hs, hu⟩ := representation_unique hp hk u (chart K)
    (he.symm.trans (factorization K hK hr hk))
  exact Prod.ext hs hu

theorem scale_smul (d : ℝ) (K : CoefficientMatrix) : scale (d • K) = d * scale K := by
  simp [scale, Matrix.smul_apply]

/-- 非零实缩放不改变坐标图；包括正归一化所需的全部情况。 -/
theorem chart_smul (d : ℝ) (hd : d ≠ 0) (K : CoefficientMatrix) : chart (d • K) = chart K := by
  have hc : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd
  have hh (i : Fin 3) : -((d • K) i 2) / (d • K) 2 2 = -(K i 2) / K 2 2 := by
    change -((d : ℂ)*K i 2)/((d : ℂ)*K 2 2) = _
    by_cases hn : K 2 2 = 0
    · simp [hn]
    · field_simp
  simp only [chart, xRatio, yRatio, hh]

theorem scale_continuous : Continuous scale := by
  unfold scale
  fun_prop

theorem chart_continuousAt (K : CoefficientMatrix) (hk : K 2 2 ≠ 0) : ContinuousAt chart K := by
  apply continuousAt_pi.mpr
  intro i
  fin_cases i <;> simp only [chart, xRatio, yRatio]
  all_goals fun_prop (disch := assumption)

def referenceProjector : CoefficientMatrix :=
  (Swap.mass Swap.kernelVector)⁻¹ • singleK Swap.kernelVector

def referenceDirections : Directions := ![0, Swap.rootTwo/2, 0, 0]

theorem kernelVector_mass : Swap.mass Swap.kernelVector = 3/2 := by
  simp [Swap.mass, Swap.kernelVector, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  nlinarith [Swap.rootTwo_sq]

/-- 与 090 的 kernelProjector_eq_outer 使用完全相同的右侧。 -/
theorem referenceProjector_eq_outer : referenceProjector =
    ((2/3 : ℝ) : ℂ) • Matrix.vecMulVec Swap.kernelVector (star Swap.kernelVector) := by
  unfold referenceProjector
  rw [kernelVector_mass]
  ext i j
  simp [singleK, Matrix.vecMulVec, Matrix.smul_apply, smul_eq_mul]

theorem referenceProjector_eq_representation :
    referenceProjector = (2/3:ℝ) • singleK (direction referenceDirections) := by
  unfold referenceProjector
  rw [kernelVector_mass]
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [singleK, direction, referenceDirections, Swap.rankOneDirection,
      Swap.kernelVector, Matrix.smul_apply, Complex.mul_re, Complex.mul_im]

theorem referenceProjector_zz : referenceProjector 2 2 = (2/3:ℂ) := by
  rw [referenceProjector_eq_representation]
  simp [singleK, direction, Swap.rankOneDirection, Matrix.smul_apply]

theorem scale_referenceProjector : scale referenceProjector = 2/3 := by
  rw [referenceProjector_eq_representation, scale_of_representation]

theorem chart_referenceProjector : chart referenceProjector = referenceDirections := by
  rw [referenceProjector_eq_representation, chart_of_representation _ (by norm_num)]

theorem chart_continuousAt_reference : ContinuousAt chart referenceProjector := by
  apply chart_continuousAt
  rw [referenceProjector_zz]
  norm_num

section Limits
variable {ι : Type*} {F : Filter ι} (K : ι → CoefficientMatrix) (d : ι → ℝ)

/-- 归一化矩阵趋于参考投影时，未经缩放的实际四方向趋于唯一参考方向。 -/
theorem chart_tendsto_of_normalized
    (hd : ∀ᶠ x in F, 0 < d x)
    (hK : Tendsto (fun x => (d x)⁻¹ • K x) F (𝓝 referenceProjector)) :
    Tendsto (fun x => chart (K x)) F (𝓝 referenceDirections) := by
  have ht := chart_continuousAt_reference.tendsto.comp hK
  rw [chart_referenceProjector] at ht
  apply ht.congr'
  filter_upwards [hd] with x hx
  exact chart_smul ((d x)⁻¹) (inv_ne_zero hx.ne') (K x)

/-- 与方向极限同时成立的真实尺度比值 k/d→2/3。 -/
theorem scale_ratio_tendsto_of_normalized
    (hK : Tendsto (fun x => (d x)⁻¹ • K x) F (𝓝 referenceProjector)) :
    Tendsto (fun x => scale (K x) / d x) F (𝓝 (2/3:ℝ)) := by
  have ht := scale_continuous.continuousAt.tendsto.comp hK
  simpa only [Function.comp_def, scale_referenceProjector, scale_smul, div_eq_mul_inv, mul_comm] using ht

/-- 极限还实际保证最终进入正 zz 坐标图；不额外假设每点已有 chart 范围。 -/
theorem eventually_scale_pos_of_normalized
    (hd : ∀ᶠ x in F, 0 < d x)
    (hK : Tendsto (fun x => (d x)⁻¹ • K x) F (𝓝 referenceProjector)) :
    ∀ᶠ x in F, 0 < scale (K x) := by
  have ht := scale_ratio_tendsto_of_normalized K d hK
  have hp := ht.eventually (lt_mem_nhds (by norm_num : (0:ℝ) < 2/3))
  filter_upwards [hd, hp] with x hx hpx
  exact (div_pos_iff.mp hpx).elim (fun h => h.1) (fun h => False.elim (not_lt_of_ge hx.le h.2))

theorem eventually_factorization_of_normalized
    (hd : ∀ᶠ x in F, 0 < d x)
    (hK : Tendsto (fun x => (d x)⁻¹ • K x) F (𝓝 referenceProjector))
    (hPSD : ∀ᶠ x in F, (K x).PosSemidef) (hr : ∀ᶠ x in F, (K x).rank = 1) :
    ∀ᶠ x in F, 0 < scale (K x) ∧
      K x = scale (K x) • singleK (direction (chart (K x))) := by
  filter_upwards [eventually_scale_pos_of_normalized K d hd hK, hPSD, hr] with x hx hpx hrx
  exact ⟨hx, factorization (K x) hpx hrx hx⟩
end Limits

/-- 直接使用 080 的七变量顺序，四方向没有任何平面限制。 -/
def parameters (ω h μ : ℝ) (u : Directions) : ActualSwapSystem.Parameters :=
  ![ω,h,μ,u 0,u 1,u 2,u 3]

theorem actualKossakowski_chart (K : CoefficientMatrix) (hK : K.PosSemidef)
    (hr : K.rank = 1) (hk : 0 < scale K) (ω h μ : ℝ) :
    ActualSwapSystem.kossakowskiMatrix (scale K, parameters ω h μ (chart K)) = K := by
  change scale K • singleK (direction (chart K)) = K
  exact (factorization K hK hr hk).symm

/-- 本坐标图与实际七变量生成元逐定义一致。 -/
theorem actualGenerator_chart (K : CoefficientMatrix) (hK : K.PosSemidef)
    (hr : K.rank = 1) (hk : 0 < scale K) (ω h μ : ℝ) :
    ActualSwapSystem.generator (scale K, parameters ω h μ (chart K)) =
      CanonicalBloch.augmentedGenerator ![ω,0,2*h] K := by
  rw [ActualSwapSystem.generator_eq_canonical, actualKossakowski_chart K hK hr hk]
  rfl

/-- 完整概率对与实际七变量模型一致，依赖已核验的真实指数读出。 -/
theorem actualProbabilities_chart (K : CoefficientMatrix) (hK : K.PosSemidef)
    (hr : K.rank = 1) (hk : 0 < scale K) (ω h μ : ℝ) :
    (ActualSwapSystem.probabilityA (scale K, parameters ω h μ (chart K)),
      ActualSwapSystem.probabilityB (scale K, parameters ω h μ (chart K))) =
      CanonicalBloch.canonicalOutput ![ω,0,2*h] K 1 := by
  rw [ActualSwapSystem.probability_eq_canonical, actualKossakowski_chart K hK hr hk]
  rfl

#print axioms rank_one_minor
#print axioms factorization
#print axioms representation_unique
#print axioms existsUnique_representation
#print axioms chart_smul
#print axioms referenceProjector_eq_outer
#print axioms chart_referenceProjector
#print axioms chart_continuousAt_reference
#print axioms chart_tendsto_of_normalized
#print axioms scale_ratio_tendsto_of_normalized
#print axioms eventually_factorization_of_normalized
#print axioms actualGenerator_chart
#print axioms actualProbabilities_chart

end TwoStateQuantumEmbedding.RankOneChart
