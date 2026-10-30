import TwoStateQuantumEmbedding.FirstOrderPSD
import TwoStateQuantumEmbedding.FirstOrderComparison
import TwoStateQuantumEmbedding.UniformRotation
import TwoStateQuantumEmbedding.ProbabilityGeometry
import TwoStateQuantumEmbedding.AzimuthGauge

noncomputable section
open Matrix Complex NormedSpace
open scoped ComplexOrder Matrix.Norms.L2Operator
namespace TwoStateQuantumEmbedding.SwapComparison
open GKSLAlgebra CanonicalBloch GKSLBounds
set_option maxHeartbeats 1000000

/-- B2：实际规范生成元、任意 Hamiltonian 圈数的统一首阶展开。 -/
theorem canonical_near_swap_comparison (hx hz : ℝ)
    (K : Matrix (Fin 3) (Fin 3) ℂ) (hxpos : 0≤hx) (hK : K.PosSemidef)
    (s : ℝ) (hsread : s=(canonicalOutput ![hx,0,hz] K 1).1+
      (canonicalOutput ![hx,0,hz] K 1).2) (hs : s≤1/64) :
    let p := unitaryProbability ![hx,0,hz] 1
    let d := dissipationSize K
    let θ := Real.sqrt (hx^2+hz^2)/2
    ∃ j : ℕ, p≤(35/3)*s ∧ |θ-Swap.frequency j/2|≤2*Real.sqrt p ∧
      |hz|≤2*θ*Real.sqrt p ∧
      |(canonicalOutput ![hx,0,hz] K 1).1-p-(Swap.matrixQa j*K).trace.re|≤
        34*d*Real.sqrt p+8*d^2 ∧
      |(canonicalOutput ![hx,0,hz] K 1).2-p-(Swap.matrixQb j*K).trace.re|≤
        34*d*Real.sqrt p+8*d^2 := by
  dsimp only
  let h : BlochVec := ![hx,0,hz]
  let p := unitaryProbability h 1
  let d := dissipationSize K
  have hp0 : 0≤p := unitaryProbability_nonneg h (t:=1) (by norm_num)
  have hd : 0≤d := dissipationSize_nonneg K hK
  have hpbound : p≤(35/3)*s := unitaryProbability_le_small_sum h K hK s hsread (by linarith)
  have hp1 : p<1 := by linarith
  obtain ⟨a,b,θ,j,hθeq,hθpos,ha,hab,hh,hb,hangle,haxis⟩ :=
    normalized_swap_reference hx hz hxpos hp1
  have hclose : ∀ t∈Set.Icc (0:ℝ) 1,
      ‖exp (t • hamiltonianCLM h)-exp (t • hamiltonianCLM ![Swap.frequency j,0,0])‖≤8*Real.sqrt p := by
    intro t ht
    change ‖exp (t • hamiltonianCLM ![hx,0,hz])-exp (t • hamiltonianCLM ![Swap.frequency j,0,0])‖≤_
    conv_lhs => rw [hh]
    exact norm_exp_hamiltonian_near_swap a b θ p t j ha hab hp0 hb hangle ht
  have hfirsta := firstOrderReturn_comparison_le h ![Swap.frequency j,0,0] K hK
    (8*Real.sqrt p) (by positivity) hclose 1 (by norm_num)
  have hfirstb := firstOrderReturn_comparison_le h ![Swap.frequency j,0,0] K hK
    (8*Real.sqrt p) (by positivity) hclose (-1) (by norm_num)
  rw [firstOrderReturn_psd_a j K hK] at hfirsta
  rw [firstOrderReturn_psd_b j K hK] at hfirstb
  have hrema := (canonicalOutput_first_order_common_le h K hK (t:=1) (by norm_num)).1
  have hremb := (canonicalOutput_first_order_common_le h K hK (t:=1) (by norm_num)).2
  simp only [one_pow, mul_one] at hrema hremb
  refine ⟨j,hpbound,?_,?_,?_,?_⟩
  · simpa only [hθeq] using hangle
  · simpa only [hθeq] using haxis
  · calc
      |(canonicalOutput h K 1).1-p-(Swap.matrixQa j*K).trace.re| ≤
          |(canonicalOutput h K 1).1-p-firstOrderReturn h K 1 1|+
          |firstOrderReturn h K 1 1-(Swap.matrixQa j*K).trace.re| := abs_sub_le _ _ _
      _ ≤ 8*d^2+4*d*(8*Real.sqrt p) := add_le_add hrema hfirsta
      _ ≤ 34*d*Real.sqrt p+8*d^2 := by nlinarith [Real.sqrt_nonneg p]
  · calc
      |(canonicalOutput h K 1).2-p-(Swap.matrixQb j*K).trace.re| ≤
          |(canonicalOutput h K 1).2-p-firstOrderReturn h K 1 (-1)|+
          |firstOrderReturn h K 1 (-1)-(Swap.matrixQb j*K).trace.re| := abs_sub_le _ _ _
      _ ≤ 8*d^2+4*d*(8*Real.sqrt p) := add_le_add hremb hfirstb
      _ ≤ 34*d*Real.sqrt p+8*d^2 := by nlinarith [Real.sqrt_nonneg p]

/-- 测量轴方位规范已真实实现；任意轴和任意耗散秩均覆盖。 -/
theorem canonical_near_swap_comparison_all_axes (h : BlochVec)
    (K : Matrix (Fin 3) (Fin 3) ℂ) (hK : K.PosSemidef)
    (s : ℝ) (hsread : s=(canonicalOutput h K 1).1+(canonicalOutput h K 1).2)
    (hs : s≤1/64) :
    ∃ (hx : ℝ) (K' : Matrix (Fin 3) (Fin 3) ℂ) (j : ℕ),
      0≤hx ∧ K'.PosSemidef ∧ K'.trace=K.trace ∧
      (∀ t : ℝ, canonicalOutput ![hx,0,h 2] K' t=canonicalOutput h K t) ∧
      (let p := unitaryProbability ![hx,0,h 2] 1
       let d := dissipationSize K'
       let θ := Real.sqrt (hx^2+(h 2)^2)/2
       p≤(35/3)*s ∧ |θ-Swap.frequency j/2|≤2*Real.sqrt p ∧
       |h 2|≤2*θ*Real.sqrt p ∧
       |(canonicalOutput h K 1).1-p-(Swap.matrixQa j*K').trace.re|≤34*d*Real.sqrt p+8*d^2 ∧
       |(canonicalOutput h K 1).2-p-(Swap.matrixQb j*K').trace.re|≤34*d*Real.sqrt p+8*d^2) := by
  obtain ⟨hx,R,K',hxpos,hR,hdet,hfix,hRh,hKdef,hK',htr,hout⟩ :=
    AzimuthGauge.exists_azimuth_normal_form h K hK
  have hs' : s=(canonicalOutput ![hx,0,h 2] K' 1).1+
      (canonicalOutput ![hx,0,h 2] K' 1).2 := by rw [hout]; exact hsread
  obtain ⟨j,hj⟩ := canonical_near_swap_comparison hx (h 2) K' hxpos hK' s hs' hs
  refine ⟨hx,K',j,hxpos,hK',htr,hout,?_⟩
  simpa only [hout] using hj

/-- 原始有限 GKSL 输入直接得到 B2，不要求调用者提供 canonical 桥。 -/
theorem finite_near_swap_comparison {n : ℕ} (H : QubitMatrix) (hH : H.IsHermitian)
    (A : Fin n → QubitMatrix) (s : ℝ)
    (hsread : s=(finiteOutput H A 1).1+(finiteOutput H A 1).2) (hs : s≤1/64) :
    ∃ (hx hz : ℝ) (K : Matrix (Fin 3) (Fin 3) ℂ) (j : ℕ),
      0≤hx ∧ K.PosSemidef ∧
      (∀ t : ℝ, canonicalOutput ![hx,0,hz] K t=finiteOutput H A t) ∧
      (let p := unitaryProbability ![hx,0,hz] 1
       let d := dissipationSize K
       let θ := Real.sqrt (hx^2+hz^2)/2
       p≤(35/3)*s ∧ |θ-Swap.frequency j/2|≤2*Real.sqrt p ∧
       |hz|≤2*θ*Real.sqrt p ∧
       |(finiteOutput H A 1).1-p-(Swap.matrixQa j*K).trace.re|≤34*d*Real.sqrt p+8*d^2 ∧
       |(finiteOutput H A 1).2-p-(Swap.matrixQb j*K).trace.re|≤34*d*Real.sqrt p+8*d^2) := by
  let h := hamiltonianVector (canonicalHamiltonian H A)
  let K := GKSLAlgebra.kossakowski (fun μ => pauliCoeffs (A μ))
  have he (t : ℝ) : finiteOutput H A t=canonicalOutput h K t :=
    finiteOutput_eq_canonicalOutput H hH A t
  have hs' : s=(canonicalOutput h K 1).1+(canonicalOutput h K 1).2 := by rw [← he]; exact hsread
  obtain ⟨hx,K',j,hxpos,hK',htr,hout,hj⟩ :=
    canonical_near_swap_comparison_all_axes h K (kossakowski_posSemidef _) s hs' hs
  refine ⟨hx,h 2,K',j,hxpos,hK',?_,?_⟩
  · intro t
    exact (hout t).trans (he t).symm
  · simpa only [← he] using hj

#print axioms canonical_near_swap_comparison
#print axioms canonical_near_swap_comparison_all_axes
#print axioms finite_near_swap_comparison
end TwoStateQuantumEmbedding.SwapComparison
