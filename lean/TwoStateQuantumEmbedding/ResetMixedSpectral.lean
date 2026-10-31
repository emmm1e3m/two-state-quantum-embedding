import TwoStateQuantumEmbedding.PureDynamics
import TwoStateQuantumEmbedding.CPTP
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum

noncomputable section
open Matrix Complex
open scoped BigOperators Matrix.Norms.Operator ComplexOrder

namespace TwoStateQuantumEmbedding.ResetMixedSpectral
open PureStationary
set_option maxHeartbeats 1600000
set_option maxRecDepth 3000

def diagonalState (ν : ℝ) : QubitMatrix := !![(ν : ℂ), 0; 0, (1-ν : ℂ)]
def swapBasis : QubitMatrix := !![0, 1; 1, 0]

theorem conjugate_mul (U V X : QubitMatrix) :
    conjugate (U*V) X = conjugate U (conjugate V X) := by
  simp only [conjugate, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem swap_unitary : swapBasisᴴ * swapBasis = 1 ∧ swapBasis * swapBasisᴴ = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [swapBasis, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]

theorem swap_diagonal (ν : ℝ) :
    conjugate swapBasis (diagonalState ν) = diagonalState (1-ν) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conjugate, swapBasis, diagonalState, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply] <;> ring

theorem mul_unitary (U V : QubitMatrix)
    (hU : Uᴴ*U=1 ∧ U*Uᴴ=1) (hV : Vᴴ*V=1 ∧ V*Vᴴ=1) :
    (U*V)ᴴ*(U*V)=1 ∧ (U*V)*(U*V)ᴴ=1 := by
  constructor
  · simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc Uᴴ U, hU.1, Matrix.one_mul, hV.1]
  · calc
      (U*V)*(U*V)ᴴ=U*(V*Vᴴ)*Uᴴ := by
        simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
      _=1 := by rw [hV.2,Matrix.mul_one,hU.2]

/-- 任意二阶密度矩阵具有按小、大本征值排列的正交谱基。 -/
theorem density_spectral_basis (ρ : QubitMatrix) (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) :
    ∃ (ν : ℝ) (U : QubitMatrix), 0 ≤ ν ∧ ν ≤ 1/2 ∧
      Uᴴ*U=1 ∧ U*Uᴴ=1 ∧ ρ = conjugate U (diagonalState ν) := by
  let U : QubitMatrix := hρ.isHermitian.eigenvectorUnitary
  let a : ℝ := hρ.isHermitian.eigenvalues 0
  let b : ℝ := hρ.isHermitian.eigenvalues 1
  have ha : 0 ≤ a := hρ.eigenvalues_nonneg 0
  have hb : 0 ≤ b := hρ.eigenvalues_nonneg 1
  have hab : a+b=1 := by
    have ht := hρ.isHermitian.trace_eq_sum_eigenvalues
    rw [htr] at ht
    have hre := congrArg Complex.re ht
    simpa [a,b,Fin.sum_univ_two] using hre.symm
  have hU : Uᴴ*U=1 ∧ U*Uᴴ=1 := by
    constructor
    · exact Unitary.coe_star_mul_self hρ.isHermitian.eigenvectorUnitary
    · exact Unitary.coe_mul_star_self hρ.isHermitian.eigenvectorUnitary
  have hspec : ρ = conjugate U (diagonalState a) := by
    have hs := hρ.isHermitian.spectral_theorem
    have hdiag : Matrix.diagonal (RCLike.ofReal ∘ hρ.isHermitian.eigenvalues) =
        diagonalState a := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [diagonalState,a]
      change (b : ℂ) = 1 - (a : ℂ)
      exact_mod_cast (show b=1-a by linarith)
    simpa only [Unitary.conjStarAlgAut_apply, hdiag, conjugate, U,
      Matrix.star_eq_conjTranspose] using hs
  by_cases ha' : a ≤ 1/2
  · exact ⟨a,U,ha,ha',hU.1,hU.2,hspec⟩
  · have hUV := mul_unitary U swapBasis hU swap_unitary
    refine ⟨b,U*swapBasis,hb,by linarith,hUV.1,hUV.2,?_⟩
    rw [conjugate_mul,swap_diagonal]
    have : 1-b=a := by linarith
    simpa only [this] using hspec

def positivePhase (z : ℂ) : ℂ := if z=0 then 1 else star z / (‖z‖ : ℂ)

theorem positivePhase_norm (z : ℂ) : ‖positivePhase z‖ = 1 := by
  by_cases hz : z=0
  · simp [positivePhase,hz]
  · simp [positivePhase,hz,norm_div,abs_of_nonneg (norm_nonneg z),norm_ne_zero_iff.mpr hz]

theorem mul_positivePhase (z : ℂ) : z * positivePhase z = (‖z‖ : ℂ) := by
  by_cases hz : z=0
  · simp [positivePhase,hz]
  · have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
    have hnorm : z.re^2+z.im^2=‖z‖^2 := by
      simpa only [normSq_apply,pow_two] using Complex.normSq_eq_norm_sq z
    rw [positivePhase,if_neg hz,← mul_div_assoc]
    apply (div_eq_iff hn).mpr
    apply Complex.ext <;>
      simp [Complex.mul_re,Complex.mul_im] <;> nlinarith [hnorm]

def rowPhase (U : QubitMatrix) : QubitMatrix :=
  Matrix.diagonal (fun i => positivePhase (U 0 i))

theorem rowPhase_unitary (U : QubitMatrix) :
    (rowPhase U)ᴴ*rowPhase U=1 ∧ rowPhase U*(rowPhase U)ᴴ=1 := by
  have hp (i : Fin 2) : normSq (positivePhase (U 0 i)) = 1 := by
    rw [Complex.normSq_eq_norm_sq,positivePhase_norm,one_pow]
  have hp0 := hp 0
  have hp1 := hp 1
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [rowPhase,Matrix.mul_apply,Fin.sum_univ_two,Matrix.conjTranspose_apply,
      Complex.mul_re,Complex.mul_im,normSq_apply] at hp0 hp1 ⊢ <;>
    nlinarith [hp0,hp1]

theorem rowPhase_preserves_diagonal (U : QubitMatrix) (ν : ℝ) :
    conjugate (rowPhase U) (diagonalState ν) = diagonalState ν := by
  have hp (i : Fin 2) : normSq (positivePhase (U 0 i)) = 1 := by
    rw [Complex.normSq_eq_norm_sq,positivePhase_norm,one_pow]
  have hp0 := hp 0
  have hp1 := hp 1
  ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [conjugate,rowPhase,diagonalState,Matrix.mul_apply,Fin.sum_univ_two,
      Matrix.conjTranspose_apply,Complex.mul_re,Complex.mul_im,normSq_apply] at hp0 hp1 ⊢ <;>
    nlinarith [congrArg (fun a : ℝ => ν*a) hp0,
      congrArg (fun a : ℝ => (1-ν)*a) hp1]

theorem rowPhase_row (U : QubitMatrix) (i : Fin 2) :
    (U*rowPhase U) 0 i = (‖U 0 i‖ : ℂ) := by
  simp only [rowPhase,Matrix.mul_diagonal]
  exact mul_positivePhase _

/-- 谱向量的独立相位使同一制备和测量的两条振幅均为非负实数。 -/
theorem density_spectral_positive_row (ρ : QubitMatrix) (hρ : ρ.PosSemidef)
    (htr : ρ.trace=1) :
    ∃ (ν : ℝ) (U : QubitMatrix) (r s : ℝ),
      0≤ν ∧ ν≤1/2 ∧ Uᴴ*U=1 ∧ U*Uᴴ=1 ∧
      ρ=conjugate U (diagonalState ν) ∧
      0≤r ∧ 0≤s ∧ U 0 0=(r:ℂ) ∧ U 0 1=(s:ℂ) := by
  obtain ⟨ν,U,hν0,hν1,hU,hUU,hρU⟩ := density_spectral_basis ρ hρ htr
  have hV := mul_unitary U (rowPhase U) ⟨hU,hUU⟩ (rowPhase_unitary U)
  refine ⟨ν,U*rowPhase U,‖U 0 0‖,‖U 0 1‖,hν0,hν1,hV.1,hV.2,?_,
    norm_nonneg _,norm_nonneg _,rowPhase_row U 0,rowPhase_row U 1⟩
  rw [conjugate_mul,rowPhase_preserves_diagonal]
  exact hρU

def measurement (p : ℝ) : QubitMatrix :=
  !![((1-p : ℝ):ℂ), (Real.sqrt (p*(1-p)):ℂ);
    (Real.sqrt (p*(1-p)):ℂ), (p:ℂ)]

theorem positive_row_geometry (U : QubitMatrix) (r s : ℝ)
    (hUU : U*Uᴴ=1) (hr : 0≤r) (hs : 0≤s)
    (hu0 : U 0 0=(r:ℂ)) (hu1 : U 0 1=(s:ℂ)) :
    r^2+s^2=1 ∧ Real.sqrt ((s^2)*(1-s^2))=r*s := by
  have he := congrArg (fun X : QubitMatrix => (X 0 0).re) hUU
  have hrow : r^2+s^2=1 := by
    simpa [Matrix.mul_apply,Fin.sum_univ_two,Matrix.conjTranspose_apply,
      hu0,hu1,Complex.mul_re,pow_two] using he
  refine ⟨hrow,?_⟩
  have hn : 0≤s^2*(1-s^2) := mul_nonneg (sq_nonneg s) (by nlinarith)
  have hsq := Real.sq_sqrt hn
  nlinarith [Real.sqrt_nonneg (s^2*(1-s^2)),mul_nonneg hr hs]

theorem positive_row_measurement (U : QubitMatrix) (r s : ℝ)
    (hUU : U*Uᴴ=1) (hr : 0≤r) (hs : 0≤s)
    (hu0 : U 0 0=(r:ℂ)) (hu1 : U 0 1=(s:ℂ)) :
    conjugate Uᴴ (Matrix.single 0 0 1) = measurement (s^2) := by
  obtain ⟨hrow,hsqrt⟩ := positive_row_geometry U r s hUU hr hs hu0 hu1
  have hsqrt' : Real.sqrt (s*s*(1-s*s))=r*s := by simpa only [pow_two] using hsqrt
  ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [conjugate,measurement,Matrix.mul_apply,Fin.sum_univ_two,
      Matrix.conjTranspose_apply,Matrix.single_apply,hu0,hu1,hsqrt,
      pow_two,hsqrt',Complex.mul_re,Complex.mul_im] <;> nlinarith

/-- 谱排序和相位规范同时保留原始制备及测量的一个共同酉基。 -/
theorem density_measurement_frame (ρ : QubitMatrix) (hρ : ρ.PosSemidef)
    (htr : ρ.trace=1) :
    ∃ (ν p : ℝ) (U : QubitMatrix),
      0≤ν ∧ ν≤1/2 ∧ 0≤p ∧ p≤1 ∧ Uᴴ*U=1 ∧ U*Uᴴ=1 ∧
      ρ=conjugate U (diagonalState ν) ∧ p=normSq (U 0 1) ∧
      conjugate Uᴴ (Matrix.single 0 0 1)=measurement p ∧
      (ρ 0 0).re=ν+(1-2*ν)*p := by
  obtain ⟨ν,U,r,s,hν0,hν1,hU,hUU,hρU,hr,hs,hu0,hu1⟩ :=
    density_spectral_positive_row ρ hρ htr
  obtain ⟨hrow,hsqrt⟩ := positive_row_geometry U r s hUU hr hs hu0 hu1
  refine ⟨ν,s^2,U,hν0,hν1,sq_nonneg s,by nlinarith,hU,hUU,hρU,?_,
    positive_row_measurement U r s hUU hr hs hu0 hu1,?_⟩
  · simp [hu1,normSq_apply,pow_two]
  · rw [hρU]
    simp [conjugate,diagonalState,Matrix.mul_apply,Fin.sum_univ_two,
      Matrix.conjTranspose_apply,hu0,hu1,Complex.mul_re]
    nlinarith

theorem stationary_in_spectral_frame {n : ℕ} (H ρ U : QubitMatrix)
    (J : Fin n → QubitMatrix) (ν : ℝ)
    (hU : Uᴴ*U=1) (hUU : U*Uᴴ=1)
    (hρU : ρ=conjugate U (diagonalState ν)) (hstat : gkslAction H J ρ=0) :
    gkslAction (conjugate Uᴴ H) (fun μ => conjugate Uᴴ (J μ)) (diagonalState ν)=0 := by
  have hc := gksl_conjugate Uᴴ H ρ J (by simpa using hUU)
  rw [hρU,conjugate_inverse U _ hU] at hc
  rw [← hρU,hstat] at hc
  simpa [conjugate] using hc

def conjugateComplexCLM (U : QubitMatrix) : QubitMatrix →L[ℂ] QubitMatrix :=
  (show QubitMatrix →ₗ[ℂ] QubitMatrix from
    { toFun := conjugate U
      map_add' := by intros X Y; simp [conjugate,mul_add,add_mul]
      map_smul' := by intros c X; simp [conjugate] }).toContinuousLinearMap

local instance : NormedRing (QubitMatrix →L[ℂ] QubitMatrix) :=
  ContinuousLinearMap.toNormedRing
local instance : NormedAlgebra ℂ (QubitMatrix →L[ℂ] QubitMatrix) :=
  ContinuousLinearMap.toNormedAlgebra
local instance : NormedAlgebra ℚ (QubitMatrix →L[ℂ] QubitMatrix) :=
  NormedAlgebra.restrictScalars ℚ ℂ _
local instance : CompleteSpace (QubitMatrix →L[ℂ] QubitMatrix) :=
  FiniteDimensional.complete ℂ _

/-- 对所有矩阵输入成立的生成元交织，自动传递到实际超算子指数。 -/
theorem actualState_intertwining {n m : ℕ} (H K U : QubitMatrix)
    (J : Fin n → QubitMatrix) (L : Fin m → QubitMatrix)
    (hL : ∀ X, gkslAction H J (conjugate U X)=conjugate U (gkslAction K L X))
    (X : QubitMatrix) (t : ℝ) :
    actualState H J (conjugate U X) t = conjugate U (actualState K L X t) := by
  have hsemi : SemiconjBy (conjugateComplexCLM U)
      ((t:ℂ) • gkslContinuousLinearMap K L)
      ((t:ℂ) • gkslContinuousLinearMap H J) := by
    apply ContinuousLinearMap.ext
    intro Y
    change conjugateComplexCLM U ((t:ℂ) • gkslAction K L Y) =
      (t:ℂ) • gkslAction H J (conjugate U Y)
    rw [map_smul]
    exact congrArg (fun Z => (t:ℂ) • Z) (hL Y).symm
  have he : conjugateComplexCLM U * NormedSpace.exp ((t:ℂ) • gkslContinuousLinearMap K L) =
      NormedSpace.exp ((t:ℂ) • gkslContinuousLinearMap H J) * conjugateComplexCLM U :=
    hsemi.exp_right
  exact (congrArg (fun F : QubitMatrix →L[ℂ] QubitMatrix => F X) he).symm

theorem actualState_conjugate {n : ℕ} (H U X : QubitMatrix)
    (J : Fin n → QubitMatrix) (hU : Uᴴ*U=1) (hUU : U*Uᴴ=1) (t : ℝ) :
    actualState H J (conjugate U X) t =
      conjugate U (actualState (conjugate Uᴴ H) (fun μ => conjugate Uᴴ (J μ)) X t) := by
  apply actualState_intertwining
  intro Y
  have hc := gksl_conjugate U (conjugate Uᴴ H) Y (fun μ => conjugate Uᴴ (J μ)) hU
  have hb (Z : QubitMatrix) : conjugate U (conjugate Uᴴ Z)=Z := by
    simpa using conjugate_inverse Uᴴ Z (by simpa using hUU)
  simpa only [hb] using hc

theorem conjugate_measurement_trace (U X : QubitMatrix) :
    (conjugate U X) 0 0 = ((conjugate Uᴴ (Matrix.single 0 0 1))*X).trace := by
  calc
    (conjugate U X) 0 0 = ((Matrix.single 0 0 1)*conjugate U X).trace := by
      simp [Matrix.trace_single_mul]
    _ = ((conjugate Uᴴ (Matrix.single 0 0 1))*X).trace := by
      simp only [conjugate,Matrix.conjTranspose_conjTranspose]
      rw [← Matrix.mul_assoc,Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]

def differenceState (u : ℝ) (z : ℂ) : QubitMatrix := !![(u:ℂ),z;star z,(-u:ℂ)]

theorem measurement_difference (p : ℝ) :
    measurement p - (1-measurement p) =
      differenceState (1-2*p) (2*Real.sqrt (p*(1-p))) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [measurement,differenceState] <;> ring

theorem measurement_readout (p u : ℝ) (z : ℂ) :
    ((measurement p * differenceState u z).trace).re =
      (1-2*p)*u + 2*Real.sqrt (p*(1-p))*z.re := by
  simp [measurement,differenceState,Matrix.trace,Matrix.mul_apply,Fin.sum_univ_two,
    Complex.mul_re]
  ring

theorem second_preparation_in_frame (U : QubitMatrix) (p : ℝ)
    (hU : Uᴴ*U=1) (hM : conjugate Uᴴ (Matrix.single 0 0 1)=measurement p) :
    conjugate Uᴴ (Matrix.single 1 1 1)=1-measurement p := by
  have hp : (Matrix.single 1 1 1 : QubitMatrix)=1-Matrix.single 0 0 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply]
  rw [hp]
  simp only [conjugate,Matrix.conjTranspose_conjTranspose,Matrix.mul_sub,Matrix.sub_mul,
    Matrix.mul_one,hU] at *
  rw [hM]

theorem preparation_difference_in_frame (U : QubitMatrix) (p : ℝ)
    (hU : Uᴴ*U=1) (hM : conjugate Uᴴ (Matrix.single 0 0 1)=measurement p) :
    conjugate Uᴴ (Matrix.single 0 0 1-Matrix.single 1 1 1)=
      differenceState (1-2*p) (2*Real.sqrt (p*(1-p))) := by
  have hs := second_preparation_in_frame U p hU hM
  have hadd : conjugate Uᴴ (Matrix.single 0 0 1-Matrix.single 1 1 1)=
      conjugate Uᴴ (Matrix.single 0 0 1)-conjugate Uᴴ (Matrix.single 1 1 1) := by
    simp only [conjugate,Matrix.mul_sub,Matrix.sub_mul]
  rw [hadd,hM,hs,measurement_difference]

theorem differenceState_hermitian (u : ℝ) (z : ℂ) :
    (differenceState u z).IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [differenceState,Matrix.conjTranspose_apply]

theorem differenceState_trace (u : ℝ) (z : ℂ) : (differenceState u z).trace=0 := by
  simp [differenceState,Matrix.trace,Fin.sum_univ_two]

theorem traceless_hermitian_coordinates (X : QubitMatrix)
    (hX : X.IsHermitian) (htr : X.trace=0) :
    X=differenceState (X 0 0).re (X 0 1) := by
  have h00 := congrArg Complex.im (hX.apply 0 0)
  have h11 := congrArg Complex.im (hX.apply 1 1)
  simp only [Complex.star_def,Complex.conj_im] at h00 h11
  have hi00 : (X 0 0).im=0 := by linarith
  have hi11 : (X 1 1).im=0 := by linarith
  have h10 : X 1 0=star (X 0 1) := (hX.apply 1 0).symm
  have ht := congrArg Complex.re htr
  simp only [Matrix.trace,Fin.sum_univ_two,Complex.add_re,Complex.zero_re] at ht
  change (X 0 0).re+(X 1 1).re=0 at ht
  ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [differenceState,h10,hi00,hi11] <;> linarith

theorem actualState_difference_coordinates {n : ℕ} (H : QubitMatrix)
    (J : Fin n → QubitMatrix) (hH : H.IsHermitian) (u : ℝ) (z : ℂ)
    (t : ℝ) (ht : 0≤t) :
    let X := actualState H J (differenceState u z) t
    X.IsHermitian ∧ X.trace=0 ∧ X=differenceState (X 0 0).re (X 0 1) := by
  dsimp only
  have hch := gkslSuperoperatorEvolution_isChannel H J t hH ht
  have hh : (actualState H J (differenceState u z) t).IsHermitian :=
    hch.pos.map_isHermitian (differenceState_hermitian u z)
  have htr : (actualState H J (differenceState u z) t).trace=0 := by
    rw [actualState,gkslSuperoperatorEvolution_trace H J t hH ht,differenceState_trace]
  exact ⟨hh,htr,traceless_hermitian_coordinates _ hh htr⟩

theorem finiteOutput_difference {n : ℕ} (H : QubitMatrix)
    (J : Fin n → QubitMatrix) (hH : H.IsHermitian) (t : ℝ) (ht : 0≤t) :
    (finiteOutput H J t).1+(finiteOutput H J t).2-1 =
      (actualState H J (Matrix.single 0 0 1-Matrix.single 1 1 1) t 0 0).re := by
  have htr := gkslSuperoperatorEvolution_trace H J t hH ht (Matrix.single 1 1 1)
  have hre := congrArg Complex.re htr
  simp only [Matrix.trace,Fin.sum_univ_two,Complex.add_re] at hre
  simp [Matrix.single_apply] at hre
  rw [finiteOutput_eq_superoperator_probabilities]
  simp only [actualState,map_sub,Matrix.sub_apply,Complex.sub_re]
  linarith

/-- 原始双输入和原始同一测量的真实有限时间读出。 -/
theorem finiteOutput_spectral_readout {n : ℕ} (H U : QubitMatrix)
    (J : Fin n → QubitMatrix) (hH : H.IsHermitian) (p t : ℝ) (ht : 0≤t)
    (hU : Uᴴ*U=1) (hUU : U*Uᴴ=1)
    (hM : conjugate Uᴴ (Matrix.single 0 0 1)=measurement p) :
    let X := actualState (conjugate Uᴴ H) (fun μ => conjugate Uᴴ (J μ))
      (differenceState (1-2*p) (2*Real.sqrt (p*(1-p)))) t
    (finiteOutput H J t).1+(finiteOutput H J t).2-1 =
      (1-2*p)*(X 0 0).re + 2*Real.sqrt (p*(1-p))*(X 0 1).re := by
  dsimp only
  let Δ : QubitMatrix := Matrix.single 0 0 1-Matrix.single 1 1 1
  have hΔ := preparation_difference_in_frame U p hU hM
  have hback : conjugate U (conjugate Uᴴ Δ)=Δ := by
    simpa using conjugate_inverse Uᴴ Δ (by simpa using hUU)
  have hinput : Δ=conjugate U (differenceState (1-2*p) (2*Real.sqrt (p*(1-p)))) := by
    rw [← hΔ]
    exact hback.symm
  rw [finiteOutput_difference H J hH t ht]
  change (actualState H J Δ t 0 0).re=_
  rw [hinput,actualState_conjugate H U _ J hU hUU t,conjugate_measurement_trace,hM]
  have hc := actualState_difference_coordinates (conjugate Uᴴ H)
    (fun μ => conjugate Uᴴ (J μ)) (conjugate_hermitian _ _ hH)
    (1-2*p) (2*Real.sqrt (p*(1-p))) t ht
  rw [hc.2.2,measurement_readout]
  simp [differenceState]

theorem conjugate_diagonal_projectors (U : QubitMatrix) (ν : ℝ) :
    conjugate U (diagonalState ν) =
      (ν:ℂ) • pureProjector (fun i => U i 0) +
      (1-(ν:ℂ)) • pureProjector (fun i => U i 1) := by
  ext i j
  simp [conjugate,diagonalState,pureProjector,Matrix.vecMulVec,Matrix.mul_apply,
    Fin.sum_univ_two,Matrix.conjTranspose_apply]
  ring

/-- 完整谱框架从原始密度稳态产生；p 的小量结论留给实际输出预算。 -/
theorem stationary_spectral_frame {n : ℕ} (H ρ : QubitMatrix)
    (J : Fin n → QubitMatrix) (hρ : ρ.PosSemidef) (htr : ρ.trace=1)
    (hstat : gkslAction H J ρ=0) :
    ∃ (ν p : ℝ) (U : QubitMatrix),
      0≤ν ∧ ν≤1/2 ∧ 0≤p ∧ p≤1 ∧ Uᴴ*U=1 ∧ U*Uᴴ=1 ∧
      ρ=conjugate U (diagonalState ν) ∧
      ρ=(ν:ℂ) • pureProjector (fun i => U i 0) +
        (1-(ν:ℂ)) • pureProjector (fun i => U i 1) ∧
      p=normSq (U 0 1) ∧ (ρ 0 0).re=ν+(1-2*ν)*p ∧
      conjugate Uᴴ (Matrix.single 0 0 1)=measurement p ∧
      gkslAction (conjugate Uᴴ H) (fun μ => conjugate Uᴴ (J μ)) (diagonalState ν)=0 := by
  obtain ⟨ν,p,U,hν,hνh,hp,hp1,hU,hUU,hρU,hpn,hM,hpop⟩ :=
    density_measurement_frame ρ hρ htr
  exact ⟨ν,p,U,hν,hνh,hp,hp1,hU,hUU,hρU,
    hρU.trans (conjugate_diagonal_projectors U ν),hpn,hpop,hM,
    stationary_in_spectral_frame H ρ U J ν hU hUU hρU hstat⟩

end TwoStateQuantumEmbedding.ResetMixedSpectral

#print axioms TwoStateQuantumEmbedding.ResetMixedSpectral.density_spectral_basis
#print axioms TwoStateQuantumEmbedding.ResetMixedSpectral.density_spectral_positive_row
#print axioms TwoStateQuantumEmbedding.ResetMixedSpectral.density_measurement_frame
#print axioms TwoStateQuantumEmbedding.ResetMixedSpectral.stationary_in_spectral_frame
#print axioms TwoStateQuantumEmbedding.ResetMixedSpectral.actualState_conjugate
#print axioms TwoStateQuantumEmbedding.ResetMixedSpectral.preparation_difference_in_frame
#print axioms TwoStateQuantumEmbedding.ResetMixedSpectral.measurement_readout
#print axioms TwoStateQuantumEmbedding.ResetMixedSpectral.actualState_difference_coordinates
#print axioms TwoStateQuantumEmbedding.ResetMixedSpectral.finiteOutput_spectral_readout
#print axioms TwoStateQuantumEmbedding.ResetMixedSpectral.stationary_spectral_frame
