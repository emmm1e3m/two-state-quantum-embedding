import TwoStateQuantumEmbedding.ResetMixedSpectral
import TwoStateQuantumEmbedding.ResetMixedAlgebra

noncomputable section
open Matrix Complex
open scoped BigOperators Matrix.Norms.Operator ComplexOrder
namespace TwoStateQuantumEmbedding.ResetMixedSpectral
open PureStationary

theorem spectral_column_eigenvectors (ρ U : QubitMatrix) (ν : ℝ)
    (hU : Uᴴ*U=1) (hρ : ρ=conjugate U (diagonalState ν)) :
    ρ *ᵥ (fun i => U i 0)=(ν:ℂ) • (fun i => U i 0) ∧
    ρ *ᵥ (fun i => U i 1)=(1-(ν:ℂ)) • (fun i => U i 1) := by
  have hm : ρ*U=U*diagonalState ν := by
    rw [hρ]
    simp only [conjugate,Matrix.mul_assoc,← Matrix.mul_assoc Uᴴ U,hU,Matrix.mul_one]
  constructor
  · ext i
    have hi := congrArg (fun M : QubitMatrix => M i 0) hm
    simpa [Matrix.mul_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_two,
      diagonalState,smul_eq_mul,mul_comm] using hi
  · ext i
    have hi := congrArg (fun M : QubitMatrix => M i 1) hm
    simpa [Matrix.mul_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_two,
      diagonalState,smul_eq_mul,mul_comm] using hi

theorem actualState_of_action_eq {n m : ℕ} (H K : QubitMatrix)
    (J : Fin n → QubitMatrix) (L : Fin m → QubitMatrix)
    (hL : ∀ X, gkslAction H J X=gkslAction K L X) (X : QubitMatrix) (t : ℝ) :
    actualState H J X t=actualState K L X t := by
  have he : gkslContinuousLinearMap H J=gkslContinuousLinearMap K L := by
    apply ContinuousLinearMap.ext
    exact hL
  simp only [actualState,gkslSuperoperatorEvolution,he]

theorem diagonalState_eq_mixed (ν : ℝ) : diagonalState ν=ResetMixed.state 1 ν 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [diagonalState,ResetMixed.state]

theorem differenceState_eq_mixed (u : ℝ) (z : ℂ) :
    differenceState u z=ResetMixed.state 0 u z := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [differenceState,ResetMixed.state]

theorem measurement_eq_mixed (p : ℝ) :
    measurement p=ResetMixed.measurement p (2*Real.sqrt (p*(1-p))) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [measurement,ResetMixed.measurement]

/-- 原始任意密度稳态到 148 坐标：共同谱基、完整生成元和实际指数均保留。 -/
theorem original_mixed_normal_form {n : ℕ} (H ρ : QubitMatrix)
    (J : Fin n → QubitMatrix) (hH : H.IsHermitian)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) (hstat : gkslAction H J ρ=0) :
    ∃ (ν p : ℝ) (U : QubitMatrix) (ω : ℝ) (h : ℂ) (x y z : Fin n → ℂ),
      0≤ν ∧ ν≤1/2 ∧ 0≤p ∧ p≤1 ∧ Uᴴ*U=1 ∧ U*Uᴴ=1 ∧
      ρ=conjugate U (ResetMixed.state 1 ν 0) ∧
      p=normSq (U 0 1) ∧ (ρ 0 0).re=ν+(1-2*ν)*p ∧
      conjugate Uᴴ (Matrix.single 0 0 1)=
        ResetMixed.measurement p (2*Real.sqrt (p*(1-p))) ∧
      gkslAction (ResetMixed.hamiltonian ω h) (ResetMixed.jumps x y z)
        (ResetMixed.state 1 ν 0)=0 ∧
      (∀ X, gkslAction (conjugate Uᴴ H) (fun μ => conjugate Uᴴ (J μ)) X=
        gkslAction (ResetMixed.hamiltonian ω h) (ResetMixed.jumps x y z) X) ∧
      (∀ X, gkslAction H J (conjugate U X)=
        conjugate U (gkslAction (ResetMixed.hamiltonian ω h) (ResetMixed.jumps x y z) X)) ∧
      (∀ X t, actualState H J (conjugate U X) t=
        conjugate U (actualState (ResetMixed.hamiltonian ω h) (ResetMixed.jumps x y z) X t)) := by
  obtain ⟨ν,p,U,hν,hνh,hp,hp1,hU,hUU,hρU,_,hpn,hpop,hM,hs⟩ :=
    stationary_spectral_frame H ρ J hρ htr hstat
  rw [diagonalState_eq_mixed] at hs hρU
  obtain ⟨ω,h,x,y,z,hn,hsn⟩ := ResetMixed.stationary_normal_form (conjugate Uᴴ H)
    (conjugate_hermitian _ _ hH) (fun μ => conjugate Uᴴ (J μ)) ν hs
  have hback (Z : QubitMatrix) : conjugate U (conjugate Uᴴ Z)=Z := by
    simpa using conjugate_inverse Uᴴ Z (by simpa using hUU)
  have ha (X : QubitMatrix) : gkslAction H J (conjugate U X)=
      conjugate U (gkslAction (ResetMixed.hamiltonian ω h) (ResetMixed.jumps x y z) X) := by
    have hc := gksl_conjugate U (conjugate Uᴴ H) X (fun μ => conjugate Uᴴ (J μ)) hU
    simpa only [hback,hn] using hc
  refine ⟨ν,p,U,ω,h,x,y,z,hν,hνh,hp,hp1,hU,hUU,hρU,hpn,hpop,?_,hsn,hn,ha,?_⟩
  · simpa only [measurement_eq_mixed] using hM
  · intro X t
    exact actualState_intertwining H (ResetMixed.hamiltonian ω h) U J
      (ResetMixed.jumps x y z) ha X t

/-- 任意规范后的共同谱基，仍读出原始同一制备/测量的 a+b-1。 -/
theorem original_mixed_readout {n : ℕ} (H U : QubitMatrix)
    (J : Fin n → QubitMatrix) (hH : H.IsHermitian)
    (ω : ℝ) (h : ℂ) (x y z : Fin n → ℂ) (p t : ℝ) (ht : 0≤t)
    (hU : Uᴴ*U=1) (hUU : U*Uᴴ=1)
    (hM : conjugate Uᴴ (Matrix.single 0 0 1)=
      ResetMixed.measurement p (2*Real.sqrt (p*(1-p))))
    (hn : ∀ X, gkslAction (conjugate Uᴴ H) (fun μ => conjugate Uᴴ (J μ)) X=
      gkslAction (ResetMixed.hamiltonian ω h) (ResetMixed.jumps x y z) X) :
    let X := actualState (ResetMixed.hamiltonian ω h) (ResetMixed.jumps x y z)
      (ResetMixed.state 0 (1-2*p) (2*Real.sqrt (p*(1-p)))) t
    (finiteOutput H J t).1+(finiteOutput H J t).2-1=
      (1-2*p)*(X 0 0).re+2*Real.sqrt (p*(1-p))*(X 0 1).re := by
  have hm : conjugate Uᴴ (Matrix.single 0 0 1)=measurement p := by
    simpa only [measurement_eq_mixed] using hM
  have hr := finiteOutput_spectral_readout H U J hH p t ht hU hUU hm
  dsimp only at hr ⊢
  rw [actualState_of_action_eq _ _ _ _ hn] at hr
  simpa only [differenceState_eq_mixed] using hr

end TwoStateQuantumEmbedding.ResetMixedSpectral

#print axioms TwoStateQuantumEmbedding.ResetMixedSpectral.original_mixed_normal_form
#print axioms TwoStateQuantumEmbedding.ResetMixedSpectral.original_mixed_readout
#print axioms TwoStateQuantumEmbedding.ResetMixedSpectral.spectral_column_eigenvectors
