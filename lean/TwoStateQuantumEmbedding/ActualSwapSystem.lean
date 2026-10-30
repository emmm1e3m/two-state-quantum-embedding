import TwoStateQuantumEmbedding.AnalyticFoundation
import TwoStateQuantumEmbedding.CanonicalBloch
import TwoStateQuantumEmbedding.SwapCore
import TwoStateQuantumEmbedding.ExponentialGradient
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic

/-! 论文七变量交换驻点系统的实际矩阵与解析除法。 -/
noncomputable section
open Matrix Filter
open scoped Topology ContDiff BigOperators Matrix.Norms.Operator ComplexOrder

namespace TwoStateQuantumEmbedding.ActualSwapSystem

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

/-- 顺序为 ω、h、μ、ξ、v、q、ζ。 -/
abbrev Parameters := Fin 7 → ℝ
abbrev Input := ℝ × Parameters
abbrev RealMatrix := Matrix (Fin 4) (Fin 4) ℝ

/-- 迹为首坐标；与 CanonicalBloch 的坐标约定一致。 -/
def hamiltonianPart (y : Parameters) : RealMatrix :=
  !![0, 0, 0, 0;
     0, 0, -2 * y 1, 0;
     0, 2 * y 1, 0, -y 0;
     0, 0, y 0, 0]

def dissipativePart (y : Parameters) : RealMatrix :=
  let U := y 3 ^ 2 + y 4 ^ 2
  let W := y 5 ^ 2 + y 6 ^ 2
  let C := y 3 * y 5 + y 4 * y 6
  !![0, 0, 0, 0;
     4 * y 6, -2 * (W + 1), 2 * C, -2 * y 3;
     -4 * y 4, 2 * C, -2 * (U + 1), -2 * y 5;
     4 * (y 3 * y 6 - y 4 * y 5), -2 * y 3, -2 * y 5, -2 * (U + W)]

/-- 对 k 的实解析延拓；k 非负时才是合法耗散参数。 -/
def generator (p : Input) : RealMatrix := hamiltonianPart p.2 + p.1 • dissipativePart p.2

def evolution (p : Input) : RealMatrix := NormedSpace.exp (generator p)
def probabilityA (p : Input) : ℝ := (1 + evolution p 3 3 + evolution p 3 0) / 2
def probabilityB (p : Input) : ℝ := (1 + evolution p 3 3 - evolution p 3 0) / 2
def objective (p : Input) : ℝ := probabilityA p - p.2 2 * probabilityB p

def hamiltonianVector (y : Parameters) : GKSLAlgebra.BlochVec := ![y 0, 0, 2 * y 1]
def jumpDirection (y : Parameters) : GKSLAlgebra.PauliVec :=
  Swap.rankOneDirection (y 3) (y 4) (y 5) (y 6)
def kossakowskiMatrix (p : Input) : Matrix (Fin 3) (Fin 3) ℂ :=
  p.1 • GKSLAlgebra.singleK (jumpDirection p.2)

def baseParameters : Parameters := ![Real.pi, 0, Swap.slope, 0, Swap.rootTwo / 2, 0, 0]
def basePoint : Input := (0, baseParameters)
def swapUnitaryGenerator : RealMatrix :=
  !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, -Real.pi; 0, 0, Real.pi, 0]

theorem generator_at_base : generator basePoint = swapUnitaryGenerator := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [generator, basePoint, baseParameters, hamiltonianPart, swapUnitaryGenerator]

theorem dissipativePart_at_base : dissipativePart baseParameters =
    !![0, 0, 0, 0; 0, -2, 0, 0; -2 * Swap.rootTwo, 0, -3, 0; 0, 0, 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dissipativePart, baseParameters, div_pow, Swap.rootTwo_sq] <;> ring

/-- 显式七变量矩阵确实是原始跳跃的规范增广 Bloch 生成元。 -/
theorem generator_eq_canonical (p : Input) :
    generator p = CanonicalBloch.augmentedGenerator (hamiltonianVector p.2)
      (kossakowskiMatrix p) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [generator, hamiltonianPart, dissipativePart, CanonicalBloch.augmentedGenerator,
      hamiltonianVector, kossakowskiMatrix, jumpDirection, Swap.rankOneDirection,
      GKSLAlgebra.blochMatrix, GKSLAlgebra.crossMatrix, GKSLAlgebra.drift,
      GKSLAlgebra.singleK, Matrix.map_apply, Matrix.trace, Fin.sum_univ_three,
      Matrix.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im] <;> ring

theorem kossakowskiMatrix_posSemidef (p : Input) (hk : 0 ≤ p.1) :
    (kossakowskiMatrix p).PosSemidef := by
  have hs : (GKSLAlgebra.singleK (jumpDirection p.2)).PosSemidef := by
    have he : GKSLAlgebra.singleK (jumpDirection p.2) =
        GKSLAlgebra.kossakowski (fun _ : Fin 1 => jumpDirection p.2) := by
      ext i j
      simp [GKSLAlgebra.kossakowski, GKSLAlgebra.singleK]
    rw [he]
    exact GKSLAlgebra.kossakowski_posSemidef _
  exact hs.smul hk

theorem probability_eq_canonical (p : Input) :
    (probabilityA p, probabilityB p) =
      CanonicalBloch.canonicalOutput (hamiltonianVector p.2) (kossakowskiMatrix p) 1 := by
  simp [probabilityA, probabilityB, evolution, generator_eq_canonical,
    CanonicalBloch.canonicalOutput, CanonicalBloch.canonicalEvolution]

theorem probability_mem_unitTimeOutputs (p : Input) (hk : 0 ≤ p.1) :
    (probabilityA p, probabilityB p) ∈ unitTimeOutputs := by
  rw [CanonicalBloch.unitTimeOutputs_eq_canonicalOutputs]
  exact ⟨hamiltonianVector p.2, kossakowskiMatrix p,
    kossakowskiMatrix_posSemidef p hk, (probability_eq_canonical p).symm⟩

/-- 算子范数下以有限矩阵单位重组各解析元素，避免混用矩阵范数。 -/
theorem analytic_matrix_entries {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X → RealMatrix} {x : X}
    (hf : ∀ i j, AnalyticAt ℝ (fun z => f z i j) x) : AnalyticAt ℝ f x := by
  have heq : f = fun z => ∑ i : Fin 4, ∑ j : Fin 4,
      f z i j • (Matrix.single i j 1 : RealMatrix) := by
    funext z
    conv_lhs => rw [Matrix.matrix_eq_sum_single (f z)]
    congr 1
    funext i
    congr 1
    funext j
    ext a b
    simp [Matrix.single_apply, Matrix.smul_apply, smul_eq_mul]
  rw [heq]
  fun_prop

def entry (i j : Fin 4) : RealMatrix →L[ℝ] ℝ :=
  ({ toFun := fun M => M i j
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : RealMatrix →ₗ[ℝ] ℝ).toContinuousLinearMap

@[simp] theorem entry_apply (i j : Fin 4) (M : RealMatrix) : entry i j M = M i j := rfl

theorem analytic_hamiltonianPart (y : Parameters) : AnalyticAt ℝ hamiltonianPart y := by
  apply analytic_matrix_entries
  intro i j
  fin_cases i <;> fin_cases j <;> simp [hamiltonianPart]
  all_goals apply ContDiffAt.analyticAt
  all_goals fun_prop

theorem analytic_dissipativePart (y : Parameters) : AnalyticAt ℝ dissipativePart y := by
  apply analytic_matrix_entries
  intro i j
  fin_cases i <;> fin_cases j <;> simp [dissipativePart]
  all_goals apply ContDiffAt.analyticAt
  all_goals fun_prop

theorem analytic_generator (p : Input) : AnalyticAt ℝ generator p := by
  have hsnd := (ContinuousLinearMap.snd ℝ ℝ Parameters).analyticAt p
  have hfst := (ContinuousLinearMap.fst ℝ ℝ Parameters).analyticAt p
  exact ((analytic_hamiltonianPart p.2).comp hsnd).add
    (hfst.smul ((analytic_dissipativePart p.2).comp hsnd))

theorem analytic_evolution (p : Input) : AnalyticAt ℝ evolution p :=
  (NormedSpace.exp_analytic (𝕂 := ℝ) (generator p)).comp (analytic_generator p)

theorem analytic_probabilityA (p : Input) : AnalyticAt ℝ probabilityA p := by
  have h33 := (entry 3 3).analyticAt (evolution p) |>.comp (analytic_evolution p)
  have h30 := (entry 3 0).analyticAt (evolution p) |>.comp (analytic_evolution p)
  change AnalyticAt ℝ (fun p => (1 + entry 3 3 (evolution p) + entry 3 0 (evolution p)) / 2) p
  fun_prop

theorem analytic_probabilityB (p : Input) : AnalyticAt ℝ probabilityB p := by
  have h33 := (entry 3 3).analyticAt (evolution p) |>.comp (analytic_evolution p)
  have h30 := (entry 3 0).analyticAt (evolution p) |>.comp (analytic_evolution p)
  change AnalyticAt ℝ (fun p => (1 + entry 3 3 (evolution p) - entry 3 0 (evolution p)) / 2) p
  fun_prop

theorem analytic_objective (p : Input) : AnalyticAt ℝ objective p := by
  have hμ : AnalyticAt ℝ (fun p : Input => p.2 2) p :=
    ((ContinuousLinearMap.proj (2 : Fin 7) : Parameters →L[ℝ] ℝ).analyticAt p.2).comp
      ((ContinuousLinearMap.snd ℝ ℝ Parameters).analyticAt p)
  exact (analytic_probabilityA p).sub (hμ.mul (analytic_probabilityB p))

abbrev Packed := RealMatrix × ℝ

/-- 同时保留乘子 μ，使外层函数无需额外参数。 -/
def packedHamiltonian (y : Parameters) : Packed := (hamiltonianPart y, y 2)
def packedDissipative (y : Parameters) : Packed := (dissipativePart y, 0)
def packedGenerator (p : Input) : Packed := packedHamiltonian p.2 + p.1 • packedDissipative p.2
def outerObjective (z : Packed) : ℝ :=
  let E := NormedSpace.exp z.1
  (1 + E 3 3 + E 3 0) / 2 - z.2 * ((1 + E 3 3 - E 3 0) / 2)

theorem objective_eq_comp : objective = outerObjective ∘ packedGenerator := by
  funext p
  simp [objective, probabilityA, probabilityB, evolution, generator,
    outerObjective, packedGenerator, packedHamiltonian, packedDissipative]

def packedHamiltonianLinear : Parameters →L[ℝ] Packed :=
  ({ toFun := packedHamiltonian
     map_add' := by
       intro y z
       apply Prod.ext
       · ext i j
         fin_cases i <;> fin_cases j <;> simp [packedHamiltonian, hamiltonianPart] <;> ring
       · rfl
     map_smul' := by
       intro s y
       apply Prod.ext
       · ext i j
         fin_cases i <;> fin_cases j <;>
           simp [packedHamiltonian, hamiltonianPart, smul_eq_mul] <;> ring
       · rfl } : Parameters →ₗ[ℝ] Packed).toContinuousLinearMap

@[simp] theorem packedHamiltonianLinear_apply (y : Parameters) :
    packedHamiltonianLinear y = packedHamiltonian y := rfl

theorem analytic_packedDissipative (y : Parameters) : AnalyticAt ℝ packedDissipative y :=
  (analytic_dissipativePart y).prod analyticAt_const

theorem analytic_packedGenerator (p : Input) : AnalyticAt ℝ packedGenerator p := by
  have hsnd := (ContinuousLinearMap.snd ℝ ℝ Parameters).analyticAt p
  have hfst := (ContinuousLinearMap.fst ℝ ℝ Parameters).analyticAt p
  exact (packedHamiltonianLinear.analyticAt p.2 |>.comp hsnd).add
    (hfst.smul ((analytic_packedDissipative p.2).comp hsnd))

theorem analytic_outerObjective (z : Packed) : AnalyticAt ℝ outerObjective z := by
  have hfst := (ContinuousLinearMap.fst ℝ RealMatrix ℝ).analyticAt z
  have hsnd := (ContinuousLinearMap.snd ℝ RealMatrix ℝ).analyticAt z
  have hE := (NormedSpace.exp_analytic (𝕂 := ℝ) z.1).comp hfst
  have h33 : AnalyticAt ℝ (fun w : Packed => entry 3 3 (NormedSpace.exp w.1)) z :=
    (entry 3 3).analyticAt _ |>.comp hE
  have h30 : AnalyticAt ℝ (fun w : Packed => entry 3 0 (NormedSpace.exp w.1)) z :=
    (entry 3 0).analyticAt _ |>.comp hE
  change AnalyticAt ℝ (fun z : Packed =>
    (1 + entry 3 3 (NormedSpace.exp z.1) + entry 3 0 (NormedSpace.exp z.1)) / 2 -
      z.2 * ((1 + entry 3 3 (NormedSpace.exp z.1) - entry 3 0 (NormedSpace.exp z.1)) / 2)) z
  have ha : AnalyticAt ℝ (fun z : Packed =>
      (1 + entry 3 3 (NormedSpace.exp z.1) + entry 3 0 (NormedSpace.exp z.1)) / 2) z := by
    fun_prop
  have hb : AnalyticAt ℝ (fun z : Packed =>
      (1 + entry 3 3 (NormedSpace.exp z.1) - entry 3 0 (NormedSpace.exp z.1)) / 2) z := by
    fun_prop
  exact ha.sub (hsnd.mul hb)

def directionIndex (j : Fin 4) : Fin 7 := ⟨j.val + 3, by omega⟩
def directionVector (j : Fin 4) : Parameters := Pi.single (directionIndex j) 1

theorem packedHamiltonian_direction_zero (j : Fin 4) :
    packedHamiltonianLinear (directionVector j) = 0 := by
  apply Prod.ext
  · ext i l
    fin_cases j <;> fin_cases i <;> fin_cases l <;>
      simp [packedHamiltonianLinear_apply, packedHamiltonian, hamiltonianPart,
        directionVector, directionIndex]
  · fin_cases j <;> simp [packedHamiltonianLinear_apply, packedHamiltonian,
      directionVector, directionIndex]

/-- 这是真实 J 的四个方向导数的解析商，零点处由同一公式定义。 -/
def dividedDirection (j : Fin 4) (p : Input) : ℝ :=
  fderiv ℝ outerObjective (packedGenerator p)
    (fderiv ℝ packedDissipative p.2 (directionVector j))

theorem analytic_dividedDirection (j : Fin 4) (p : Input) :
    AnalyticAt ℝ (dividedDirection j) p := by
  have hsnd := (ContinuousLinearMap.snd ℝ ℝ Parameters).analyticAt p
  have houter := (analytic_outerObjective (packedGenerator p)).fderiv.comp
    (analytic_packedGenerator p)
  have hinner := (analytic_packedDissipative p.2).fderiv.comp hsnd
  exact ((houter.contDiffAt : ContDiffAt ℝ ω _ _).clm_apply
    ((hinner.contDiffAt : ContDiffAt ℝ ω _ _).clm_apply contDiffAt_const)).analyticAt

theorem direction_factor (j : Fin 4) (p : Input) :
    fderiv ℝ objective p (0, directionVector j) = p.1 * dividedDirection j p := by
  have hA := packedHamiltonianLinear.hasFDerivAt.comp p hasFDerivAt_snd
  have hR := (analytic_packedDissipative p.2).differentiableAt.hasFDerivAt.comp p
    hasFDerivAt_snd
  have hQ := hA.add (hasFDerivAt_fst.smul hR)
  have hO := (analytic_outerObjective (packedGenerator p)).differentiableAt.hasFDerivAt
  rw [objective_eq_comp]
  rw [(hO.comp p hQ).fderiv]
  change fderiv ℝ outerObjective (packedGenerator p)
      (packedHamiltonianLinear (directionVector j) +
        (p.1 • fderiv ℝ packedDissipative p.2 (directionVector j) +
          (0 : ℝ) • packedDissipative p.2)) = _
  rw [packedHamiltonian_direction_zero]
  simp [dividedDirection, smul_eq_mul]

theorem dividedDirection_eq_quotient (j : Fin 4) (p : Input) (hk : p.1 ≠ 0) :
    dividedDirection j p = fderiv ℝ objective p (0, directionVector j) / p.1 := by
  rw [direction_factor]
  field_simp

/-- J 的任意固定方向导数仍联合解析。 -/
theorem analytic_objective_direction (v : Input) (p : Input) :
    AnalyticAt ℝ (fun q => fderiv ℝ objective q v) p :=
  (((analytic_objective p).fderiv.contDiffAt : ContDiffAt ℝ ω _ _).clm_apply
    contDiffAt_const).analyticAt

/-- 论文 G，未知量与方程顺序均固定为 ω、h、μ、ξ、v、q、ζ。 -/
def stationarity (p : Input) : Parameters :=
  ![fderiv ℝ objective p (0, Pi.single 0 1),
    fderiv ℝ objective p (0, Pi.single 1 1),
    fderiv ℝ objective p (1, 0),
    dividedDirection 0 p, dividedDirection 1 p,
    dividedDirection 2 p, dividedDirection 3 p]

theorem analytic_stationarity (p : Input) : AnalyticAt ℝ stationarity p := by
  apply AnalyticAt.pi
  intro j
  fin_cases j <;> simp [stationarity]
  · exact analytic_objective_direction _ _
  · exact analytic_objective_direction _ _
  · exact analytic_objective_direction _ _
  all_goals exact analytic_dividedDirection _ _

/-- 延拓值与论文积分式在 k=0 给出的混合导数一致。 -/
theorem dividedDirection_zero_eq_mixed_derivative (j : Fin 4) (y : Parameters) :
    deriv (fun k : ℝ => fderiv ℝ objective (k, y) (0, directionVector j)) 0 =
      dividedDirection j (0, y) := by
  have hq : AnalyticAt ℝ (fun k : ℝ => dividedDirection j (k, y)) 0 :=
    (analytic_dividedDirection j (0, y)).comp (f := fun k : ℝ => (k, y))
      (analyticAt_id.prod analyticAt_const)
  apply QuantumEmbedding.AnalyticFoundation.analytic_factor_value_eq_deriv hq
  exact Eventually.of_forall fun k => by simpa [smul_eq_mul] using direction_factor j (k, y)

/-- 未除以 k 的原始七个驻点方程。 -/
def rawStationarity (p : Input) : Parameters :=
  ![fderiv ℝ objective p (0, Pi.single 0 1),
    fderiv ℝ objective p (0, Pi.single 1 1),
    fderiv ℝ objective p (1, 0),
    fderiv ℝ objective p (0, directionVector 0),
    fderiv ℝ objective p (0, directionVector 1),
    fderiv ℝ objective p (0, directionVector 2),
    fderiv ℝ objective p (0, directionVector 3)]

theorem stationarity_zero_iff_raw (p : Input) (hk : p.1 ≠ 0) :
    stationarity p = 0 ↔ rawStationarity p = 0 := by
  simp [funext_iff, Fin.forall_fin_succ, stationarity, rawStationarity,
    direction_factor, mul_eq_zero, hk]

theorem objective_direction_at_zero (j : Fin 4) (y : Parameters) :
    fderiv ℝ objective (0, y) (0, directionVector j) = 0 := by
  rw [direction_factor]
  simp

theorem generator_scale_derivative (p : Input) :
    fderiv ℝ generator p (1, 0) = dissipativePart p.2 := by
  have hA := (analytic_hamiltonianPart p.2).differentiableAt.hasFDerivAt.comp p
    hasFDerivAt_snd
  have hR := (analytic_dissipativePart p.2).differentiableAt.hasFDerivAt.comp p
    hasFDerivAt_snd
  rw [show fderiv ℝ generator p = _ from (hA.add (hasFDerivAt_fst.smul hR)).fderiv]
  change fderiv ℝ hamiltonianPart p.2 0 +
    (p.1 • fderiv ℝ dissipativePart p.2 0 + (1 : ℝ) • dissipativePart p.2) = _
  simp

/-- 真实指数的尺度导数化为 Duhamel 积分；此处没有假定论文的一阶系数。 -/
theorem evolution_scale_derivative (p : Input) :
    fderiv ℝ evolution p (1, 0) =
      ∫ s in (0 : ℝ)..1,
        NormedSpace.exp ((1 - s) • generator p) * dissipativePart p.2 *
          NormedSpace.exp (s • generator p) := by
  have hc := (ExponentialGradient.hasFDerivAt_exp_integral (generator p)).comp p
    (analytic_generator p).differentiableAt.hasFDerivAt
  rw [show fderiv ℝ evolution p = _ from hc.fderiv]
  change ExponentialGradient.expDerivative (generator p)
    (fderiv ℝ generator p (1, 0)) = _
  rw [generator_scale_derivative, ExponentialGradient.expDerivative_apply]
  rfl

#print axioms analytic_generator
#print axioms generator_at_base
#print axioms dissipativePart_at_base
#print axioms generator_eq_canonical
#print axioms kossakowskiMatrix_posSemidef
#print axioms probability_eq_canonical
#print axioms probability_mem_unitTimeOutputs
#print axioms analytic_evolution
#print axioms analytic_probabilityA
#print axioms analytic_probabilityB
#print axioms analytic_objective
#print axioms objective_eq_comp
#print axioms packedHamiltonian_direction_zero
#print axioms analytic_dividedDirection
#print axioms direction_factor
#print axioms dividedDirection_eq_quotient
#print axioms analytic_stationarity
#print axioms dividedDirection_zero_eq_mixed_derivative
#print axioms stationarity_zero_iff_raw
#print axioms objective_direction_at_zero
#print axioms generator_scale_derivative
#print axioms evolution_scale_derivative
#print axioms analytic_matrix_entries
#print axioms entry_apply
#print axioms analytic_hamiltonianPart
#print axioms analytic_dissipativePart
#print axioms packedHamiltonianLinear_apply
#print axioms analytic_packedDissipative
#print axioms analytic_packedGenerator
#print axioms analytic_outerObjective
#print axioms analytic_objective_direction

end TwoStateQuantumEmbedding.ActualSwapSystem
