import TwoStateQuantumEmbedding.ActualSwapSystem

/-! 实际七变量函数的反射协变，包含负 k 和 k=0 的解析除法。 -/
noncomputable section
open Matrix Filter
open scoped Topology Matrix.Norms.Operator

namespace TwoStateQuantumEmbedding.ActualSwapSystem

set_option maxRecDepth 3000
set_option maxHeartbeats 1500000

def reflectionSigns : Parameters := ![1, -1, 1, -1, 1, 1, -1]

def reflectParameters : Parameters →L[ℝ] Parameters :=
  (show Parameters →ₗ[ℝ] Parameters from
    { toFun := fun y i => reflectionSigns i * y i
      map_add' := by intros; ext i; simp [mul_add]
      map_smul' := by intros; ext i; simp [smul_eq_mul]; ring }).toContinuousLinearMap

@[simp] theorem reflectParameters_apply (y : Parameters) (i : Fin 7) :
    reflectParameters y i = reflectionSigns i * y i := rfl

theorem reflectionSigns_sq (i : Fin 7) : reflectionSigns i * reflectionSigns i = 1 := by
  fin_cases i <;> norm_num [reflectionSigns]

@[simp] theorem reflectParameters_involutive (y : Parameters) :
    reflectParameters (reflectParameters y) = y := by
  ext i
  simp only [reflectParameters_apply, ← mul_assoc, reflectionSigns_sq, one_mul]

@[simp] theorem reflectParameters_base : reflectParameters baseParameters = baseParameters := by
  ext i
  fin_cases i <;> simp [reflectionSigns, baseParameters]

def reflectInput : Input →L[ℝ] Input :=
  (ContinuousLinearMap.id ℝ ℝ).prodMap reflectParameters

@[simp] theorem reflectInput_apply (p : Input) : reflectInput p = (p.1, reflectParameters p.2) := rfl

@[simp] theorem reflectInput_involutive (p : Input) : reflectInput (reflectInput p) = p := by
  simp

theorem reflectParameters_single (i : Fin 7) :
    reflectParameters (Pi.single i 1) = reflectionSigns i • Pi.single i 1 := by
  ext j
  by_cases hj : j = i
  · subst j
    simp
  · simp [hj]

theorem reflectInput_parameter_direction (i : Fin 7) :
    reflectInput (0, Pi.single i 1) = reflectionSigns i • ((0 : ℝ), Pi.single i 1) := by
  simp [reflectParameters_single]

@[simp] theorem reflectInput_scale_direction : reflectInput (1, 0) = (1, 0) := by simp

def reflectionMatrix : RealMatrix := Matrix.diagonal ![1, -1, 1, 1]

/-- 反酉 Z 共轭在实 Bloch 坐标中只翻转 X 坐标。 -/
theorem generator_reflection_intertwines (p : Input) :
    SemiconjBy reflectionMatrix (generator p) (generator (reflectInput p)) := by
  change reflectionMatrix * generator p = generator (reflectInput p) * reflectionMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reflectionMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal, generator,
      hamiltonianPart, dissipativePart, reflectionSigns] <;> ring

theorem evolution_reflection_intertwines (p : Input) :
    reflectionMatrix * evolution p = evolution (reflectInput p) * reflectionMatrix :=
  (generator_reflection_intertwines p).exp_right

theorem evolution_reflection_readout (p : Input) :
    evolution (reflectInput p) 3 3 = evolution p 3 3 ∧
    evolution (reflectInput p) 3 0 = evolution p 3 0 := by
  have h33 := congrArg (fun A : RealMatrix => A 3 3) (evolution_reflection_intertwines p)
  have h30 := congrArg (fun A : RealMatrix => A 3 0) (evolution_reflection_intertwines p)
  constructor
  · simpa [reflectionMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal] using h33.symm
  · simpa [reflectionMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal] using h30.symm

@[simp] theorem probabilityA_reflect (p : Input) : probabilityA (reflectInput p) = probabilityA p := by
  simp only [probabilityA, (evolution_reflection_readout p).1, (evolution_reflection_readout p).2]

@[simp] theorem probabilityB_reflect (p : Input) : probabilityB (reflectInput p) = probabilityB p := by
  simp only [probabilityB, (evolution_reflection_readout p).1, (evolution_reflection_readout p).2]

@[simp] theorem objective_reflect (p : Input) : objective (reflectInput p) = objective p := by
  unfold objective
  rw [probabilityA_reflect, probabilityB_reflect]
  simp [reflectionSigns]

/-- 对真实目标应用链式法则，没有把梯度对称性当作前提。 -/
theorem objective_derivative_reflect (p v : Input) :
    fderiv ℝ objective (reflectInput p) v = fderiv ℝ objective p (reflectInput v) := by
  have hc := (analytic_objective (reflectInput (reflectInput p))).differentiableAt.hasFDerivAt.comp
    (reflectInput p) reflectInput.hasFDerivAt
  simp only [reflectInput_involutive, Function.comp_def, objective_reflect] at hc
  rw [hc.fderiv]
  rfl

theorem objective_parameter_derivative_reflect (p : Input) (i : Fin 7) :
    fderiv ℝ objective (reflectInput p) (0, Pi.single i 1) =
      reflectionSigns i * fderiv ℝ objective p (0, Pi.single i 1) := by
  rw [objective_derivative_reflect, reflectInput_parameter_direction, map_smul]
  rfl

theorem objective_scale_derivative_reflect (p : Input) :
    fderiv ℝ objective (reflectInput p) (1, 0) = fderiv ℝ objective p (1, 0) := by
  rw [objective_derivative_reflect, reflectInput_scale_direction]

/-- 除法的非零 k 部分直接取自真实方向导数的协变。 -/
theorem dividedDirection_reflect_nonzero (j : Fin 4) (p : Input) (hk : p.1 ≠ 0) :
    dividedDirection j (reflectInput p) =
      reflectionSigns (directionIndex j) * dividedDirection j p := by
  rw [dividedDirection_eq_quotient j _ (by simpa using hk),
    dividedDirection_eq_quotient j p hk]
  change fderiv ℝ objective (reflectInput p) (0, Pi.single (directionIndex j) 1) / p.1 = _
  rw [objective_parameter_derivative_reflect]
  simp only [directionVector]
  ring

/-- k=0 单独使用实际混合导数恒等式，故解析延拓的零集没有被跳过。 -/
theorem dividedDirection_reflect_zero (j : Fin 4) (y : Parameters) :
    dividedDirection j (0, reflectParameters y) =
      reflectionSigns (directionIndex j) * dividedDirection j (0, y) := by
  rw [← dividedDirection_zero_eq_mixed_derivative j (reflectParameters y)]
  have he : (fun k : ℝ => fderiv ℝ objective (k, reflectParameters y) (0, directionVector j)) =
      fun k => reflectionSigns (directionIndex j) *
        fderiv ℝ objective (k, y) (0, directionVector j) := by
    funext k
    exact objective_parameter_derivative_reflect (k, y) (directionIndex j)
  rw [he, deriv_const_mul_field, dividedDirection_zero_eq_mixed_derivative]

theorem dividedDirection_reflect (j : Fin 4) (p : Input) :
    dividedDirection j (reflectInput p) =
      reflectionSigns (directionIndex j) * dividedDirection j p := by
  by_cases hk : p.1 = 0
  · rcases p with ⟨k, y⟩
    change k = 0 at hk
    subst k
    exact dividedDirection_reflect_zero j y
  · exact dividedDirection_reflect_nonzero j p hk

/-- 全实 k 的实际七方程精确协变。 -/
theorem stationarity_reflect (p : Input) :
    stationarity (reflectInput p) = reflectParameters (stationarity p) := by
  ext i
  fin_cases i <;>
    simp [stationarity, objective_parameter_derivative_reflect,
      objective_scale_derivative_reflect, dividedDirection_reflect,
      reflectionSigns, directionIndex, -reflectInput_apply]

theorem stationarity_reflect_zero_iff (p : Input) :
    stationarity (reflectInput p) = 0 ↔ stationarity p = 0 := by
  rw [stationarity_reflect]
  constructor
  · intro he
    have hr := congrArg reflectParameters he
    simpa using hr
  · intro he
    simp [he]

#print axioms probabilityA_reflect
#print axioms probabilityB_reflect
#print axioms objective_derivative_reflect
#print axioms dividedDirection_reflect_zero
#print axioms stationarity_reflect
#print axioms stationarity_reflect_zero_iff

end TwoStateQuantumEmbedding.ActualSwapSystem
