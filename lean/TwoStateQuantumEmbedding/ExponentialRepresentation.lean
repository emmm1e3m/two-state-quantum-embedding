import TwoStateQuantumEmbedding.Model
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Tactic

/-! 原始 GKSL 作用与 Liouville 矩阵指数的语义桥。 -/

noncomputable section
open Matrix Complex
open scoped Matrix.Norms.Operator

namespace TwoStateQuantumEmbedding

local instance matrixIsNormable (ι : Type*) [Fintype ι] [DecidableEq ι] :
    IsNormableSpace ℂ (Matrix ι ι ℂ) :=
  isNormableSpace_of_finiteDimensional

@[implicit_reducible] local instance matrixCLMNormedRing
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    NormedRing (Matrix ι ι ℂ →L[ℂ] Matrix ι ι ℂ) :=
  ContinuousLinearMap.toNormedRing

@[implicit_reducible] local instance matrixCLMNormedAlgebraComplex
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    NormedAlgebra ℂ (Matrix ι ι ℂ →L[ℂ] Matrix ι ι ℂ) :=
  ContinuousLinearMap.toNormedAlgebra

local instance matrixCLMTopologicalRing
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    IsTopologicalRing (Matrix ι ι ℂ →L[ℂ] Matrix ι ι ℂ) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

@[implicit_reducible] local instance matrixCLMNormedAlgebraRat
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    NormedAlgebra ℚ (Matrix ι ι ℂ →L[ℂ] Matrix ι ι ℂ) :=
  NormedAlgebra.restrictScalars ℚ ℂ (Matrix ι ι ℂ →L[ℂ] Matrix ι ι ℂ)

local instance matrixCLMCompleteSpace
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    CompleteSpace (Matrix ι ι ℂ →L[ℂ] Matrix ι ι ℂ) :=
  FiniteDimensional.complete ℂ (Matrix ι ι ℂ →L[ℂ] Matrix ι ι ℂ)

section General
variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- 将矩阵的行列指标组成有序对；不改变原模型的指标顺序。 -/
def matrixVecLinearEquiv : Matrix ι ι ℂ ≃ₗ[ℂ] (ι × ι → ℂ) where
  toFun ρ ij := ρ ij.1 ij.2
  invFun v i j := v (i, j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 有限维保证向量化及其逆映射均连续。 -/
def matrixVecContinuousLinearEquiv : Matrix ι ι ℂ ≃L[ℂ] (ι × ι → ℂ) :=
  (matrixVecLinearEquiv ι).toContinuousLinearEquiv

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem matrixVec_apply (ρ : Matrix ι ι ℂ) (ij : ι × ι) :
    matrixVecLinearEquiv ι ρ ij = ρ ij.1 ij.2 := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem matrixVec_symm_apply (v : ι × ι → ℂ) (i j : ι) :
    (matrixVecLinearEquiv ι).symm v i j = v (i, j) := rfl

/-- 超算子的复线性自同态代数与矩阵代数同构，乘法对应复合。 -/
def matrixEndAlgEquiv : Module.End ℂ (Matrix ι ι ℂ) ≃ₐ[ℂ]
    Matrix (ι × ι) (ι × ι) ℂ :=
  ((matrixVecLinearEquiv ι).conjAlgEquiv ℂ).trans LinearMap.toMatrixAlgEquiv'

/-- 连续线性超算子使用相同的代数表示。 -/
def matrixCLMAlgEquiv : (Matrix ι ι ℂ →L[ℂ] Matrix ι ι ℂ) ≃ₐ[ℂ]
    Matrix (ι × ι) (ι × ι) ℂ :=
  (Module.End.toContinuousLinearMap (𝕜 := ℂ) (Matrix ι ι ℂ)).symm.trans
    (matrixEndAlgEquiv ι)

@[simp] theorem matrixEndAlgEquiv_apply
    (f : Module.End ℂ (Matrix ι ι ℂ)) (ij kl : ι × ι) :
    matrixEndAlgEquiv ι f ij kl = f (Matrix.single kl.1 kl.2 1) ij.1 ij.2 := by
  change f ((matrixVecLinearEquiv ι).symm (Pi.single kl 1)) ij.1 ij.2 = _
  apply congrArg (fun ρ : Matrix ι ι ℂ => f ρ ij.1 ij.2)
  ext i j
  simp [Matrix.single_apply, Pi.single_apply, Prod.ext_iff, eq_comm]

@[simp] theorem matrixCLMAlgEquiv_apply
    (f : Matrix ι ι ℂ →L[ℂ] Matrix ι ι ℂ) (ij kl : ι × ι) :
    matrixCLMAlgEquiv ι f ij kl = f (Matrix.single kl.1 kl.2 1) ij.1 ij.2 :=
  matrixEndAlgEquiv_apply ι f.toLinearMap ij kl

/-- 表示同构连续，因此能逐项传递指数级数。 -/
theorem continuous_matrixCLMAlgEquiv : Continuous (matrixCLMAlgEquiv ι) :=
  (matrixCLMAlgEquiv ι).toLinearMap.continuous_of_finiteDimensional

/-- 无需任何指数表示假设：连续环同构将超算子指数送到矩阵指数。 -/
theorem matrixCLMAlgEquiv_exp (f : Matrix ι ι ℂ →L[ℂ] Matrix ι ι ℂ) :
    matrixCLMAlgEquiv ι (NormedSpace.exp f) =
      NormedSpace.exp (matrixCLMAlgEquiv ι f) :=
  @NormedSpace.map_exp _ _ _ _ (matrixCLMCompleteSpace ι) _ _ _ _ _
    (matrixCLMAlgEquiv ι) (continuous_matrixCLMAlgEquiv ι) f

/-- 复参数版本同时覆盖实时间与 QICLean 的复数强制转换约定。 -/
theorem matrixCLMAlgEquiv_exp_smul (z : ℂ)
    (f : Matrix ι ι ℂ →L[ℂ] Matrix ι ι ℂ) :
    matrixCLMAlgEquiv ι (NormedSpace.exp (z • f)) =
      NormedSpace.exp (z • matrixCLMAlgEquiv ι f) := by
  rw [matrixCLMAlgEquiv_exp, map_smul]

/-- 表示矩阵的乘向量作用等于原超算子作用后的向量化。 -/
theorem matrixEndAlgEquiv_mulVec (f : Module.End ℂ (Matrix ι ι ℂ))
    (ρ : Matrix ι ι ℂ) :
    matrixEndAlgEquiv ι f *ᵥ matrixVecLinearEquiv ι ρ =
      matrixVecLinearEquiv ι (f ρ) := by
  change Matrix.toLinAlgEquiv' (LinearMap.toMatrixAlgEquiv'
    ((matrixVecLinearEquiv ι).conjAlgEquiv ℂ f)) (matrixVecLinearEquiv ι ρ) = _
  rw [Matrix.toLinAlgEquiv'_toMatrixAlgEquiv']
  rfl

theorem matrixCLMAlgEquiv_mulVec (f : Matrix ι ι ℂ →L[ℂ] Matrix ι ι ℂ)
    (ρ : Matrix ι ι ℂ) :
    matrixCLMAlgEquiv ι f *ᵥ matrixVecLinearEquiv ι ρ =
      matrixVecLinearEquiv ι (f ρ) :=
  matrixEndAlgEquiv_mulVec ι f.toLinearMap ρ

/-- 真正的指数作用桥，适用于任意输入矩阵和任意复参数。 -/
theorem matrix_exp_mulVec_eq_vec_exp (z : ℂ)
    (f : Matrix ι ι ℂ →L[ℂ] Matrix ι ι ℂ) (ρ : Matrix ι ι ℂ) :
    NormedSpace.exp (z • matrixCLMAlgEquiv ι f) *ᵥ matrixVecLinearEquiv ι ρ =
      matrixVecLinearEquiv ι ((NormedSpace.exp (z • f)) ρ) := by
  rw [← matrixCLMAlgEquiv_exp_smul]
  exact matrixCLMAlgEquiv_mulVec ι _ ρ

end General

/-! 以下直接实例化原模型的定义，不添加 Hermitian、正性或表示假设。 -/

/-- 原模型的有限维 GKSL 线性作用天然连续。 -/
def gkslContinuousLinearMap {n : ℕ} (H : QubitMatrix) (A : Fin n → QubitMatrix) :
    QubitMatrix →L[ℂ] QubitMatrix :=
  (gkslLinearMap H A).toContinuousLinearMap

@[simp] theorem gkslContinuousLinearMap_apply {n : ℕ} (H : QubitMatrix)
    (A : Fin n → QubitMatrix) (ρ : QubitMatrix) :
    gkslContinuousLinearMap H A ρ = gkslAction H A ρ := rfl

/-- 直接在连续线性超算子代数中定义指数演化。 -/
def gkslSuperoperatorEvolution {n : ℕ} (H : QubitMatrix)
    (A : Fin n → QubitMatrix) (t : ℝ) : QubitMatrix →L[ℂ] QubitMatrix :=
  NormedSpace.exp ((t : ℂ) • gkslContinuousLinearMap H A)

/-- 复参数的实数嵌入与原模型使用的实标量作用一致。 -/
theorem gkslSuperoperatorEvolution_eq_real_exp {n : ℕ} (H : QubitMatrix)
    (A : Fin n → QubitMatrix) (t : ℝ) :
    gkslSuperoperatorEvolution H A t =
      NormedSpace.exp (t • gkslContinuousLinearMap H A) := rfl

/-- 此形式直接匹配有限维超算子库的 End 到 CLM 指数约定。 -/
theorem gkslSuperoperatorEvolution_eq_end_exp {n : ℕ} (H : QubitMatrix)
    (A : Fin n → QubitMatrix) (t : ℝ) :
    gkslSuperoperatorEvolution H A t =
      NormedSpace.exp ((t : ℂ) •
        (Module.End.toContinuousLinearMap QubitMatrix) (gkslLinearMap H A)) := rfl

/-- 原 actionMatrix 正是代数表示，而非另一个仅形式相似的数组。 -/
theorem matrixCLMAlgEquiv_eq_actionMatrix (f : QubitMatrix →L[ℂ] QubitMatrix) :
    matrixCLMAlgEquiv (Fin 2) f = actionMatrix f := by
  ext ij kl
  exact matrixCLMAlgEquiv_apply (Fin 2) f ij kl

@[simp] theorem matrixCLMAlgEquiv_gksl {n : ℕ} (H : QubitMatrix)
    (A : Fin n → QubitMatrix) :
    matrixCLMAlgEquiv (Fin 2) (gkslContinuousLinearMap H A) = gkslMatrix H A := by
  rw [matrixCLMAlgEquiv_eq_actionMatrix]
  rfl

/-- 四维指数与真实超算子指数在任意实时间精确对应。 -/
theorem finiteEvolution_eq_superoperator_representation {n : ℕ}
    (H : QubitMatrix) (A : Fin n → QubitMatrix) (t : ℝ) :
    finiteEvolution H A t =
      matrixCLMAlgEquiv (Fin 2) (gkslSuperoperatorEvolution H A t) := by
  rw [gkslSuperoperatorEvolution, matrixCLMAlgEquiv_exp_smul, matrixCLMAlgEquiv_gksl]
  rfl

/-- 对任意输入矩阵，原 finiteEvolution 的作用就是超算子指数的作用。 -/
theorem finiteEvolution_mulVec_eq_superoperator {n : ℕ}
    (H : QubitMatrix) (A : Fin n → QubitMatrix) (t : ℝ) (ρ : QubitMatrix) :
    finiteEvolution H A t *ᵥ (fun ij => ρ ij.1 ij.2) =
      fun ij => gkslSuperoperatorEvolution H A t ρ ij.1 ij.2 := by
  rw [finiteEvolution_eq_superoperator_representation]
  exact matrixCLMAlgEquiv_mulVec (Fin 2) _ ρ

/-- 每一个 Liouville 矩阵元均是演化后的矩阵单位的对应矩阵元。 -/
theorem finiteEvolution_entry_eq_superoperator {n : ℕ}
    (H : QubitMatrix) (A : Fin n → QubitMatrix) (t : ℝ) (ij kl : LiouvilleIndex) :
    finiteEvolution H A t ij kl =
      gkslSuperoperatorEvolution H A t (Matrix.single kl.1 kl.2 1) ij.1 ij.2 := by
  rw [finiteEvolution_eq_superoperator_representation, matrixCLMAlgEquiv_apply]

/-- 两项输出等于同一基下两个矩阵单位的演化对角元的实部。 -/
theorem finiteOutput_eq_superoperator_probabilities {n : ℕ}
    (H : QubitMatrix) (A : Fin n → QubitMatrix) (t : ℝ) :
    finiteOutput H A t =
      ((gkslSuperoperatorEvolution H A t (Matrix.single 0 0 1) 0 0).re,
       (gkslSuperoperatorEvolution H A t (Matrix.single 1 1 1) 1 1).re) := by
  simp only [finiteOutput, finiteEvolution_entry_eq_superoperator]

end TwoStateQuantumEmbedding

#print axioms TwoStateQuantumEmbedding.matrixCLMAlgEquiv_exp
#print axioms TwoStateQuantumEmbedding.matrix_exp_mulVec_eq_vec_exp
#print axioms TwoStateQuantumEmbedding.gkslSuperoperatorEvolution_eq_real_exp
#print axioms TwoStateQuantumEmbedding.gkslSuperoperatorEvolution_eq_end_exp
#print axioms TwoStateQuantumEmbedding.finiteEvolution_eq_superoperator_representation
#print axioms TwoStateQuantumEmbedding.finiteEvolution_mulVec_eq_superoperator
#print axioms TwoStateQuantumEmbedding.finiteOutput_eq_superoperator_probabilities


