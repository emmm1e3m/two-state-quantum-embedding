import TwoStateQuantumEmbedding.ResetFamily

noncomputable section
open Matrix Complex Filter Topology
open scoped Matrix.Norms.Operator

namespace TwoStateQuantumEmbedding.ResetDiagonalFamily

/-- 实振幅单跳族；令 m=√B、n=√A、v=√U 即为正文构造。 -/
def jump (m n v : ℝ) : QubitMatrix := !![-(m : ℂ), -(v : ℂ); n, 0]
def jumps (m n v : ℝ) : Fin 1 → QubitMatrix := fun _ => jump m n v
def hamiltonian (κ : ℝ) : QubitMatrix := !![0, Complex.I * κ; -Complex.I * κ, 0]
def diagonalState (ν : ℝ) : QubitMatrix := !![(ν : ℂ), 0; 0, 1 - ν]
def mode (u x : ℝ) : QubitMatrix := !![(u : ℂ), x; x, -(u : ℂ)]
def state (ν u x : ℝ) : QubitMatrix := diagonalState ν + mode u x

theorem hamiltonian_hermitian (κ : ℝ) : (hamiltonian κ).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hamiltonian, Matrix.conjTranspose_apply]

/-- 直接展开原始 GKSL，显示实相干子空间的不变性。 -/
theorem actual_mode_action (m n v κ u x : ℝ) :
    gkslAction (hamiltonian κ) (jumps m n v) (mode u x) =
      mode (-(n ^ 2 + v ^ 2) * u + (m * v + 2 * κ) * x)
        (-(m * n + 2 * κ) * u - ((n + v) ^ 2 + m ^ 2) / 2 * x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gkslAction, dissipator, hamiltonian, jumps, jump, mode,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct] <;>
    push_cast <;> ring_nf <;> simp [Complex.I_sq] <;> ring

/-- 对角输入的真实生成元，不借用抽象稳态接口。 -/
theorem actual_diagonal_action (m n v κ ν : ℝ) :
    gkslAction (hamiltonian κ) (jumps m n v) (diagonalState ν) =
      mode (v ^ 2 * (1 - ν) - n ^ 2 * ν)
        (κ * (1 - 2 * ν) - m * n * ν - m * v / 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gkslAction, dissipator, hamiltonian, jumps, jump, diagonalState, mode,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct] <;>
    push_cast <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem actual_stationary (m n v κ ν : ℝ)
    (hpop : v ^ 2 * (1 - ν) = n ^ 2 * ν)
    (hcoh : κ * (1 - 2 * ν) = m * n * ν + m * v / 2) :
    gkslAction (hamiltonian κ) (jumps m n v) (diagonalState ν) = 0 := by
  rw [actual_diagonal_action, hpop, hcoh]
  have hc : m * n * ν + m * v / 2 - m * n * ν - m * v / 2 = 0 := by ring
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hc, mode]

/-- 定态平移后的实际二维实负反馈块。 -/
theorem actual_real_block (m n v κ ν u x : ℝ)
    (hpop : v ^ 2 * (1 - ν) = n ^ 2 * ν)
    (hcoh : κ * (1 - 2 * ν) = m * n * ν + m * v / 2) :
    gkslAction (hamiltonian κ) (jumps m n v) (state ν u x) =
      mode (-(n ^ 2 + v ^ 2) * u + (m * v + 2 * κ) * x)
        (-(m * n + 2 * κ) * u - ((n + v) ^ 2 + m ^ 2) / 2 * x) := by
  rw [state, gkslAction_add, actual_stationary m n v κ ν hpop hcoh, zero_add,
    actual_mode_action]

/-- χ 参数下的稳态占据及 Hamiltonian 系数。 -/
def occupation (χ : ℝ) : ℝ := χ ^ 2 / (1 + χ ^ 2)
def kappa (m n χ : ℝ) : ℝ := m * n * χ * (1 + χ) / (2 * (1 - χ))

theorem parameter_stationarity (m n χ : ℝ) (hχ : χ ≠ 1) :
    (χ * n) ^ 2 * (1 - occupation χ) = n ^ 2 * occupation χ ∧
    kappa m n χ * (1 - 2 * occupation χ) =
      m * n * occupation χ + m * (χ * n) / 2 := by
  have hd : 1 + χ ^ 2 ≠ 0 := by positivity
  have he : 1 - χ ≠ 0 := sub_ne_zero.mpr (Ne.symm hχ)
  constructor <;> dsimp [occupation, kappa] <;> field_simp <;> ring

theorem family_stationary (m n χ : ℝ) (hχ : χ ≠ 1) :
    gkslAction (hamiltonian (kappa m n χ)) (jumps m n (χ * n))
      (diagonalState (occupation χ)) = 0 :=
  actual_stationary m n (χ * n) (kappa m n χ) (occupation χ)
    (parameter_stationarity m n χ hχ).1 (parameter_stationarity m n χ hχ).2


@[simp] theorem mode_zero : mode 0 0 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [mode]

theorem mode_add (u x v y : ℝ) : mode u x + mode v y = mode (u + v) (x + y) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [mode] <;> ring

theorem mode_smul (a u x : ℝ) : (a : ℂ) • mode u x = mode (a * u) (a * x) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [mode] <;> ring

def alpha (n v : ℝ) : ℝ := n ^ 2 + v ^ 2
def damping (m n v : ℝ) : ℝ := ((n + v) ^ 2 + m ^ 2) / 2
def couplingUp (m v κ : ℝ) : ℝ := m * v + 2 * κ
def couplingDown (m n κ : ℝ) : ℝ := m * n + 2 * κ

theorem actual_mode_eigen (m n v κ u x γ : ℝ)
    (hu : -alpha n v * u + couplingUp m v κ * x = -γ * u)
    (hx : -couplingDown m n κ * u - damping m n v * x = -γ * x) :
    gkslAction (hamiltonian κ) (jumps m n v) (mode u x) =
      ((-γ : ℝ) : ℂ) • mode u x := by
  rw [actual_mode_action, mode_smul]
  exact congrArg₂ mode hu hx

/-- 本征模的系数直接由真实二维块的迹与行列式确定。 -/
theorem spectral_coordinates (α ℓ r c f s : ℝ) (hgap : f - s ≠ 0)
    (htrace : f + s = α + ℓ) (hdet : f * s = α * ℓ + r * c) :
    (-α * ((α - s) / (f - s)) + r * (c / (f - s)) =
      -f * ((α - s) / (f - s))) ∧
    (-c * ((α - s) / (f - s)) - ℓ * (c / (f - s)) = -f * (c / (f - s))) ∧
    (-α * ((f - α) / (f - s)) + r * (-c / (f - s)) =
      -s * ((f - α) / (f - s))) ∧
    (-c * ((f - α) / (f - s)) - ℓ * (-c / (f - s)) = -s * (-c / (f - s))) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp
  · linear_combination α * htrace - hdet
  · linear_combination c * htrace
  · linear_combination -α * htrace + hdet
  · linear_combination -c * htrace

def fastMode (α c f s : ℝ) : QubitMatrix := mode ((α - s) / (f - s)) (c / (f - s))
def slowMode (α c f s : ℝ) : QubitMatrix := mode ((f - α) / (f - s)) (-c / (f - s))

theorem modes_sum (α c f s : ℝ) (hgap : f - s ≠ 0) :
    fastMode α c f s + slowMode α c f s = mode 1 0 := by
  rw [fastMode, slowMode, mode_add]
  congr 1 <;> field_simp <;> ring

theorem modes_eigen (m n v κ f s : ℝ) (hgap : f - s ≠ 0)
    (htrace : f + s = alpha n v + damping m n v)
    (hdet : f * s = alpha n v * damping m n v + couplingUp m v κ * couplingDown m n κ) :
    gkslAction (hamiltonian κ) (jumps m n v)
      (fastMode (alpha n v) (couplingDown m n κ) f s) =
        ((-f : ℝ) : ℂ) • fastMode (alpha n v) (couplingDown m n κ) f s ∧
    gkslAction (hamiltonian κ) (jumps m n v)
      (slowMode (alpha n v) (couplingDown m n κ) f s) =
        ((-s : ℝ) : ℂ) • slowMode (alpha n v) (couplingDown m n κ) f s := by
  obtain ⟨h1, h2, h3, h4⟩ := spectral_coordinates (alpha n v) (damping m n v)
    (couplingUp m v κ) (couplingDown m n κ) f s hgap htrace hdet
  exact ⟨actual_mode_eigen m n v κ _ _ f h1 h2,
    actual_mode_eigen m n v κ _ _ s h3 h4⟩

/-- 真实 GKSL 指数作用于人口扰动的精确两个本征模。 -/
theorem actual_mode_evolution (m n v κ f s t : ℝ) (hgap : f - s ≠ 0)
    (htrace : f + s = alpha n v + damping m n v)
    (hdet : f * s = alpha n v * damping m n v + couplingUp m v κ * couplingDown m n κ) :
    gkslSuperoperatorEvolution (hamiltonian κ) (jumps m n v) t (mode 1 0) =
      (Real.exp (-f * t) : ℂ) • fastMode (alpha n v) (couplingDown m n κ) f s +
      (Real.exp (-s * t) : ℂ) • slowMode (alpha n v) (couplingDown m n κ) f s := by
  obtain ⟨hf, hs⟩ := modes_eigen m n v κ f s hgap htrace hdet
  have hef := ResetFamily.evolution_eigen (hamiltonian κ) (jumps m n v) t _ _ hf
  have hes := ResetFamily.evolution_eigen (hamiltonian κ) (jumps m n v) t _ _ hs
  rw [← modes_sum (alpha n v) (couplingDown m n κ) f s hgap, map_add, hef, hes]
  congr 2 <;> rw [Complex.ofReal_exp] <;> congr 1 <;> push_cast <;> ring

/-- 两个实验输入在对角稳态与人口扰动方向上的精确分解。 -/
theorem input_decomposition (ν : ℝ) :
    (Matrix.single 0 0 1 : QubitMatrix) = diagonalState ν + ((1 - ν : ℝ) : ℂ) • mode 1 0 ∧
    (Matrix.single 1 1 1 : QubitMatrix) = diagonalState ν + ((-ν : ℝ) : ℂ) • mode 1 0 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [diagonalState, mode, Matrix.single_apply] <;> ring

def response (α f s t : ℝ) : ℝ :=
  (α - s) / (f - s) * Real.exp (-f * t) + (f - α) / (f - s) * Real.exp (-s * t)

/-- 与人口响应同步的真实实相干响应。 -/
def coherenceResponse (c f s t : ℝ) : ℝ :=
  c / (f - s) * Real.exp (-f * t) + (-c) / (f - s) * Real.exp (-s * t)

theorem actual_response_evolution (m n v κ f s t : ℝ) (hgap : f - s ≠ 0)
    (htrace : f + s = alpha n v + damping m n v)
    (hdet : f * s = alpha n v * damping m n v + couplingUp m v κ * couplingDown m n κ) :
    gkslSuperoperatorEvolution (hamiltonian κ) (jumps m n v) t (mode 1 0) =
      mode (response (alpha n v) f s t) (coherenceResponse (couplingDown m n κ) f s t) := by
  rw [actual_mode_evolution m n v κ f s t hgap htrace hdet]
  simp only [fastMode, slowMode, mode_smul, mode_add]
  congr 1 <;> dsimp [response, coherenceResponse] <;> ring

/-- 直接读出原模型的两项概率；实际 ε 精确为 ν(1-q)。 -/
theorem actual_finiteOutput (m n v κ ν f s t : ℝ)
    (hpop : v ^ 2 * (1 - ν) = n ^ 2 * ν)
    (hcoh : κ * (1 - 2 * ν) = m * n * ν + m * v / 2)
    (hgap : f - s ≠ 0)
    (htrace : f + s = alpha n v + damping m n v)
    (hdet : f * s = alpha n v * damping m n v + couplingUp m v κ * couplingDown m n κ) :
    finiteOutput (hamiltonian κ) (jumps m n v) t =
      (ν + (1 - ν) * response (alpha n v) f s t,
       1 - ν * (1 - response (alpha n v) f s t)) := by
  have hs := actual_stationary m n v κ ν hpop hcoh
  have hstation : gkslAction (hamiltonian κ) (jumps m n v) (diagonalState ν) =
      (0 : ℂ) • diagonalState ν := by simpa using hs
  have he := ResetFamily.evolution_eigen (hamiltonian κ) (jumps m n v) t _ 0 hstation
  simp only [mul_zero, Complex.exp_zero, one_smul] at he
  obtain ⟨h0, h1⟩ := input_decomposition ν
  rw [finiteOutput_eq_superoperator_probabilities, h0, h1]
  simp only [map_add, map_smul, he, actual_response_evolution m n v κ f s t hgap htrace hdet]
  simp only [mode_smul]
  ext <;> simp [mode, diagonalState] <;> dsimp [response] <;> ring

/-- 实际增益等于响应的负值，未替换实际读出误差。 -/
theorem actual_gain_identity (m n v κ ν f s t : ℝ)
    (hpop : v ^ 2 * (1 - ν) = n ^ 2 * ν)
    (hcoh : κ * (1 - 2 * ν) = m * n * ν + m * v / 2)
    (hgap : f - s ≠ 0)
    (htrace : f + s = alpha n v + damping m n v)
    (hdet : f * s = alpha n v * damping m n v + couplingUp m v κ * couplingDown m n κ) :
    1 - (finiteOutput (hamiltonian κ) (jumps m n v) t).2 =
      ν * (1 - response (alpha n v) f s t) ∧
    1 - (finiteOutput (hamiltonian κ) (jumps m n v) t).2 -
      (finiteOutput (hamiltonian κ) (jumps m n v) t).1 =
        -response (alpha n v) f s t := by
  rw [actual_finiteOutput m n v κ ν f s t hpop hcoh hgap htrace hdet]
  constructor <;> dsimp <;> ring

/-- 正文的系数 d 将双指数写成 (1+d)e^(-ft)-d e^(-st)。 -/
theorem response_two_modes (α f s t : ℝ) (hgap : f - s ≠ 0) :
    response α f s t =
      (1 + (α - f) / (f - s)) * Real.exp (-f * t) -
      ((α - f) / (f - s)) * Real.exp (-s * t) := by
  unfold response
  field_simp
  ring

/-- 由判别式得到真实二维块的两个衰减率。 -/
def gap (α ℓ r c : ℝ) : ℝ := Real.sqrt ((α - ℓ) ^ 2 - 4 * r * c)
def fastRate (α ℓ r c : ℝ) : ℝ := (α + ℓ + gap α ℓ r c) / 2
def slowRate (α ℓ r c : ℝ) : ℝ := (α + ℓ - gap α ℓ r c) / 2

theorem rates_trace_det (α ℓ r c : ℝ) (hdisc : 0 ≤ (α - ℓ) ^ 2 - 4 * r * c) :
    fastRate α ℓ r c + slowRate α ℓ r c = α + ℓ ∧
    fastRate α ℓ r c * slowRate α ℓ r c = α * ℓ + r * c ∧
    fastRate α ℓ r c - slowRate α ℓ r c = gap α ℓ r c := by
  have hsq : gap α ℓ r c ^ 2 = (α - ℓ) ^ 2 - 4 * r * c := Real.sq_sqrt hdisc
  dsimp [fastRate, slowRate]
  constructor
  · ring
  constructor
  · nlinarith
  · ring

/-- χ 参数下负反馈系数的精确化简。 -/
theorem family_coefficients (m n χ : ℝ) (hχ : χ ≠ 1) :
    alpha n (χ * n) = n ^ 2 * (1 + χ ^ 2) ∧
    damping m n (χ * n) = (n ^ 2 * (1 + χ) ^ 2 + m ^ 2) / 2 ∧
    couplingUp m (χ * n) (kappa m n χ) = 2 * m * n * χ / (1 - χ) ∧
    couplingDown m n (kappa m n χ) = m * n * (1 + χ ^ 2) / (1 - χ) := by
  have he : 1 - χ ≠ 0 := sub_ne_zero.mpr (Ne.symm hχ)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp [alpha, damping, couplingUp, couplingDown, kappa]
  · ring
  · ring
  · field_simp; ring
  · field_simp; ring

/-- 正文使用的 ν 参数及平方根振幅。 -/
def chi (ν : ℝ) : ℝ := Real.sqrt (ν / (1 - ν))
def paperJump (ν A B : ℝ) : QubitMatrix :=
  jump (Real.sqrt B) (Real.sqrt A) (Real.sqrt (ν * A / (1 - ν)))
def paperJumps (ν A B : ℝ) : Fin 1 → QubitMatrix := fun _ => paperJump ν A B
def paperKappa (ν A B : ℝ) : ℝ :=
  Real.sqrt (A * B) * (ν + chi ν / 2) / (1 - 2 * ν)
def paperHamiltonian (ν A B : ℝ) : QubitMatrix := hamiltonian (paperKappa ν A B)

theorem chi_parameters (ν : ℝ) (hν : 0 < ν) (hνh : ν < 1 / 2) :
    0 < chi ν ∧ chi ν < 1 ∧ occupation (chi ν) = ν := by
  have hp : 0 < 1 - ν := by linarith
  have hs : chi ν ^ 2 = ν / (1 - ν) := Real.sq_sqrt (le_of_lt (div_pos hν hp))
  have hr : chi ν ^ 2 * (1 - ν) = ν := (eq_div_iff (ne_of_gt hp)).mp hs
  have hc : 0 < chi ν := Real.sqrt_pos.2 (div_pos hν hp)
  have hc1 : chi ν < 1 := by
    have hh : ν / (1 - ν) < 1 := (div_lt_one hp).2 (by linarith)
    nlinarith
  refine ⟨hc, hc1, ?_⟩
  unfold occupation
  apply (div_eq_iff (by positivity : (1 : ℝ) + chi ν ^ 2 ≠ 0)).2
  nlinarith

theorem paper_amplitude (ν A : ℝ) (hν : 0 < ν) (hνh : ν < 1 / 2) :
    Real.sqrt (ν * A / (1 - ν)) = chi ν * Real.sqrt A := by
  have hp : 0 ≤ ν / (1 - ν) := le_of_lt (div_pos hν (by linarith))
  rw [show ν * A / (1 - ν) = (ν / (1 - ν)) * A by ring, Real.sqrt_mul hp]
  rfl

theorem paper_parameters (ν A B : ℝ) (hν : 0 < ν) (hνh : ν < 1 / 2)
    (hA : 0 ≤ A) :
    paperJumps ν A B = jumps (Real.sqrt B) (Real.sqrt A) (chi ν * Real.sqrt A) ∧
    paperHamiltonian ν A B =
      hamiltonian (kappa (Real.sqrt B) (Real.sqrt A) (chi ν)) := by
  have hc := chi_parameters ν hν hνh
  constructor
  · funext μ
    simp [paperJumps, paperJump, jumps, paper_amplitude ν A hν hνh]
  · unfold paperHamiltonian
    congr 1
    have he : 1 - 2 * ν ≠ 0 := by linarith
    have hk := (parameter_stationarity (Real.sqrt B) (Real.sqrt A) (chi ν)
      (ne_of_lt hc.2.1)).2
    rw [hc.2.2] at hk
    unfold paperKappa
    rw [Real.sqrt_mul hA]
    apply (div_eq_iff he).2
    nlinarith

/-- 原文单跳和 Hamiltonian 具有所声称的对角稳态。 -/
theorem paper_stationary (ν A B : ℝ) (hν : 0 < ν) (hνh : ν < 1 / 2)
    (hA : 0 ≤ A) :
    gkslAction (paperHamiltonian ν A B) (paperJumps ν A B) (diagonalState ν) = 0 := by
  obtain ⟨hj, hh⟩ := paper_parameters ν A B hν hνh hA
  obtain ⟨_, hc, ho⟩ := chi_parameters ν hν hνh
  rw [hj, hh]
  simpa only [ho] using family_stationary (Real.sqrt B) (Real.sqrt A) (chi ν) (ne_of_lt hc)

theorem paper_hermitian (ν A B : ℝ) : (paperHamiltonian ν A B).IsHermitian :=
  hamiltonian_hermitian _

/-- 正文参数产生真实有限 GKSL 输出，不需要任何额外可实现性假设。 -/
theorem paper_output_mem_finite (ν A B t : ℝ) (ht : 0 ≤ t) :
    finiteOutput (paperHamiltonian ν A B) (paperJumps ν A B) t ∈ finiteOutputs :=
  ⟨1, paperHamiltonian ν A B, paperJumps ν A B, t, paper_hermitian ν A B, ht, rfl⟩

/-- 双指数响应确实满足真实负反馈方程及人口初始条件。 -/
theorem response_realODE (α ℓ r c f s t : ℝ) (hgap : f - s ≠ 0)
    (htrace : f + s = α + ℓ) (hdet : f * s = α * ℓ + r * c) :
    HasDerivAt (response α f s)
      (-α * response α f s t + r * coherenceResponse c f s t) t ∧
    HasDerivAt (coherenceResponse c f s)
      (-c * response α f s t - ℓ * coherenceResponse c f s t) t ∧
    response α f s 0 = 1 ∧ coherenceResponse c f s 0 = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := spectral_coordinates α ℓ r c f s hgap htrace hdet
  have hef := ((hasDerivAt_id t).const_mul (-f)).exp
  have hes := ((hasDerivAt_id t).const_mul (-s)).exp
  have hq := (hef.const_mul ((α - s) / (f - s))).add
    (hes.const_mul ((f - α) / (f - s)))
  have hz := (hef.const_mul (c / (f - s))).add
    (hes.const_mul (-c / (f - s)))
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert hq using 1
    · rfl
    dsimp [response, coherenceResponse]
    linear_combination Real.exp (-f * t) * h1 + Real.exp (-s * t) * h3
  · convert hz using 1
    · rfl
    dsimp [response, coherenceResponse]
    linear_combination Real.exp (-f * t) * h2 + Real.exp (-s * t) * h4
  · simp [response]
    field_simp <;> ring
  · simp [coherenceResponse]
    ring

/-- 本族真实指数演化在原实子空间中的 ODE 及初值。 -/
theorem actual_realODE (m n v κ f s t : ℝ) (hgap : f - s ≠ 0)
    (htrace : f + s = alpha n v + damping m n v)
    (hdet : f * s = alpha n v * damping m n v + couplingUp m v κ * couplingDown m n κ) :
    gkslSuperoperatorEvolution (hamiltonian κ) (jumps m n v) t (mode 1 0) =
      mode (response (alpha n v) f s t) (coherenceResponse (couplingDown m n κ) f s t) ∧
    HasDerivAt (response (alpha n v) f s)
      (-alpha n v * response (alpha n v) f s t +
        couplingUp m v κ * coherenceResponse (couplingDown m n κ) f s t) t ∧
    HasDerivAt (coherenceResponse (couplingDown m n κ) f s)
      (-couplingDown m n κ * response (alpha n v) f s t -
        damping m n v * coherenceResponse (couplingDown m n κ) f s t) t ∧
    response (alpha n v) f s 0 = 1 ∧ coherenceResponse (couplingDown m n κ) f s 0 = 0 :=
  ⟨actual_response_evolution m n v κ f s t hgap htrace hdet,
    response_realODE (alpha n v) (damping m n v) (couplingUp m v κ)
      (couplingDown m n κ) f s t hgap htrace hdet⟩

/-- 总体速率为一的形状参数；总体速率可吸收到有限演化时间。 -/
def shapeAlpha (χ : ℝ) : ℝ := 1 + χ ^ 2
def shapeDamping (χ τ : ℝ) : ℝ := ((1 + χ) ^ 2 + τ) / 2
def shapeProduct (χ τ : ℝ) : ℝ := 2 * χ * τ * (1 + χ ^ 2) / (1 - χ) ^ 2
def shapeDiscriminant (χ τ : ℝ) : ℝ :=
  (shapeAlpha χ - shapeDamping χ τ) ^ 2 - 4 * shapeProduct χ τ
def shapeGap (χ τ : ℝ) : ℝ := Real.sqrt (shapeDiscriminant χ τ)
def shapeFast (χ τ : ℝ) : ℝ := (shapeAlpha χ + shapeDamping χ τ + shapeGap χ τ) / 2
def shapeSlow (χ τ : ℝ) : ℝ := (shapeAlpha χ + shapeDamping χ τ - shapeGap χ τ) / 2
def shapeD (χ τ : ℝ) : ℝ := (shapeAlpha χ - shapeFast χ τ) / shapeGap χ τ
def shapeBeta (χ τ : ℝ) : ℝ := shapeSlow χ τ / shapeFast χ τ

theorem shape_actual_coefficients (χ τ : ℝ) (hχ : χ ≠ 1) (hτ : 0 ≤ τ) :
    alpha 1 χ = shapeAlpha χ ∧
    damping (Real.sqrt τ) 1 χ = shapeDamping χ τ ∧
    couplingUp (Real.sqrt τ) χ (kappa (Real.sqrt τ) 1 χ) *
      couplingDown (Real.sqrt τ) 1 (kappa (Real.sqrt τ) 1 χ) = shapeProduct χ τ := by
  have hs := Real.sq_sqrt hτ
  have hc := family_coefficients (Real.sqrt τ) 1 χ hχ
  simp only [mul_one, one_pow, one_mul] at hc
  refine ⟨by simp [alpha, shapeAlpha], by simpa [damping, shapeDamping, hs], ?_⟩
  rw [hc.2.2.1, hc.2.2.2]
  dsimp [shapeProduct]
  have he : 1 - χ ≠ 0 := sub_ne_zero.mpr (Ne.symm hχ)
  field_simp
  nlinarith [hs]

theorem shape_spectrum (χ τ : ℝ) (hdisc : 0 < shapeDiscriminant χ τ) :
    shapeFast χ τ - shapeSlow χ τ = shapeGap χ τ ∧
    0 < shapeGap χ τ ∧
    shapeFast χ τ + shapeSlow χ τ = shapeAlpha χ + shapeDamping χ τ ∧
    shapeFast χ τ * shapeSlow χ τ =
      shapeAlpha χ * shapeDamping χ τ + shapeProduct χ τ := by
  have hs : shapeGap χ τ ^ 2 = shapeDiscriminant χ τ := Real.sq_sqrt hdisc.le
  have hp : 0 < shapeGap χ τ := Real.sqrt_pos.2 hdisc
  refine ⟨?_, hp, ?_, ?_⟩ <;> dsimp [shapeFast, shapeSlow]
  · ring
  · ring
  · dsimp [shapeDiscriminant] at hs
    nlinarith

/-- 形状参数给出的双指数就是原单跳族的实际有限输出。 -/
theorem shape_finiteOutput (χ τ t : ℝ) (hχ : χ ≠ 1) (hτ : 0 ≤ τ)
    (hdisc : 0 < shapeDiscriminant χ τ) :
    finiteOutput (hamiltonian (kappa (Real.sqrt τ) 1 χ)) (jumps (Real.sqrt τ) 1 χ) t =
      (occupation χ + (1 - occupation χ) *
        ((1 + shapeD χ τ) * Real.exp (-shapeFast χ τ * t) -
          shapeD χ τ * Real.exp (-shapeSlow χ τ * t)),
       1 - occupation χ * (1 -
        ((1 + shapeD χ τ) * Real.exp (-shapeFast χ τ * t) -
          shapeD χ τ * Real.exp (-shapeSlow χ τ * t)))) := by
  obtain ⟨ha, hl, hp⟩ := shape_actual_coefficients χ τ hχ hτ
  obtain ⟨hg, hgp, ht, hd⟩ := shape_spectrum χ τ hdisc
  have hgap : shapeFast χ τ - shapeSlow χ τ ≠ 0 := by rw [hg]; exact ne_of_gt hgp
  have hstat := parameter_stationarity (Real.sqrt τ) 1 χ hχ
  simp only [mul_one] at hstat
  have hout := actual_finiteOutput (Real.sqrt τ) 1 χ (kappa (Real.sqrt τ) 1 χ)
    (occupation χ) (shapeFast χ τ) (shapeSlow χ τ) t hstat.1 (by simpa using hstat.2) hgap
    (by simpa only [ha, hl] using ht) (by simpa only [ha, hl, hp] using hd)
  rw [ha, response_two_modes _ _ _ _ hgap, hg] at hout
  exact hout

/-- 判别式为正时，负指数系数可改写为不相消的公式。 -/
theorem shapeD_stable (χ τ : ℝ) (hg : shapeGap χ τ ≠ 0)
    (he : shapeAlpha χ - shapeDamping χ τ + shapeGap χ τ ≠ 0)
    (hdisc : 0 ≤ shapeDiscriminant χ τ) :
    shapeD χ τ = 2 * shapeProduct χ τ /
      (shapeGap χ τ * (shapeAlpha χ - shapeDamping χ τ + shapeGap χ τ)) := by
  have hs : shapeGap χ τ ^ 2 = shapeDiscriminant χ τ := Real.sq_sqrt hdisc
  dsimp [shapeD, shapeFast]
  field_simp
  dsimp [shapeDiscriminant] at hs
  nlinarith

/-- 稳定相对系数，避免在 d 的两个接近根之间相减。 -/
def dFactor (χ τ : ℝ) : ℝ :=
  4 * shapeAlpha χ / ((1 - χ) ^ 2 * shapeGap χ τ *
    (shapeAlpha χ - shapeDamping χ τ + shapeGap χ τ))

theorem shapeD_factor (χ τ : ℝ) (hχ : χ ≠ 1)
    (hg : shapeGap χ τ ≠ 0)
    (he : shapeAlpha χ - shapeDamping χ τ + shapeGap χ τ ≠ 0)
    (hdisc : 0 ≤ shapeDiscriminant χ τ) :
    shapeD χ τ = χ * τ * dFactor χ τ := by
  rw [shapeD_stable χ τ hg he hdisc]
  dsimp [shapeProduct, dFactor, shapeAlpha]
  field_simp
  ring

/-- 实际谱的全部零阶极限，由显式公式连续性推出。 -/
theorem shape_limits {ι : Type*} {l : Filter ι} (χ τ : ι → ℝ)
    (hχ : Tendsto χ l (𝓝 0)) (hτ : Tendsto τ l (𝓝 0)) :
    Tendsto (fun i => shapeAlpha (χ i)) l (𝓝 1) ∧
    Tendsto (fun i => shapeDamping (χ i) (τ i)) l (𝓝 (1 / 2)) ∧
    Tendsto (fun i => shapeProduct (χ i) (τ i)) l (𝓝 0) ∧
    Tendsto (fun i => shapeDiscriminant (χ i) (τ i)) l (𝓝 (1 / 4)) ∧
    Tendsto (fun i => shapeGap (χ i) (τ i)) l (𝓝 (1 / 2)) ∧
    Tendsto (fun i => shapeFast (χ i) (τ i)) l (𝓝 1) ∧
    Tendsto (fun i => shapeSlow (χ i) (τ i)) l (𝓝 (1 / 2)) ∧
    Tendsto (fun i => shapeD (χ i) (τ i)) l (𝓝 0) ∧
    Tendsto (fun i => shapeBeta (χ i) (τ i)) l (𝓝 (1 / 2)) ∧
    Tendsto (fun i => dFactor (χ i) (τ i)) l (𝓝 8) := by
  have ha : Tendsto (fun i => shapeAlpha (χ i)) l (𝓝 1) := by
    simpa [shapeAlpha] using ((tendsto_const_nhds (x := (1 : ℝ))).add (hχ.pow 2))
  have hl : Tendsto (fun i => shapeDamping (χ i) (τ i)) l (𝓝 (1 / 2)) := by
    convert ((((tendsto_const_nhds (x := (1 : ℝ))).add hχ).pow 2).add hτ).div_const 2 using 1 <;> norm_num [shapeDamping]
  have hp : Tendsto (fun i => shapeProduct (χ i) (τ i)) l (𝓝 0) := by
    convert ((((tendsto_const_nhds (x := (2 : ℝ))).mul hχ).mul hτ).mul ha).div
      (((tendsto_const_nhds (x := (1 : ℝ))).sub hχ).pow 2) (by norm_num) using 1 <;> norm_num [shapeProduct, shapeAlpha] <;> rfl
  have hd : Tendsto (fun i => shapeDiscriminant (χ i) (τ i)) l (𝓝 (1 / 4)) := by
    convert ((ha.sub hl).pow 2).sub ((tendsto_const_nhds (x := (4 : ℝ))).mul hp) using 1 <;> norm_num [shapeDiscriminant]
  have hg : Tendsto (fun i => shapeGap (χ i) (τ i)) l (𝓝 (1 / 2)) := by
    convert hd.sqrt using 1 <;> norm_num [shapeGap]
  have hf : Tendsto (fun i => shapeFast (χ i) (τ i)) l (𝓝 1) := by
    convert ((ha.add hl).add hg).div_const 2 using 1 <;> norm_num [shapeFast]
  have hs : Tendsto (fun i => shapeSlow (χ i) (τ i)) l (𝓝 (1 / 2)) := by
    convert ((ha.add hl).sub hg).div_const 2 using 1 <;> norm_num [shapeSlow]
  have hcoef : Tendsto (fun i => shapeD (χ i) (τ i)) l (𝓝 0) := by
    convert (ha.sub hf).div hg (by norm_num) using 1 <;> norm_num [shapeD] <;> rfl
  have hb : Tendsto (fun i => shapeBeta (χ i) (τ i)) l (𝓝 (1 / 2)) := by
    convert hs.div hf (by norm_num) using 1 <;> norm_num [shapeBeta] <;> rfl
  have hfac : Tendsto (fun i => dFactor (χ i) (τ i)) l (𝓝 8) := by
    convert ((tendsto_const_nhds (x := (4 : ℝ))).mul ha).div
      (((((tendsto_const_nhds (x := (1 : ℝ))).sub hχ).pow 2).mul hg).mul ((ha.sub hl).add hg))
      (by norm_num) using 1 <;> norm_num [dFactor] <;> rfl
  exact ⟨ha, hl, hp, hd, hg, hf, hs, hcoef, hb, hfac⟩

/-- 本征指数偏移的稳定恒等式，是 τ log(1/ν)=2 窗口中 e⁻² 因子的来源。 -/
theorem exponent_shift_identity (χ τ : ℝ)
    (hτ : τ ≠ 0) (hg : shapeGap χ τ ≠ 0)
    (he : shapeAlpha χ - shapeDamping χ τ + shapeGap χ τ ≠ 0)
    (hdisc : 0 ≤ shapeDiscriminant χ τ) :
    (shapeFast χ τ / shapeGap χ τ - 2) / τ =
      (1 + 2 * (χ / τ) + 6 * shapeProduct χ τ /
        (τ * (shapeAlpha χ - shapeDamping χ τ + shapeGap χ τ))) / shapeGap χ τ := by
  have hs : shapeGap χ τ ^ 2 = shapeDiscriminant χ τ := Real.sq_sqrt hdisc
  dsimp [shapeFast]
  field_simp
  dsimp [shapeDiscriminant, shapeAlpha, shapeDamping] at hs ⊢
  nlinarith

def curveNu (L : ℝ) : ℝ := Real.exp (-L)
def curveChi (L : ℝ) : ℝ := chi (curveNu L)
def curveTau (L : ℝ) : ℝ := 2 / L

theorem curveNu_limit : Tendsto curveNu atTop (𝓝 0) := by
  change Tendsto (fun L : ℝ => Real.exp (-L)) atTop (𝓝 0)
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 1 (by norm_num)
  simpa only [Real.rpow_zero, one_mul, mul_one, neg_one_mul] using h

theorem curveTau_limit : Tendsto curveTau atTop (𝓝 0) :=
  tendsto_id.const_div_atTop 2

theorem curveChi_limit : Tendsto curveChi atTop (𝓝 0) := by
  change Tendsto (fun L => Real.sqrt (curveNu L / (1 - curveNu L))) atTop (𝓝 0)
  have h := (curveNu_limit.div
    ((tendsto_const_nhds (x := (1 : ℝ))).sub curveNu_limit) (by norm_num)).sqrt
  simpa only [Pi.div_apply, sub_zero, zero_div, Real.sqrt_zero] using h

theorem curveNu_pos (L : ℝ) : 0 < curveNu L := Real.exp_pos _

theorem curve_parameters_eventually : ∀ᶠ L : ℝ in atTop,
    0 < curveNu L ∧ curveNu L < 1 / 2 ∧ 0 < curveChi L ∧
      curveChi L < 1 ∧ occupation (curveChi L) = curveNu L ∧ 0 < curveTau L := by
  filter_upwards [curveNu_limit.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    eventually_gt_atTop (0 : ℝ)] with L hν hL
  have hc := chi_parameters (curveNu L) (curveNu_pos L) hν
  exact ⟨curveNu_pos L, hν, hc.1, hc.2.1, hc.2.2, div_pos (by norm_num) hL⟩

theorem curveTau_log_exact (L : ℝ) : curveTau L = 2 / Real.log (1 / curveNu L) := by
  simp [curveTau, curveNu, Real.log_inv]

theorem curveChi_radius (L : ℝ) (hL : 0 < L) :
    curveChi L = Real.exp (-L / 2) / Real.sqrt (1 - curveNu L) := by
  have hν : curveNu L < 1 := by simpa [curveNu] using Real.exp_lt_one_iff.mpr (by linarith : -L < 0)
  have hp : 0 ≤ 1 - curveNu L := by linarith
  unfold curveChi chi
  rw [Real.sqrt_div (curveNu_pos L).le]
  congr 1
  unfold curveNu
  exact (Real.exp_half (-L)).symm

theorem curveChi_mul_L_limit : Tendsto (fun L => curveChi L * L) atTop (𝓝 0) := by
  have hnum : Tendsto (fun L : ℝ => Real.exp (-L / 2) * L) atTop (𝓝 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1 / 2) (by norm_num)
    simpa [neg_div, div_eq_mul_inv, mul_comm] using h
  have hden : Tendsto (fun L => Real.sqrt (1 - curveNu L)) atTop (𝓝 1) := by
    simpa using (((tendsto_const_nhds (x := (1 : ℝ))).sub curveNu_limit).sqrt)
  have hh : Tendsto (fun L => Real.exp (-L / 2) * L / Real.sqrt (1 - curveNu L)) atTop (𝓝 0) := by
    convert hnum.div hden (by norm_num) using 1 <;> norm_num <;> rfl
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  rw [curveChi_radius L hL]
  ring

theorem curveChi_div_tau_limit : Tendsto (fun L => curveChi L / curveTau L) atTop (𝓝 0) := by
  have hh : Tendsto (fun L => curveChi L * L / 2) atTop (𝓝 0) := by
    simpa only [zero_div] using curveChi_mul_L_limit.div_const 2
  apply hh.congr'
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with L hL
  dsimp [curveTau]
  field_simp

/-- 真实族在全部充分大 L 上具有正实谱、正最优负系数。 -/
theorem curve_spectral_tail : ∀ᶠ L : ℝ in atTop,
    0 < shapeDiscriminant (curveChi L) (curveTau L) ∧
    0 < shapeSlow (curveChi L) (curveTau L) ∧
    shapeSlow (curveChi L) (curveTau L) < shapeFast (curveChi L) (curveTau L) ∧
    0 < shapeD (curveChi L) (curveTau L) ∧
    0 < shapeBeta (curveChi L) (curveTau L) ∧ shapeBeta (curveChi L) (curveTau L) < 1 ∧
    0 < dFactor (curveChi L) (curveTau L) ∧
    0 < shapeAlpha (curveChi L) - shapeDamping (curveChi L) (curveTau L) +
      shapeGap (curveChi L) (curveTau L) := by
  obtain ⟨ha, hl, hp, hd, hg, hf, hs, hc, hb, hfac⟩ :=
    shape_limits curveChi curveTau curveChi_limit curveTau_limit
  have he : Tendsto (fun L => shapeAlpha (curveChi L) - shapeDamping (curveChi L) (curveTau L) +
      shapeGap (curveChi L) (curveTau L)) atTop (𝓝 1) := by
    convert (ha.sub hl).add hg using 1 <;> norm_num
  filter_upwards [curve_parameters_eventually,
    hd.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
    hs.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    hfac.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 8)),
    he.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))]
    with L hpar hdisc hslow hdf he
  obtain ⟨hgap, hgp, htrace, hdet⟩ := shape_spectrum (curveChi L) (curveTau L) hdisc
  have hsf : shapeSlow (curveChi L) (curveTau L) < shapeFast (curveChi L) (curveTau L) := by linarith
  have hfast : 0 < shapeFast (curveChi L) (curveTau L) := lt_trans hslow hsf
  have hdpos : 0 < shapeD (curveChi L) (curveTau L) := by
    rw [shapeD_factor _ _ (ne_of_lt hpar.2.2.2.1) (ne_of_gt hgp) (ne_of_gt he) hdisc.le]
    exact mul_pos (mul_pos hpar.2.2.1 hpar.2.2.2.2.2) hdf
  exact ⟨hdisc, hslow, hsf, hdpos, div_pos hslow hfast, (div_lt_one hfast).2 hsf, hdf, he⟩

theorem curve_exponent_shift_limit :
    Tendsto (fun L => (shapeFast (curveChi L) (curveTau L) /
      shapeGap (curveChi L) (curveTau L) - 2) / curveTau L) atTop (𝓝 2) := by
  obtain ⟨ha, hl, hp, hd, hg, hf, hs, hc, hb, hfac⟩ :=
    shape_limits curveChi curveTau curveChi_limit curveTau_limit
  have he : Tendsto (fun L => shapeAlpha (curveChi L) - shapeDamping (curveChi L) (curveTau L) +
      shapeGap (curveChi L) (curveTau L)) atTop (𝓝 1) := by
    convert (ha.sub hl).add hg using 1 <;> norm_num
  have hk : Tendsto (fun L => shapeProduct (curveChi L) (curveTau L) /
      (curveTau L * (shapeAlpha (curveChi L) - shapeDamping (curveChi L) (curveTau L) +
        shapeGap (curveChi L) (curveTau L)))) atTop (𝓝 0) := by
    have hbase : Tendsto (fun L => 2 * curveChi L * shapeAlpha (curveChi L) /
        ((1 - curveChi L) ^ 2 * (shapeAlpha (curveChi L) - shapeDamping (curveChi L) (curveTau L) +
          shapeGap (curveChi L) (curveTau L)))) atTop (𝓝 0) := by
      convert (((tendsto_const_nhds (x := (2 : ℝ))).mul curveChi_limit).mul ha).div
        ((((tendsto_const_nhds (x := (1 : ℝ))).sub curveChi_limit).pow 2).mul he)
        (by norm_num) using 1 <;> norm_num <;> rfl
    apply hbase.congr'
    filter_upwards [curve_parameters_eventually, curve_spectral_tail] with L hpar hsp
    have ht := ne_of_gt hpar.2.2.2.2.2
    have hc : 1 - curveChi L ≠ 0 := by linarith [hpar.2.2.2.1]
    have he' := ne_of_gt hsp.2.2.2.2.2.2.2
    dsimp [shapeProduct, shapeAlpha]
    field_simp <;> ring
  have hlim : Tendsto (fun L => (1 + 2 * (curveChi L / curveTau L) +
      6 * (shapeProduct (curveChi L) (curveTau L) /
        (curveTau L * (shapeAlpha (curveChi L) - shapeDamping (curveChi L) (curveTau L) +
          shapeGap (curveChi L) (curveTau L))))) / shapeGap (curveChi L) (curveTau L)) atTop (𝓝 2) := by
    convert (((tendsto_const_nhds (x := (1 : ℝ))).add
      ((tendsto_const_nhds (x := (2 : ℝ))).mul curveChi_div_tau_limit)).add
        ((tendsto_const_nhds (x := (6 : ℝ))).mul hk)).div hg (by norm_num)
      using 1 <;> norm_num <;> rfl
  apply hlim.congr'
  filter_upwards [curve_parameters_eventually, curve_spectral_tail] with L hpar hsp
  have hg0 : shapeGap (curveChi L) (curveTau L) ≠ 0 :=
    ne_of_gt (shape_spectrum _ _ hsp.1).2.1
  simpa only [mul_div_assoc] using (exponent_shift_identity _ _ (ne_of_gt hpar.2.2.2.2.2) hg0
    (ne_of_gt hsp.2.2.2.2.2.2.2) hsp.1.le).symm

theorem curve_log_d_limit : Tendsto (fun L =>
    Real.log (shapeD (curveChi L) (curveTau L)) / L) atTop (𝓝 (-1 / 2)) := by
  obtain ⟨ha, hl, hp, hd, hg, hf, hs, hc, hb, hfac⟩ :=
    shape_limits curveChi curveTau curveChi_limit curveTau_limit
  have hlogOne : Tendsto (fun L => Real.log (1 - curveNu L)) atTop (𝓝 0) := by
    have hOne : Tendsto (fun L => 1 - curveNu L) atTop (𝓝 1) := by
      simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub curveNu_limit
    have h := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hOne
    simpa only [sub_zero, Real.log_one, Function.comp_def] using h
  have hlogχ : Tendsto (fun L => Real.log (curveChi L) / L) atTop (𝓝 (-1 / 2)) := by
    have hbase : Tendsto (fun L => -1 / 2 - (Real.log (1 - curveNu L) / L) / 2)
        atTop (𝓝 (-1 / 2)) := by
      simpa only [zero_div, sub_zero, id_eq] using ((hlogOne.div_atTop tendsto_id).div_const 2).const_sub (-1 / 2)
    apply hbase.congr'
    filter_upwards [curve_parameters_eventually, eventually_gt_atTop (0 : ℝ)] with L hpar hL
    have hv : 0 < 1 - curveNu L := by linarith [hpar.2.1]
    dsimp [curveChi, chi]
    rw [Real.log_sqrt (div_nonneg hpar.1.le hv.le), Real.log_div hpar.1.ne' hv.ne']
    simp only [curveNu, Real.log_exp]
    field_simp <;> ring
  have hlogL : Tendsto (fun L : ℝ => Real.log L / L) atTop (𝓝 0) := by
    simpa only [id_eq, Pi.div_apply] using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hlogτ : Tendsto (fun L => Real.log (curveTau L) / L) atTop (𝓝 0) := by
    have hbase : Tendsto (fun L : ℝ => Real.log 2 / L - Real.log L / L) atTop (𝓝 0) := by
      simpa only [sub_zero, id_eq] using ((tendsto_const_nhds (x := Real.log 2)).div_atTop tendsto_id).sub hlogL
    apply hbase.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    rw [curveTau, Real.log_div (by norm_num) (ne_of_gt hL)]
    ring
  have hlogfac : Tendsto (fun L => Real.log (dFactor (curveChi L) (curveTau L)) / L)
      atTop (𝓝 0) := by
    have h := (Real.continuousAt_log (by norm_num : (8 : ℝ) ≠ 0)).tendsto.comp hfac
    simpa only [Function.comp_apply, id_eq] using h.div_atTop tendsto_id
  have hbase : Tendsto (fun L => Real.log (curveChi L) / L + Real.log (curveTau L) / L +
      Real.log (dFactor (curveChi L) (curveTau L)) / L) atTop (𝓝 (-1 / 2)) := by
    simpa only [add_zero] using (hlogχ.add hlogτ).add hlogfac
  apply hbase.congr'
  filter_upwards [curve_parameters_eventually, curve_spectral_tail] with L hpar hsp
  have hgp := (shape_spectrum _ _ hsp.1).2.1
  rw [shapeD_factor _ _ (ne_of_lt hpar.2.2.2.1) (ne_of_gt hgp)
    (ne_of_gt hsp.2.2.2.2.2.2.2) hsp.1.le]
  rw [Real.log_mul (mul_ne_zero hpar.2.2.1.ne' hpar.2.2.2.2.2.ne') hsp.2.2.2.2.2.2.1.ne',
    Real.log_mul hpar.2.2.1.ne' hpar.2.2.2.2.2.ne']
  ring

/-- 最优增益中的额外实幂趋于 e⁻²。 -/
theorem curve_power_correction_limit : Tendsto (fun L =>
    Real.exp ((shapeFast (curveChi L) (curveTau L) /
      shapeGap (curveChi L) (curveTau L) - 2) *
        Real.log (shapeD (curveChi L) (curveTau L)))) atTop (𝓝 (Real.exp (-2))) := by
  have hshift : Tendsto (fun L => (shapeFast (curveChi L) (curveTau L) /
      shapeGap (curveChi L) (curveTau L) - 2) * L) atTop (𝓝 4) := by
    have hbase : Tendsto (fun L => ((shapeFast (curveChi L) (curveTau L) /
        shapeGap (curveChi L) (curveTau L) - 2) / curveTau L) * 2) atTop (𝓝 4) := by
      convert curve_exponent_shift_limit.mul_const 2 using 1 <;> norm_num
    apply hbase.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    dsimp [curveTau]
    field_simp
  have hbase : Tendsto (fun L => ((shapeFast (curveChi L) (curveTau L) /
      shapeGap (curveChi L) (curveTau L) - 2) * L) *
        (Real.log (shapeD (curveChi L) (curveTau L)) / L)) atTop (𝓝 (-2)) := by
    convert hshift.mul curve_log_d_limit using 1 <;> norm_num
  have hlim : Tendsto (fun L => (shapeFast (curveChi L) (curveTau L) /
      shapeGap (curveChi L) (curveTau L) - 2) *
        Real.log (shapeD (curveChi L) (curveTau L))) atTop (𝓝 (-2)) := by
    apply hbase.congr'
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with L hL
    field_simp
  exact Real.continuous_exp.continuousAt.tendsto.comp hlim

#print axioms actual_finiteOutput
#print axioms paper_stationary
#print axioms actual_realODE
#print axioms shape_finiteOutput
#print axioms curve_spectral_tail
#print axioms curve_exponent_shift_limit
#print axioms curve_log_d_limit
#print axioms curve_power_correction_limit
end TwoStateQuantumEmbedding.ResetDiagonalFamily



