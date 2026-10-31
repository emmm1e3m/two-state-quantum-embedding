import TwoStateQuantumEmbedding.ResetCore
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

noncomputable section
open Matrix

namespace TwoStateQuantumEmbedding.ResetEnvelope

abbrev M2 := Matrix (Fin 2) (Fin 2) ℝ

def chi (ν : ℝ) : ℝ := Real.sqrt (ν / (1 - ν))
def tiltV (p : ℝ) : ℝ := 1 - 2 * p
def tiltW (p : ℝ) : ℝ := 2 * Real.sqrt (p * (1 - p))
def alpha (ν A : ℝ) : ℝ := A * (1 + chi ν ^ 2)
def lambda (ν A B : ℝ) : ℝ := (A * (1 - chi ν) ^ 2 + B) / 2
def down (ν A B : ℝ) : ℝ := Real.sqrt (A * B) * (1 + chi ν ^ 2) / (1 - chi ν)
def up (ν A B : ℝ) : ℝ := 2 * chi ν * Real.sqrt (A * B) / (1 - chi ν)
def comparisonMatrix (ν A B : ℝ) : M2 :=
  !![-alpha ν A, up ν A B; down ν A B, -lambda ν A B]
def quadratic (p : ℝ) (T : M2) : ℝ :=
  dotProduct ![tiltV p, tiltW p] (T *ᵥ ![tiltV p, tiltW p])
def envelope (p ν A B : ℝ) : ℝ :=
  max (quadratic p (NormedSpace.exp (comparisonMatrix ν A B)) -
    2 * tiltV p ^ 2 * Real.exp (-alpha ν A)) 0

def rateA (x : ℝ) : ℝ := 1 + x ^ 2
def rateL (x τ : ℝ) : ℝ := ((1 - x) ^ 2 + τ) / 2
def rateC (x τ : ℝ) : ℝ := Real.sqrt τ * (1 + x ^ 2) / (1 - x)
def rateR (x τ : ℝ) : ℝ := 2 * x * Real.sqrt τ / (1 - x)
def coupling (x τ : ℝ) : ℝ := rateR x τ * rateC x τ
def gap (x τ : ℝ) : ℝ := rateA x - rateL x τ
def discriminant (x τ : ℝ) : ℝ :=
  Real.sqrt (gap x τ ^ 2 + 4 * coupling x τ)
def beta (x τ : ℝ) : ℝ := (rateA x + rateL x τ - discriminant x τ) / 2
def gamma (x τ : ℝ) : ℝ := (rateA x + rateL x τ + discriminant x τ) / 2
def slowWeight (p x τ : ℝ) : ℝ :=
  ((gamma x τ - rateA x) * tiltV p ^ 2 +
    (gamma x τ - rateL x τ) * tiltW p ^ 2 +
    (rateR x τ + rateC x τ) * (tiltV p * tiltW p)) / discriminant x τ


end TwoStateQuantumEmbedding.ResetEnvelope
