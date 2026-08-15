import Mathlib

noncomputable section
open MeasureTheory
open scoped BigOperators Interval

namespace MathlibPlus.Open.ResearchBatch.C0143

def alpha (j : Fin 52) : ℝ := 2 * (j : ℝ) + 1 / 2

def cutoffKappa (c : ℕ) : ℝ := 2 * Real.pi / Real.log c

def finiteDirichletSum (c : ℕ) (q : ℂ) : ℂ :=
  ∑ n ∈ (Finset.range c).filter (fun n => 1 ≤ n),
    (1 / Real.sqrt (n : ℝ) : ℂ) *
      Complex.exp (-q * (Real.log (n : ℝ) : ℂ))

def rationalResolvent (a : Fin 52 → ℚ) (q : ℂ) : ℂ :=
  ∑ j : Fin 52, (a j : ℂ) / (alpha j + q)

def endpointResolvent (c : ℕ) (a : Fin 52 → ℚ) (q : ℂ) : ℂ :=
  ∑ j : Fin 52,
    (a j : ℂ) *
      (Real.rpow (c : ℝ) (-((2 * (j : ℕ) : ℝ) + 1 / 2)) : ℂ) *
      (∑ n ∈ (Finset.range c).filter (fun n => 1 ≤ n),
        (n : ℂ) ^ (2 * (j : ℕ))) /
      ((alpha j : ℂ) + q)

def prolateError (c : ℕ) (a : Fin 52 → ℚ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * Real.pi * z) *
      finiteDirichletSum c (Complex.I * cutoffKappa c * z) *
      rationalResolvent a (Complex.I * cutoffKappa c * z) -
    Complex.exp (-Complex.I * Real.pi * z) *
      endpointResolvent c a (Complex.I * cutoffKappa c * z)

def prolateEvenPart (c : ℕ) (a : Fin 52 → ℚ) (z : ℂ) : ℂ :=
  (prolateError c a z + prolateError c a (-z)) / 2

def exactCutoffProlateTransform_claim2256 : Prop :=
  ∀ c : ℕ, 2 ≤ c → ∀ a : Fin 52 → ℚ,
    Differentiable ℂ (prolateEvenPart c a) ∧
    ∀ z : ℂ, prolateEvenPart c a (-z) = prolateEvenPart c a z

end MathlibPlus.Open.ResearchBatch.C0143
