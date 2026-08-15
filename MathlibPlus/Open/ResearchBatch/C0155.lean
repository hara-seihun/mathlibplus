import Mathlib

noncomputable section
open MeasureTheory
open scoped BigOperators Interval

namespace MathlibPlus.Open.ResearchBatch.C0155

def balancedProfileH (x : ℝ) : ℝ :=
  x^2 * (2 * Real.pi * x^2 - 3) * Real.exp (-Real.pi * x^2)

def balancedProfileWeight (lambda theta x : ℝ) : ℝ :=
  (1 - x^2 / lambda^2) ^ (2 * Int.toNat (Int.floor (Real.log lambda)) + 2) *
    Real.exp (-theta * x^2 / lambda^2)

def balancedProfileSource_claim2434 (lambda theta x : ℝ) : ℝ :=
  if |x| ≤ lambda then balancedProfileWeight lambda theta x * balancedProfileH x else 0

def balancedProfileSource (lambda theta x : ℝ) : ℝ :=
  balancedProfileSource_claim2434 lambda theta x

def exactZeroMassAndCenter_claim2437 : Prop :=
  ∀ lambda theta : ℝ, 1 < lambda →
    (∫ x in (-lambda)..lambda,
      balancedProfileWeight lambda theta x * balancedProfileH x) = 0 →
    (∀ theta' : ℝ,
      (∫ x in (-lambda)..lambda,
        balancedProfileWeight lambda theta' x * balancedProfileH x) = 0 →
      theta' = theta) →
    (∫ x : ℝ, balancedProfileSource lambda theta x) = 0 ∧
      balancedProfileSource lambda theta 0 = 0

end MathlibPlus.Open.ResearchBatch.C0155
