import Mathlib

noncomputable section

open scoped BigOperators
open Filter MeasureTheory

namespace MathlibPlus.Open.ResearchFormalization.O0098Claim11428

/-- The primes at the endpoint cutoff, with the exact natural index used by
`Q_y`. -/
def endpointPrimeSet (y : ℕ) : Finset ℕ :=
  Finset.filter Nat.Prime (Finset.Icc 2 y)

/-- The primorial `Q_y = ∏_{p≤y} p`. -/
def endpointPrimorial (y : ℕ) : ℕ :=
  ∏ p ∈ endpointPrimeSet y, p

/-- The prime mass `L_y = Σ_{p≤y} p^(-1/2)`. -/
def endpointPrimeMass (y : ℕ) : ℝ :=
  ∑' p : {p : ℕ // Nat.Prime p},
    if p.1 ≤ y then Real.rpow (p.1 : ℝ) (-1 / 2) else 0

/-- The periodic Beurling basis term used in the primorial Nyman carrier. -/
def endpointBasis (α x : ℝ) : ℝ :=
  Int.fract (α / x) - α * Int.fract (1 / x)

/-- The exact primorial divisor packet `v_y`. -/
def endpointNymanV (y : ℕ) (x : ℝ) : ℝ :=
  -∑ d ∈ Nat.divisors (endpointPrimorial y),
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      endpointBasis (1 / (d : ℝ)) x

/-- The exact Nyman defect `g_y = 1-v_y`. -/
def endpointNymanG (y : ℕ) (x : ℝ) : ℝ :=
  1 - endpointNymanV y x

/-- The squared L2 carrier of the exact endpoint defect on `(0,1)`. -/
def endpointNormSq (y : ℕ) : ℝ :=
  ∫ x in Set.Ioo (0 : ℝ) 1, (endpointNymanG y x) ^ 2

/-- Claim 11428: the logarithmic squared-norm and prime-mass asymptotics,
with the stated divergence of the endpoint norm. -/
def claim11428 : Prop :=
  Asymptotics.IsEquivalent Filter.atTop
      (fun y : ℕ => Real.log (endpointNormSq y))
      (fun y : ℕ => 2 * endpointPrimeMass y) ∧
    Asymptotics.IsEquivalent Filter.atTop
      (fun y : ℕ => 2 * endpointPrimeMass y)
      (fun y : ℕ =>
        4 * Real.sqrt (y : ℝ) / Real.log (y : ℝ)) ∧
    Filter.Tendsto
      (fun y : ℕ => Real.sqrt (endpointNormSq y))
      Filter.atTop Filter.atTop

end MathlibPlus.Open.ResearchFormalization.O0098Claim11428
