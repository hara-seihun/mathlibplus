import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

/-- The primes in the cutoff prefix `y`. -/
def primeCutoff (y : ℕ) : Finset ℕ :=
  (Finset.range (y + 1)).filter Nat.Prime

/-- The primorial attached to the cutoff prefix `y`. -/
def primorialCutoff (y : ℕ) : ℕ :=
  ∏ p ∈ primeCutoff y, p

/-- The independent-phase Bohr-torus energy from Claim 7710. -/
noncomputable def bohrTorusEnergy (y : ℕ) (c : ℝ) : ℝ :=
  ∏ p ∈ primeCutoff y, (1 + Real.rpow (p : ℝ) (2 * c - 4))

/-- The finite-cutoff trace kernel used by the exact trace-energy formula. -/
noncomputable def traceKernel (y : ℕ) (x : ℝ) : ℝ :=
  ∑ d ∈ Nat.divisors (primorialCutoff y),
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      Real.rpow (d : ℝ) (-2) * Real.exp (-(x / (d : ℝ)))

/-- The cutoff trace energy, as the weighted square integral in the repair context. -/
noncomputable def traceEnergy (y : ℕ) (c : ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ),
    |traceKernel y x| ^ 2 * Real.rpow x (2 * c - 1)

/-- Bohr-torus energy does not dominate the prime-log orbit. -/
def bohrTorusEnergy_doesNotDominate_primeLogOrbit : Prop :=
  (∀ c : ℝ, c < (3 / 2 : ℝ) →
      BddAbove (Set.range (fun y : ℕ => bohrTorusEnergy y c))) ∧
    (∀ c : ℝ, 1 < c → c < (3 / 2 : ℝ) →
      Filter.Tendsto (fun y : ℕ => traceEnergy y c) Filter.atTop Filter.atTop) ∧
    (∀ c : ℝ, 1 < c → c < (3 / 2 : ℝ) →
      ¬ ∃ C_c : ℝ, ∀ y : ℕ,
        traceEnergy y c ≤ C_c * bohrTorusEnergy y c)

end MathlibPlus.Open.Analysis
