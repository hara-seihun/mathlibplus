import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.NumberTheory

/-- Registry statement for admitted claim 17541.  The displayed formula for
`κ_m(P)` is inlined: `P` is a finite nonempty set of primes and the inner
index ranges over positive integers, exactly as in the source formula. -/
def claim17541_oddScatteringCumulantPositivity : Prop :=
  ∀ (P : Finset ℕ),
    (∀ p ∈ P, Nat.Prime p) →
    P.Nonempty →
    ∀ m : ℕ, Odd m →
      0 < ∑' p : {p // p ∈ P},
        ∑' r : ℕ+,
          (r : ℝ) ^ (m - 1) *
              (Real.log (p.1 : ℝ)) ^ m *
            Real.rpow (p.1 : ℝ) (-((r : ℝ) / 2))

end MathlibPlus.Open.NumberTheory
