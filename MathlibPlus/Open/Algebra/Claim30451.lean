import Mathlib

namespace MathlibPlus.Open.Algebra.Claim30451

noncomputable section

open Polynomial

/-- The quartic `f_d(t) = t^4 - t^3 + d t - 1` used in the norm record. -/
def quartic (d : ℤ) : Polynomial ℚ :=
  X ^ 4 - X ^ 3 + C (d : ℚ) * X - 1

/-- Claim 30451: for a root of the displayed quartic generating the number
field `K = ℚ(t)`, the three field norms have the stated values. -/
def claim30451_normIdentities : Prop :=
  ∀ (d : ℤ), 2 ≤ d →
    ∀ (K : Type*) [Field K] [NumberField K],
      ∀ (t : K),
        Algebra.adjoin ℚ ({t} : Set K) = ⊤ →
        aeval t (quartic d) = 0 →
        Algebra.norm ℚ t = (-1 : ℚ) ∧
          Algebra.norm ℚ (t - 1) = (d - 1 : ℚ) ∧
          Algebra.norm ℚ (t ^ 2 - t + 1) = ((d - 1 : ℚ) ^ 2)

end

end MathlibPlus.Open.Algebra.Claim30451
