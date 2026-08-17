import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.NumberTheory.Claim51904

noncomputable section

/-- The valuation sum used by the admitted code function. -/
def valuationSum (q : ℕ) : ℕ :=
  ∑ r ∈ Finset.range q, 2 ^ padicValNat 2 (r + 1)

/-- The integer-parameter code function `H_A(q) = A q - 2 V(q)`. -/
def highBitCode (A : ℤ) (q : ℕ) : ℤ :=
  A * (q : ℤ) - 2 * (valuationSum q : ℤ)

/-- Claim 51904: complement reflection and its exact high-bit renormalization. -/
def complementReflectionAndRenormalization : Prop :=
  ∀ (A : ℤ) (s r : ℕ),
    1 ≤ s →
    0 ≤ r →
    r < 2 ^ s →
    highBitCode A (2 ^ s - 1 - r) =
        (A - (s : ℤ)) * (2 : ℤ) ^ s - A - highBitCode A r ∧
      ∀ (k q : ℕ),
        q = 2 ^ s - 1 - r →
        s ≤ k →
        highBitCode A q = (2 : ℤ) ^ k - A →
        highBitCode A r =
          (2 : ℤ) ^ s *
            (A - (s : ℤ) - (2 : ℤ) ^ (k - s))

end

end MathlibPlus.Open.NumberTheory.Claim51904
