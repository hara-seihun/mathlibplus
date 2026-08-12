import Mathlib

namespace MathlibPlus.Algebra.Claim8007

/-- The reciprocal factorial convention used by claim 8007: negative
arguments contribute zero. -/
def reciprocalFactorial (n : ℤ) : ℚ :=
  if h : 0 ≤ n then 1 / (Nat.factorial n.toNat : ℚ) else 0

def reciprocalFactorialMatrix (M k : ℕ) : Matrix (Fin k) (Fin k) ℚ :=
  fun i j =>
    reciprocalFactorial ((M : ℤ) - 1 - (i.val : ℤ) - (j.val : ℤ))

end MathlibPlus.Algebra.Claim8007

namespace MathlibPlus.Open.Algebra.Claim8007

/-- The reciprocal-factorial determinant identity and its nonvanishing
consequence, with the source's positive integer parameters represented by
natural numbers and its negative-factorial convention made explicit. -/
def reciprocalFactorialDeterminant_claim8007 : Prop :=
  ∀ (M k : ℕ), 1 ≤ M → 1 ≤ k → k ≤ M →
    let D := Matrix.det (MathlibPlus.Algebra.Claim8007.reciprocalFactorialMatrix M k)
    D =
        ((-1 : ℚ) ^ (k * (k - 1) / 2)) *
          (Finset.range k).prod (fun j =>
            (Nat.factorial j : ℚ) /
              (Nat.factorial (M - 1 - j) : ℚ)) ∧
      D ≠ 0

end MathlibPlus.Open.Algebra.Claim8007
