import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace MathlibPlus.NumberTheory.Claim8247

open scoped BigOperators

/-- The generalized-Jordan coefficient from admitted claim 8247.

For the claim's domain (`q` prime, `0 ≤ t ≤ 1`, `n ≥ 1`), this is the
finite product over prime divisors of `n` other than `q`; the empty product
is one. -/
noncomputable def generalizedJordanCoefficient_claim8247
    (q : ℕ) (t : ℝ) (n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors.filter (fun p => p ≠ q),
    (1 - Real.rpow (p : ℝ) (-t))

end MathlibPlus.NumberTheory.Claim8247
