import Mathlib

namespace MathlibPlus.Combinatorics.R0554

/-- Claim 26188: the exact degree-indicator binomial inversion identity over
integers. -/
def degreeIndicatorBinomialInversion_claim26188 : Prop :=
  ∀ (n d k : ℕ),
    0 ≤ d → d ≤ n - 1 → 0 ≤ k → k ≤ n - 1 →
      (if k = d then (1 : ℤ) else 0) =
        ∑ s ∈ Finset.Icc d (n - 1),
          (-1 : ℤ) ^ (s - d) * (Nat.choose s d : ℤ) *
            (Nat.choose k s : ℤ)

end MathlibPlus.Combinatorics.R0554
