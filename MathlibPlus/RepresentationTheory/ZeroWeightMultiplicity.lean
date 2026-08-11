import Mathlib

/-!
# Zero-weight multiplicities

The local count uses the monomial model for `Symᵏ(ℂ³)`: a zero-weight
monomial has exponent triple `(a, k - 2 * a, a)`, hence `2 * a ≤ k`.
-/

namespace MathlibPlus.RepresentationTheory

/-- The zero-weight monomials in the `k`-th symmetric power of the spin-one
three-dimensional representation are counted by `⌊k / 2⌋ + 1`. -/
theorem zeroWeightMultiplicity (k : ℕ) :
    ((Finset.range (k + 1)).filter (fun a => 2 * a ≤ k)).card = k / 2 + 1 := by
  have hfilter :
      (Finset.range (k + 1)).filter (fun a => 2 * a ≤ k) =
        Finset.range (k / 2 + 1) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hfilter, Finset.card_range]

end MathlibPlus.RepresentationTheory
