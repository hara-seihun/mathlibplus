import Mathlib

namespace MathlibPlus.Algebra.RootedFactorHomogeneity

/-- Claim 50636: the displayed rooted-factor term has the common weight of the
whole row. The weight is stated over `ℚ` to retain the source's rational
coefficient setting while keeping truncated natural subtraction explicit. -/
theorem rootedFactorTermWeight_claim50636
    (M d k q h : ℕ) (_hk : 2 ≤ k) (hkM : k ≤ M) :
    ((M - k : ℕ) : ℚ) *
          (((d - 1 : ℕ) : ℚ) + (q : ℚ) * (h : ℚ)) +
        (q : ℚ) * (k : ℚ) * (h : ℚ) +
          (k : ℚ) * ((d - 1 : ℕ) : ℚ) =
      (M : ℚ) * (((d - 1 : ℕ) : ℚ) + (q : ℚ) * (h : ℚ)) := by
  rw [Nat.cast_sub hkM]
  ring

end MathlibPlus.Algebra.RootedFactorHomogeneity
