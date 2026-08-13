import Mathlib

namespace MathlibPlus.Algebra

/-- Claim 9854: after applying the Leibniz rule, a common factor contributes
exactly its square to the unreduced Wronskian.  The derivation interface keeps
this algebraic cancellation independent of a particular analytic model. -/
theorem claim9854_unreducedWronskian_factor {R : Type*} [CommRing R]
    (d S B : R) (D : R → R)
    (hD : ∀ x y : R, D (x * y) = D x * y + x * D y) :
    (d * S) * D (d * B) - D (d * S) * (d * B) =
      d ^ 2 * (S * D B - D S * B) := by
  rw [hD, hD]
  ring

end MathlibPlus.Algebra
