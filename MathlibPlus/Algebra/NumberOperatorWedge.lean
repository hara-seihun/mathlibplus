import Mathlib

/-!
# Coefficient identity for the number-operator wedge

This file formalizes the coefficient-level algebra behind the claim that
`|h⟩ ∧ N|h⟩` has coefficient `(b - a) h_a h_b` in the ordered basis wedge
`|a⟩ ∧ |b⟩`.  The informal claim does not specify a topological completion for
its infinite formal sum, so this theorem records the well-defined coefficient
identity rather than asserting convergence or equality of completed vectors.
-/

namespace MathlibPlus.Algebra.NumberOperatorWedge

/-- The coefficient of `|a⟩ ∧ |b⟩` in `|h⟩ ∧ N|h⟩`, for `a < b`, is
`(b - a) h_a h_b`. -/
theorem coefficientIdentity
    {R : Type*} [CommRing R] (h : ℕ → R) {a b : ℕ} (hab : a < b) :
    h a * ((b : R) * h b) - h b * ((a : R) * h a) =
      ((b - a : ℕ) : R) * h a * h b := by
  rw [Nat.cast_sub (Nat.le_of_lt hab)]
  ring

end MathlibPlus.Algebra.NumberOperatorWedge
