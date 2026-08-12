import Mathlib

namespace MathlibPlus.Algebra.Claim34990

/-- The two displayed `P₃` rooting messages, with the source-specific rooted
factor carrier left at the fidelity boundary. -/
theorem rooting_messages_claim34990 {R : Type*} [CommRing R] (a q : R) :
    let pA : R := 2 * a * q - a + q ^ 3 - 2 * q ^ 2 + q
    let pB : R := q * (2 * a + q ^ 2 - 2 * q)
    let nuA : R := 2 * a * q - a + q ^ 3 - 3 * q ^ 2 + q
    let nuB : R := 2 * a * q - a + q ^ 3 - 3 * q ^ 2 + q
    pA = 2 * a * q - a + q ^ 3 - 2 * q ^ 2 + q ∧
      pB = q * (2 * a + q ^ 2 - 2 * q) ∧
      nuA = nuB ∧
      nuA = 2 * a * q - a + q ^ 3 - 3 * q ^ 2 + q := by
  simp

end MathlibPlus.Algebra.Claim34990
