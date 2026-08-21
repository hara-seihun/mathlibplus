-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is a root of the Unverified library rather than of MathlibPlus and no build here depends on it. See unverified.txt.
import Mathlib

namespace MathlibPlus.Algebra.FiniteFieldElliptic

open Polynomial

/-- Claim 11598: the two short-Weierstrass control curves over `𝔽₅`; the
point count includes the point at infinity and the Frobenius polynomial is
`X² - aX + 5`, with `a = 6 - #E` in `ℤ`. -/
theorem controlCurves_claim11598 :
    let F := ZMod 5
    let AffinePoints : F → F → Type := fun a b =>
      {p : F × F // p.2 ^ 2 = p.1 ^ 3 + a * p.1 + b}
    let pointCount : F → F → ℕ := fun a b =>
      Fintype.card (AffinePoints a b) + 1
    let trace : F → F → ℤ := fun a b =>
      5 + 1 - (pointCount a b : ℤ)
    let frobeniusPolynomial : F → F → Polynomial ℤ := fun a b =>
      X ^ 2 - C (trace a b) * X + C 5
    (4 * (1 : F) ^ 3 + 27 * (1 : F) ^ 2) ≠ 0 ∧
      (4 * (2 : F) ^ 3 + 27 * (0 : F) ^ 2) ≠ 0 ∧
      pointCount 1 1 = 9 ∧
      pointCount 2 0 = 2 ∧
      frobeniusPolynomial 1 1 = X ^ 2 + C 3 * X + C 5 ∧
      frobeniusPolynomial 2 0 = X ^ 2 - C 4 * X + C 5 := by
  dsimp
  have h1 : Fintype.card
      ({p : ZMod 5 × ZMod 5 // p.2 ^ 2 = p.1 ^ 3 + p.1 + 1}) = 8 := by
    native_decide
  have h2 : Fintype.card
      ({p : ZMod 5 × ZMod 5 // p.2 ^ 2 = p.1 ^ 3 + 2 * p.1}) = 1 := by
    native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · simp [h1]
  constructor
  · simp [h2]
  constructor
  · simp [h1]
  · simp [h2]

end MathlibPlus.Algebra.FiniteFieldElliptic
