import Mathlib

namespace MathlibPlus.Algebra

/--
Claim 10617.  The source's four signed layer multiplicities are recorded as
an explicit four-coordinate vector; the displayed amplitude factorization is
proved over an arbitrary commutative ring.  The source gives no formal
construction connecting the layers to the polynomial, so the polynomial
identity is stated exactly as displayed rather than adding one.
-/
theorem fourLayerShadowAmplitude (R : Type*) [CommRing R] (q : R) :
    let c : Fin 4 → ℤ := ![1, 2, -2, -1]
    let P : R → R := fun q => 1 + 2 * q - 2 * q ^ 2 - q ^ 3
    (∀ j : Fin 4, c ((3 : Fin 4) - j) = -c j) ∧
      P q = (1 - q) * (q ^ 2 + 3 * q + 1) := by
  dsimp
  constructor
  · intro j
    fin_cases j <;> decide
  · ring

end MathlibPlus.Algebra
