import Mathlib

namespace MathlibPlus.Algebra.Claim38342

/-- Exact two-factor discriminant identity from the displayed substitutions. -/
theorem twoFactorDiscriminantIdentity {R : Type*} [CommRing R]
    (A B C D : R) :
    let E := A - B
    let W := C - D
    let S := A + B
    let c := A + B - C - D
    let k := A * B - C * D
    (W - E) * (W + E) = -2 * c * S + c ^ 2 + 4 * k := by
  dsimp
  ring

end MathlibPlus.Algebra.Claim38342
