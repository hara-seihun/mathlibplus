import Mathlib

namespace MathlibPlus.Algebra.TriangularTransport

/-- The inverse formula in the normalized triangular transporter of claim 59214.
The source uses a prime field; the calculation is valid over every commutative ring. -/
theorem triangularShear_inverse
    {R : Type*} [CommRing R]
    (f : R → R) (g : R → R → R)
    (_hf0 : f 0 = 0) (_hg0 : g 0 0 = 0) :
    let q : (R × R × R) → (R × R × R) :=
      fun ⟨x, y, z⟩ => (x, y + f x, z + g x y)
    let qInv : (R × R × R) → (R × R × R) :=
      fun ⟨x, y, z⟩ => (x, y - f x, z - g x (y - f x))
    (Function.LeftInverse qInv q ∧ Function.RightInverse qInv q) := by
  dsimp
  constructor
  · intro x
    rcases x with ⟨x, y, z⟩
    ext <;> dsimp <;> simp
  · intro x
    rcases x with ⟨x, y, z⟩
    ext <;> dsimp <;> simp

/-- The coupled relative-transport calculation in claim 59215. -/
theorem relativeTransportFormula
    {R : Type*} [CommRing R]
    (f : R → R) (g : R → R → R)
    (_hf0 : f 0 = 0) (_hg0 : g 0 0 = 0)
    (r s₀ t a b c : R) :
    let δ : R := f (r + a) - f r - f a
    let q : (R × R × R) → (R × R × R) :=
      fun ⟨x, y, z⟩ => (x, y + f x, z + g x y)
    let qInv : (R × R × R) → (R × R × R) :=
      fun ⟨x, y, z⟩ => (x, y - f x, z - g x (y - f x))
    qInv (q ((r, s₀, t) + (a, b, c)) - q (r, s₀, t)) =
      (a, b + δ,
        c + g (r + a) (s₀ + b) - g r s₀ - g a (b + δ)) := by
  dsimp
  ext <;> dsimp <;> simp
  · ring
  · have harg :
        s₀ + b + f (r + a) - (s₀ + f r) - f a =
          b + (f (r + a) - f r - f a) := by
      ring
    rw [harg]
    ring

end MathlibPlus.Algebra.TriangularTransport
