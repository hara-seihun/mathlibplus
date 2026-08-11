import Mathlib

namespace MathlibPlus.Open.Algebra

/-!
# Affine determinant marker degree

Statement-fidelity registry node for admitted claim 18950.  The determinant is
formed over `Polynomial R` so the marker variable is explicit; the
epsilon-independent factor is represented by an arbitrary scalar.
-/

/-- The determinant of an affine `m` by `m` matrix has marker degree at most
`m`, and multiplication by a marker-independent scalar does not increase that
bound. -/
def affineDeterminantCoreBoundedDegree : Prop :=
  ∀ {R : Type*} [CommRing R] (m : ℕ)
    (C : Matrix (Fin m) (Fin m) R),
    let Cₚ : Matrix (Fin m) (Fin m) (Polynomial R) :=
      fun i j => Polynomial.C (C i j)
    let q : Polynomial R := Matrix.det
      ((1 : Matrix (Fin m) (Fin m) (Polynomial R)) +
        (Polynomial.X : Polynomial R) • Cₚ)
    q.natDegree ≤ m ∧
      (∀ ε : R, Polynomial.eval ε q =
        Matrix.det
          ((1 : Matrix (Fin m) (Fin m) R) + ε • C)) ∧
      (∀ a : R, (Polynomial.C a * q).natDegree ≤ m)

end MathlibPlus.Open.Algebra
