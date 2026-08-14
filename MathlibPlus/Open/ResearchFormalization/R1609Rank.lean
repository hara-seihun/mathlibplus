import Mathlib

namespace MathlibPlus.Open

/-- The rank of an integer matrix after scalar extension to `ℚ`. -/
noncomputable def rationalRank {m n : Nat} (A : Matrix (Fin m) (Fin n) ℤ) : Nat :=
  Matrix.rank (A.map (Int.castRingHom ℚ))

/-- The rank of an integer matrix after reduction modulo `p`. -/
noncomputable def modularRank {m n : Nat} (p : Nat)
    (A : Matrix (Fin m) (Fin n) ℤ) : Nat :=
  Matrix.rank (A.map (Int.castRingHom (ZMod p)))

/-- Column nullity expressed using the finite-dimensional matrix rank. -/
noncomputable def rationalNullity {m n : Nat} (A : Matrix (Fin m) (Fin n) ℤ) : Nat :=
  n - rationalRank A

noncomputable def modularNullity {m n : Nat} (p : Nat)
    (A : Matrix (Fin m) (Fin n) ℤ) : Nat :=
  n - modularRank p A

/--
Claim 39581.  For an integer matrix and a prime `p`, reduction modulo `p`
cannot increase rank; with a fixed number of columns this is equivalently the
opposite inequality for rational and modular nullities.
-/
def characteristicZeroRankBound : Prop :=
  ∀ (m n p : Nat) (hp : Nat.Prime p)
    (A : Matrix (Fin m) (Fin n) ℤ),
    modularRank p A ≤ rationalRank A ∧
      (rationalNullity A ≤ modularNullity p A ↔ modularRank p A ≤ rationalRank A)

end MathlibPlus.Open
