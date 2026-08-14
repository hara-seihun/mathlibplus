import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization

/-- The product of the linear factors indexed by an arity `m` family. -/
def equalArityProduct {R : Type*} [CommRing R] (m : ℕ) (a : Fin m → R) : Polynomial R :=
  ∏ i : Fin m, (Polynomial.X + Polynomial.C (a i))

/-- The complete product of the pairwise cross differences of two families. -/
def crossDifferenceProduct {R : Type*} [CommRing R] (m : ℕ)
    (a b : Fin m → R) : R :=
  ∏ i : Fin m, ∏ j : Fin m, (a i - b j)

/-- Claim 25144: the equal-arity products have the stated degree gate and
Gauss content split. -/
def equalArityContentSplit (R : Type*) [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] [NormalizedGCDMonoid R] (m : ℕ)
    (a b : Fin m → R) : Prop :=
  let F := equalArityProduct m a
  let G := equalArityProduct m b
  F.Monic ∧ G.Monic ∧ F.natDegree = m ∧ G.natDegree = m ∧
    (F - G).degree ≤ ((m - 1 : ℕ) : WithBot ℕ) ∧
    ∃ Q : Polynomial R,
      F - G = Polynomial.C (Polynomial.content (F - G)) * Q ∧
        Q.IsPrimitive

/-- Claim 25148: prime content divisors occur in cross differences, with the
stated multiplicity bound expressed by divisibility in the UFD. -/
def contentPrimeCrossSupport (R : Type*) [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] [NormalizedGCDMonoid R] (m : ℕ)
    (a b : Fin m → R) : Prop :=
  let F := equalArityProduct m a
  let G := equalArityProduct m b
  let h := Polynomial.content (F - G)
  (∀ p : R, Prime p → p ∣ h →
      ∃ i : Fin m, ∃ j : Fin m, p ∣ a i - b j) ∧
    (∀ p : R, ∀ k : ℕ, Prime p → p ^ k ∣ h →
      p ^ (m * k) ∣ crossDifferenceProduct m a b)

end MathlibPlus.Open.ResearchFormalization
