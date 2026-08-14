import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2.R0834

/-- Claim 25170: a nontrivial rational cross-ratio equation among free
monomials forces a triple collision. -/
def claim25170 : Prop :=
  ∀ (σ : Type) [DecidableEq σ]
    (u v x y : σ →₀ ℤ) (lam : ℚ),
    lam ≠ 0 → lam ≠ 1 →
    let A : AddMonoidAlgebra ℚ (σ →₀ ℤ) := AddMonoidAlgebra.single u 1
    let B : AddMonoidAlgebra ℚ (σ →₀ ℤ) := AddMonoidAlgebra.single v 1
    let C : AddMonoidAlgebra ℚ (σ →₀ ℤ) := AddMonoidAlgebra.single x 1
    let D : AddMonoidAlgebra ℚ (σ →₀ ℤ) := AddMonoidAlgebra.single y 1
    (A - D) * (B - C) = (algebraMap ℚ _ lam) * ((A - C) * (B - D)) →
      (u = v ∧ u = x) ∨ (u = v ∧ u = y) ∨ (u = x ∧ u = y) ∨
        (v = x ∧ v = y)

/-- Claim 25172: two equality pairs cannot realize a nontrivial constant
cross-ratio; the three pairings are all covered explicitly. -/
def claim25172 : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R]
    (A B C D : R) (lam : R), lam ≠ 0 → lam ≠ 1 →
    ((A = B ∧ C = D ∧ A ≠ C) ∨
      (A = C ∧ B = D ∧ A ≠ B) ∨
      (A = D ∧ B = C ∧ A ≠ B)) →
    (A - D) * (B - C) ≠ lam * ((A - C) * (B - D))

/-- Claim 25175: the four normalized linear irreducibles in Q[x] exhibit the
nontrivial constant cross-ratio 3/4. -/
def claim25175 : Prop :=
  let X : Polynomial ℚ := Polynomial.X
  let A : Polynomial ℚ := X
  let B : Polynomial ℚ := X + Polynomial.C 1
  let C : Polynomial ℚ := X + Polynomial.C 2
  let D : Polynomial ℚ := X + Polynomial.C 3
  Irreducible A ∧ Irreducible B ∧ Irreducible C ∧ Irreducible D ∧
    A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D ∧
    (A - D) * (B - C) = Polynomial.C (3 / 4 : ℚ) * ((A - C) * (B - D))

end MathlibPlus.Open.NewResearch2.R0834
