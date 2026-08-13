import Mathlib

open scoped BigOperators

namespace MathlibPlus.Algebra

/-- Claim 24574: for three monic split polynomials, all coefficientwise
balances are equivalent to the single polynomial identity.  The factors are
written over an arbitrary commutative ring; the source's cavity-specific
coefficients and index set are not defined in the packet. -/
theorem splitPolynomialCoefficientCriterion_claim24574
    {R ι : Type*} [CommRing R] [Fintype ι]
    (c : Fin 3 → R) (A : Fin 3 → ι → R) :
    let C : Fin 3 → Polynomial R :=
      fun i => ∏ j, (Polynomial.X - Polynomial.C (A i j))
    ((∀ n : ℕ,
        Polynomial.coeff
            (∑ i, Polynomial.C (c i) * C i) n = 0) ↔
      (∑ i, Polynomial.C (c i) * C i) = 0) := by
  dsimp
  constructor
  · intro h
    apply Polynomial.ext
    intro n
    simpa using h n
  · intro h n
    rw [h]
    simp

/-- Claim 5554: the merge operation obeys the five displayed semilattice laws.
The packet does not define its carrier or notation, so the generic `sup`
operation on a bounded semilattice is used as the explicit interface. -/
theorem semilatticeMergeLaws_claim5554
    {α : Type*} [SemilatticeSup α] [OrderBot α] [OrderTop α]
    (a b c : α) :
    a ⊔ b = b ⊔ a ∧
      (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c) ∧
      a ⊔ a = a ∧
      a ⊔ ⊥ = a ∧
      a ⊔ ⊤ = ⊤ := by
  simp [sup_comm, sup_left_comm]

/-- Claim 6239: the four crossed allocation terms factor as the displayed
rectangle difference.  The packet does not define the ambient operator `Φ`,
so it is kept as an arbitrary map and the algebraic factorization is proved
before applying it. -/
theorem fullURectangleDifference_claim6239
    {R S : Type*} [CommRing R]
    (Φ : R → S) (z C D E F : R) :
    Φ (z * C * E + z * D * F - z * C * F - z * D * E) =
      Φ (z * (C - D) * (E - F)) := by
  congr 1
  ring

end MathlibPlus.Algebra
