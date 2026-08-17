import Mathlib

namespace MathlibPlus.Open.GroupTheory.R1658

/-- Claim 37951: a coprime product automorphism preserving all lifted
relation sets preserves the factor axis and restricts to an automorphism of
that factor carrying every source relation to its target. -/
def productCI2AutomorphismRestrictsToFactor_claim37951 : Prop :=
  ∀ {A B : Type*} [Group A] [Group B] [Fintype A] [Fintype B]
    (hcoprime : Nat.Coprime (Fintype.card A) (Fintype.card B))
    (k : ℕ) (S T : Fin k → Set A)
    (φ : (A × B) ≃* (A × B)),
    (∀ i : Fin k,
      Set.image φ (S i ×ˢ ({1} : Set B)) =
        T i ×ˢ ({1} : Set B)) →
    Set.image φ {g : A × B | g.2 = 1} =
        {g : A × B | g.2 = 1} ∧
      ∃ ψ : A ≃* A,
        (∀ a : A, φ (a, 1) = (ψ a, 1)) ∧
          (∀ i : Fin k, Set.image ψ (S i) = T i)

end MathlibPlus.Open.GroupTheory.R1658
