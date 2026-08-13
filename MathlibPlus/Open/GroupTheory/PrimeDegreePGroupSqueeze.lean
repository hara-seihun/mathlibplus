import Mathlib

namespace MathlibPlus.Open.GroupTheory

/--
Claim 29877 (formalized from the admitted prime-degree p-group squeeze).
The induced permutation group is represented by a subgroup of the symmetric
permutation group on `Fin p`; the two transitive order-`p` subgroups are
represented as subgroups of that induced group.
-/
def primeDegreePGroupSqueeze_claim29877 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    ∀ (H : Subgroup (Equiv.Perm (Fin p))),
      IsPGroup p H →
        Nat.card H ∣ Nat.factorial p ∧
          Nat.card H ≤ p ∧
            ∀ (C₁ C₂ : Subgroup H),
              IsCyclic C₁ →
              IsCyclic C₂ →
              Nat.card C₁ = p →
              Nat.card C₂ = p →
              (∀ x y : Fin p, ∃ c : C₁,
                (c.1 : Equiv.Perm (Fin p)) x = y) →
              (∀ x y : Fin p, ∃ c : C₂,
                (c.1 : Equiv.Perm (Fin p)) x = y) →
              C₁ = ⊤ ∧ C₂ = ⊤

end MathlibPlus.Open.GroupTheory
