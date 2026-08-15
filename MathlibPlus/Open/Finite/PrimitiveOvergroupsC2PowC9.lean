import Mathlib

namespace MathlibPlus.Open

/-- Claim 28554: the primitive overgroups of the indicated regular groups are
2-transitive, with the three stated action degrees. -/
def primitiveOvergroupsOfC2PowC9AreTwoTransitive : Prop :=
  ∀ (r : ℕ) (Ω : Type*) [Fintype Ω],
    ((r = 3 ∧ Fintype.card Ω = 72) ∨
      (r = 4 ∧ Fintype.card Ω = 144) ∨
      (r = 5 ∧ Fintype.card Ω = 288)) →
    ∀ P : Subgroup (Equiv.Perm Ω),
      ((∀ x y : Ω, ∃ p : P, (p : Equiv.Perm Ω) x = y) ∧
        (∀ B : Set Ω,
          B.Nonempty →
            (∀ p : P,
              B.image (p : Equiv.Perm Ω) = B ∨
                Disjoint (B.image (p : Equiv.Perm Ω)) B) →
            B.Subsingleton ∨ B = Set.univ)) →
      ∀ K : Subgroup (Equiv.Perm Ω),
        (∀ x y : Ω, ∃! k : K, (k : Equiv.Perm Ω) x = y) →
        Nonempty
          (((Multiplicative (Fin r → ZMod 2)) × Multiplicative (ZMod 9)) ≃*
            K) →
        K ≤ P →
        (∀ ⦃x₁ x₂ y₁ y₂ : Ω⦄,
          x₁ ≠ x₂ → y₁ ≠ y₂ →
            ∃ p : P,
              (p : Equiv.Perm Ω) x₁ = y₁ ∧
                (p : Equiv.Perm Ω) x₂ = y₂)

end MathlibPlus.Open
