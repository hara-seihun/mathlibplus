import MathlibPlus.Open.ResearchFormalization.R1516

namespace MathlibPlus.Open.ResearchFormalization.R1516.Claim38061

noncomputable section

/-- A noncentralizing row relabeling changes the normalized base and therefore
cannot be identified with the same normalized row profile. -/
def noncentralizingRowPermutationIsCounterfeit_claim38061 : Prop :=
  ∀ (A B : Type*) [Fintype A] [Fintype B] [Group A] [Group B]
    (σ α : Equiv.Perm A) (q : A → Equiv.Perm B),
    (¬ ∀ a : A, α (σ a) = σ (α a)) →
      let f : A × B → A × B := skewRowMap σ q
      let Φ : A × B ≃ A × B := Equiv.prodCongr α (Equiv.refl B)
      let transported : A × B → A × B :=
        fun p => Φ.symm (f (Φ p))
      let normalizedProfileEquivalence
          (g h : A × B → A × B) : Prop :=
        ∃ q₁ q₂ : A → Equiv.Perm B,
          (∀ a b, g (a, b) = (σ a, q₁ a b)) ∧
            ∀ a b, h (a, b) = (σ a, q₂ a b)
      (∀ a : A, ∀ b : B,
        transported (a, b) =
          (α.symm (σ (α a)), q (α a) b)) ∧
        α.symm * σ * α ≠ σ ∧
        ¬ normalizedProfileEquivalence f transported

end

end MathlibPlus.Open.ResearchFormalization.R1516.Claim38061
