import MathlibPlus.Basic

namespace MathlibPlus.Open.GroupTheory

/-- Claim 47313.  On the literal source-level universal type of permutations,
repair the points where the multiplication table already holds and fix the
complement.  The source does not state finiteness of `Ω`, so that issue is
left visible in this registry proposition rather than silently added. -/
def repairedPermutationTable_claim47313 : Prop :=
  ∀ {G Ω : Type*} [Group G] (Φ : G → Equiv.Perm Ω),
    let X : Set Ω :=
      {x | ∀ g h, Φ g (Φ h x) = Φ (g * h) x}
    let B : Set Ω := (Set.univ : Set Ω) \ X
    (∀ k, Set.MapsTo (Φ k) X X ∧ Φ k '' X = X) ∧
      (∀ x, x ∈ X → Φ 1 x = x) ∧
      ∃ Ψ : G → Equiv.Perm Ω,
        (∀ g x, x ∈ X → Ψ g x = Φ g x) ∧
          (∀ g x, x ∈ B → Ψ g x = x) ∧
          (∀ g h x, Ψ g (Ψ h x) = Ψ (g * h) x) ∧
          (∀ x, Ψ 1 x = x)

end MathlibPlus.Open.GroupTheory
