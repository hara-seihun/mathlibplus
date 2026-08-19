import Mathlib

noncomputable section

namespace MathlibPlus.Open.GroupTheory.Claim24811HallCommuting

def conjugateSubgroup {G : Type*} [Group G]
    (g : G) (Q : Subgroup G) : Subgroup G :=
  Q.map (MulAut.conj g)

/-- Claim 24811: when the relevant ambient Sylow p-subgroups are elementary
abelian, Sylow containment and conjugacy place the two p-subgroups in one
commuting adjusted copy. -/
def claim24811_hallGroupsCanBeMadeCommuting : Prop :=
  ∀ {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (P Q : Subgroup G),
    Nat.card P = p →
    Nat.card Q = p →
    IsPGroup p P →
    IsPGroup p Q →
    (∀ S : Sylow p G, ∀ a b : S, Commute (a : G) (b : G)) →
    ∃ S : Sylow p G,
      P ≤ (S : Subgroup G) ∧
        ∃ g : G,
          conjugateSubgroup g Q ≤ (S : Subgroup G) ∧
            ∀ a ∈ P, ∀ b ∈ Q,
              Commute a (MulAut.conj g b)

end MathlibPlus.Open.GroupTheory.Claim24811HallCommuting
