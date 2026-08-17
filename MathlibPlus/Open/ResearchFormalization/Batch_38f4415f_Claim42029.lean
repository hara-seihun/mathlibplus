import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.Claim42029

private def regularOn {B : Type*} (P : Subgroup (Equiv.Perm B)) : Prop :=
  ∀ x y : B, ∃! g : P, g.1 x = y

private def abelianSubgroup {B : Type*}
    (P : Subgroup (Equiv.Perm B)) : Prop :=
  ∀ a b : P, a * b = b * a

/-- Two regular abelian subgroups of one finite p-subgroup of Sym(B) share
    the nontrivial central p-line. -/
def claim42029 : Prop :=
  ∀ (B : Type*) [Fintype B]
    (p : ℕ) (hp : Nat.Prime p)
    (U P Q : Subgroup (Equiv.Perm B)),
    P ≤ U → Q ≤ U →
    IsPGroup p U →
    regularOn P → regularOn Q →
    abelianSubgroup P → abelianSubgroup Q →
    ((Subgroup.center U : Subgroup U) ≠ ⊥) ∧
    (∀ z : Subgroup.center U, (z.1 : Equiv.Perm B) ∈ P) ∧
    (∀ z : Subgroup.center U, (z.1 : Equiv.Perm B) ∈ Q) ∧
    ∃ D : Subgroup (Equiv.Perm B),
      D ≤ P ∧ D ≤ Q ∧ Nat.card D = p

end MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.Claim42029
