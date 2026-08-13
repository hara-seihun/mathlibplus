import Mathlib

namespace MathlibPlus.Open.Combinatorics

/-- Faithful registry node for the minimum-lattice necessary conditions.  The
packet does not define its strict-majority or exact-half tightness statistics,
so those two source relations are explicit parameters rather than silently
chosen counting conventions. -/
def minimumLatticeNecessaryConditions_claim20810
    (α : Type*) [Fintype α] [Lattice α] [BoundedOrder α]
    (joinBelowStrictMajority : Finset α → α → Prop)
    (exactHalfTight : α → α → Prop) : Prop :=
  let meetIrreducible : α → Prop := fun x =>
    x ≠ ⊤ ∧ ∀ a b : α, x = a ⊓ b → x = a ∨ x = b
  let joinIrreducible : α → Prop := fun x =>
    x ≠ ⊥ ∧ ∀ a b : α, x = a ⊔ b → x = a ∨ x = b
  Fintype.card α ≥ 53 ∧
    (∀ x y : α,
      meetIrreducible x → joinIrreducible y → ¬ x ≤ y) ∧
    (∀ x : α, ¬ (meetIrreducible x ∧ joinIrreducible x)) ∧
    (∀ S : Finset α,
      S.Nonempty →
      (∀ x ∈ S, meetIrreducible x) →
      ∃ y : α, joinIrreducible y ∧ joinBelowStrictMajority S y) ∧
    (∀ x : α,
      meetIrreducible x →
      ∃ y : α, joinIrreducible y ∧ y ≤ x ∧ exactHalfTight y x) ∧
    (∀ x : α,
      x ≠ ⊥ → x ≠ ⊤ →
      ∃ a b c : α,
        ¬ a ≤ b ∧ ¬ b ≤ a ∧
        ¬ a ≤ c ∧ ¬ c ≤ a ∧
        ¬ b ≤ c ∧ ¬ c ≤ b)

end MathlibPlus.Open.Combinatorics
