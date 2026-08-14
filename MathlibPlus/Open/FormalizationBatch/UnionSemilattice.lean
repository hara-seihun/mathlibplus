import Mathlib

namespace MathlibPlus.Open.FormalizationBatch

/-- The assembly law that would turn union into addition in a free divisor group. -/
def UnionAdditiveEncoding (α G : Type) [DecidableEq α] [AddGroup G]
    (f : Finset α → G) : Prop :=
  f ∅ = 0 ∧ ∀ A B : Finset α, f (A ∪ B) = f A + f B

/-- Claim 12209: union idempotence kills every generator under group assembly. -/
def claim12209 : Prop :=
  (∀ (α : Type) [DecidableEq α] (f : Finset α → Finsupp α ℤ),
      UnionAdditiveEncoding α (Finsupp α ℤ) f →
        ∀ a : α, f {a} = 0) ∧
    (∀ (α : Type) [DecidableEq α] (_ : Nonempty α),
      ¬ ∃ f : Finset α → Finsupp α ℤ,
        UnionAdditiveEncoding α (Finsupp α ℤ) f ∧
          ∀ a : α, f {a} = Finsupp.single a 1) ∧
    (∀ (α : Type) (a : α),
      Finsupp.single a (2 : ℤ) ≠ Finsupp.single a 1 ∧
        Finsupp.single a (-2 : ℤ) ≠ 0)

end MathlibPlus.Open.FormalizationBatch
