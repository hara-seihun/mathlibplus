import Mathlib

namespace MathlibPlus.Open.Algebra.Claim9651

universe u v

/--
The nonidempotent multiset calculus is a distinct model from the native
idempotent set-scar algebra: its multiplicity-sensitive statements cannot be
transported from set scars without an observer that forgets multiplicity.
-/
def multiset_model_is_new_theory : Prop :=
  (∀ {α : Type u} (A : Set α), A ∪ A = A) ∧
  (∀ {α : Type u} (a : α),
    ({a} : Multiset α) + {a} ≠ ({a} : Multiset α)) ∧
  (∀ {α : Type u} (translation : Set α → Multiset α),
    (∀ a : α, translation {a} = ({a} : Multiset α)) →
    (∀ A B : Set α, translation (A ∪ B) = translation A + translation B) →
    False) ∧
  (∀ {α : Type u} {β : Type v} (D : Multiset α → β),
    (∀ M N : Multiset α,
      (∀ a : α, a ∈ M ↔ a ∈ N) → D M = D N) →
    (∀ a : α, D ({a} : Multiset α) = D (({a} : Multiset α) + {a})))

end MathlibPlus.Open.Algebra.Claim9651
