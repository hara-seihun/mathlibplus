import Mathlib

namespace MathlibPlus.Open.Analysis

/--
For a finite cochain index type, exact coordinate boundaries on a set of
indices give cocycle representatives supported on the complementary indices.
The final conjunct records the stated vanishing consequence when every
coordinate belongs to the chosen set.
-/
def cocycleRepresentativeOutside
    {R I C1 C3 : Type*}
    [Ring R] [Fintype I]
    [AddCommGroup C1] [Module R C1]
    [AddCommGroup C3] [Module R C3]
    (d₁ : C1 →ₗ[R] (I → R))
    (d₂ : (I → R) →ₗ[R] C3) : Prop :=
  letI : DecidableEq I := Classical.decEq I
  d₂.comp d₁ = 0 →
  ∀ (J : Set I),
    (∀ i : I, i ∈ J →
      ∃ x : C1, d₁ x = (fun j : I => if j = i then 1 else 0)) →
    (∀ y : I → R, d₂ y = 0 →
        ∃ z : C1, ∃ r : I → R,
          d₂ r = 0 ∧
            r = y - d₁ z ∧
              (∀ i : I, i ∈ J → r i = 0) ∧
                (∀ i : I, i ∉ J → r i = y i)) ∧
      (J = Set.univ →
        ∀ y : I → R, d₂ y = 0 → ∃ z : C1, d₁ z = y)

end MathlibPlus.Open.Analysis
