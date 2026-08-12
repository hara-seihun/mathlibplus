import Mathlib

namespace MathlibPlus.Algebra.FamilyProduct

/-- The union product of two families of subsets of `X`. -/
def familyProduct {X : Type*} (A B : Set (Set X)) : Set (Set X) :=
  {c | ∃ a ∈ A, ∃ b ∈ B, a ∪ b = c}

/-- The family product is commutative. The nonemptiness hypotheses are retained
from the informal claim, although the equality itself does not need them. -/
theorem familyProduct_commutative {X : Type*} (A B : Set (Set X))
    (_hA : A.Nonempty) (_hB : B.Nonempty) :
    familyProduct A B = familyProduct B A := by
  ext c
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨b, hb, a, ha, Set.union_comm b a⟩
  · rintro ⟨b, hb, a, ha, rfl⟩
    exact ⟨a, ha, b, hb, Set.union_comm a b⟩

/-- The family product is associative. -/
theorem familyProduct_associative {X : Type*}
    (A B C : Set (Set X))
    (_hA : A.Nonempty) (_hB : B.Nonempty) (_hC : C.Nonempty) :
    familyProduct (familyProduct A B) C =
      familyProduct A (familyProduct B C) := by
  ext u
  constructor
  · rintro ⟨v, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩
    refine ⟨a, ha, b ∪ c, ?_, ?_⟩
    · exact ⟨b, hb, c, hc, rfl⟩
    · ext x
      simp [or_assoc]
  · rintro ⟨a, ha, v, ⟨b, hb, c, hc, rfl⟩, rfl⟩
    refine ⟨a ∪ b, ?_, c, hc, ?_⟩
    · exact ⟨a, ha, b, hb, rfl⟩
    · ext x
      simp [or_assoc]

/-- The family product is monotone for inclusion in either factor. -/
theorem familyProduct_mono {X : Type*}
    {A A' B B' : Set (Set X)}
    (hAA' : A ⊆ A') (hBB' : B ⊆ B') :
    familyProduct A B ⊆ familyProduct A' B' := by
  intro u hu
  rcases hu with ⟨a, ha, b, hb, rfl⟩
  exact ⟨a, hAA' ha, b, hBB' hb, rfl⟩

end MathlibPlus.Algebra.FamilyProduct
