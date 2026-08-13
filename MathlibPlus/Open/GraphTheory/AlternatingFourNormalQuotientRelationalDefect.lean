import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Every finite group with a normal quotient isomorphic to `A₄` has a
simultaneous two-relation directed Cayley CI defect.  The singleton coordinate
of the quotient witness pulls back to a relation whose exact left-translation
stabilizer is the chosen kernel. -/
def alternatingFourNormalQuotientTwoRelationDefect : Prop :=
  ∀ (G : Type) [Fintype G] [Group G] (N : Subgroup G) [N.Normal],
    Nonempty ((G ⧸ N) ≃* alternatingGroup (Fin 4)) →
    ∃ (S T : Fin 2 → Set G) (e : G ≃ G),
      (∀ i, (1 : G) ∉ S i) ∧
      (∀ i, (1 : G) ∉ T i) ∧
      Set.ncard (S 0) = Nat.card N ∧
      Set.ncard (T 0) = Nat.card N ∧
      Set.ncard (S 1) = 5 * Nat.card N ∧
      Set.ncard (T 1) = 5 * Nat.card N ∧
      (∀ g : G, (fun x : G => g * x) '' S 0 = S 0 ↔ g ∈ N) ∧
      (∀ g : G, (fun x : G => g * x) '' T 0 = T 0 ↔ g ∈ N) ∧
      e 1 = 1 ∧
      Function.Involutive e ∧
      (∀ i x y, x⁻¹ * y ∈ S i ↔ (e x)⁻¹ * e y ∈ T i) ∧
      ¬ ∃ α : G ≃* G, ∀ i, α '' S i = T i

end MathlibPlus.Open.GraphTheory
