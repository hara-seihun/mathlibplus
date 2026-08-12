import Mathlib

namespace MathlibPlus.Open.Combinatorics

/-- Claim 35486.  The full Boolean coordinate family is made explicit as the
finite down-set of all nonempty subsets of source members.  The derived member
has a distinguished star coordinate and contains the Boolean complement of the
nonempty-subset down-set of its source member. -/
def fullBooleanComplementPreservesDistinctnessAndExcludesSunflowers : Prop :=
  ∀ (α : Type*) [DecidableEq α]
    (G : Finset (Finset α)) (w : ℕ),
    0 < w →
    (∀ A ∈ G, A.card = w) →
    let Pstar : Finset α → Finset (Finset α) :=
      fun A => A.powerset.erase ∅
    let D : Finset (Finset α) := G.biUnion Pstar
    let lift : Finset (Finset α) → Finset (Option (Finset α)) :=
      fun S => S.image (fun T : Finset α => some T)
    let derived : Finset α → Finset (Option (Finset α)) :=
      fun A => insert none (lift (D \ Pstar A))
    (∀ A ∈ G, ∀ B ∈ G, A ≠ B → derived A ≠ derived B) ∧
    (∀ A ∈ G, ∀ B ∈ G, A ≠ B →
      derived A ∩ derived B =
        insert none (lift (D \ (Pstar A ∪ Pstar B)))) ∧
    (∀ A ∈ G, ∀ B ∈ G, A ≠ B →
      ∀ T ∈ Pstar A ∪ Pstar B,
        ((∀ U ∈ Pstar A ∪ Pstar B, T ⊆ U → U = T) ↔
          T = A ∨ T = B)) ∧
    (∀ A ∈ G, ∀ B ∈ G, ∀ C ∈ G,
      derived A ∩ derived B = derived A ∩ derived C →
      derived A ∩ derived B = derived B ∩ derived C →
      A = B ∨ A = C ∨ B = C)

end MathlibPlus.Open.Combinatorics
