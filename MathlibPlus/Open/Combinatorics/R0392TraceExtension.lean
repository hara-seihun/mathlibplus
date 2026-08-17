import Mathlib

open Classical

namespace MathlibPlus.Open.Combinatorics.R0392

noncomputable section

/-- Pairwise intersection for an indexed finite-set family. -/
def pairwiseIntersecting {I V : Type*} [DecidableEq I] [DecidableEq V]
    (F : I → Finset V) : Prop :=
  ∀ i j, i ≠ j → (F i ∩ F j).Nonempty

/-- Three distinct members form a sunflower when their pairwise intersections
are the same core. -/
def threeSunflower {I V : Type*} [DecidableEq I] [DecidableEq V]
    (F : I → Finset V) (i j k : I) : Prop :=
  F i ∩ F j = F i ∩ F k ∧ F i ∩ F j = F j ∩ F k

/-- A family is free of three-sunflowers. -/
def threeSunflowerFree {I V : Type*} [DecidableEq I] [DecidableEq V]
    (F : I → Finset V) : Prop :=
  ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ threeSunflower F i j k

/-- The ordinary family obtained by adjoining the distinguished pivot member. -/
def extendedMember {I V : Type*} [DecidableEq I] [DecidableEq V]
    (X : Finset V) (C T : I → Finset V) (o : Option I) : Finset V :=
  match o with
  | none => X
  | some i => C i ∪ T i

/-- The arbitrary fixed-weight trace-code extension, with the pivot included
in the ordinary indexed family. -/
def claim_20839 : Prop :=
  ∀ {I V : Type*} [DecidableEq I] [DecidableEq V]
    (X Y : Finset V) (C T : I → Finset V) (b p : ℕ),
    Function.Injective C →
      (∀ i : I, C i ⊆ Y ∧ (C i).card = b) →
        pairwiseIntersecting C →
          threeSunflowerFree C →
            Disjoint X Y →
              X.card = b + p →
                (∀ i : I, T i ⊆ X ∧ (T i).card = p) →
                  Function.Injective (extendedMember X C T) ∧
                    (∀ o : Option I,
                      (extendedMember X C T o).card = b + p) ∧
                    pairwiseIntersecting (extendedMember X C T) ∧
                    threeSunflowerFree (extendedMember X C T) ∧
                    (∀ i : I,
                      X ∩ extendedMember X C T (some i) = T i)

end

end MathlibPlus.Open.Combinatorics.R0392
