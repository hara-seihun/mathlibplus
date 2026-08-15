import Mathlib

noncomputable section
open scoped BigOperators
open Set MeasureTheory

namespace MathlibPlus.Open.ResearchFormalization.Batch

/-- The three labeled points used in the fixed-order complement example. -/
abbrev U123 := {x : Fin 4 // x.1 ≠ 0}

def e1 : U123 := ⟨1, by decide⟩
def e2 : U123 := ⟨2, by decide⟩
def e3 : U123 := ⟨3, by decide⟩
def universe123 : Finset U123 := {e1, e2, e3}
def triangleFamily : Finset (Finset U123) :=
  {{e1, e2}, {e1, e3}, {e2, e3}}

def pairwiseIntersecting (F : Finset (Finset U123)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ≠ B → (A ∩ B).Nonempty

def isThreeSunflower (F : Finset (Finset U123)) : Prop :=
  ∃ core : Finset U123,
    (∀ A ∈ F, core ⊆ A) ∧
    (∀ A ∈ F, ∀ B ∈ F, A ≠ B →
      (A \ core) ∩ (B \ core) = ∅)

def unionClosed (F : Finset (Finset U123)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F

def complementFamily123 : Finset (Finset U123) :=
  triangleFamily.image (fun A => universe123 \ A)

def claim35484 : Prop :=
  pairwiseIntersecting triangleFamily ∧
    ¬isThreeSunflower triangleFamily ∧
    complementFamily123 = {{e3}, {e2}, {e1}} ∧
    isThreeSunflower complementFamily123 ∧
    ¬unionClosed complementFamily123
end MathlibPlus.Open.ResearchFormalization.Batch
