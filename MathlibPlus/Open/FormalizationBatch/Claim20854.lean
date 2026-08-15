import Mathlib

open scoped BigOperators Matrix

namespace MathlibPlus.Open.FormalizationBatch.Claim20854

variable {L : Type*} [Fintype L] [Lattice L] [BoundedOrder L]
  [DecidableEq L] [DecidableLE L]

def joinIrreducible (x : L) : Prop :=
  x ≠ ⊥ ∧ ∀ a b : L, x = a ⊔ b → x = a ∨ x = b

def lowerCover (a b : L) : Prop :=
  a < b ∧ ¬ ∃ x : L, a < x ∧ x < b

def threeElementSet (t₁ t₂ t₃ : L) : Finset L := {t₁, t₂, t₃}

def finiteJoin (S : Finset L) : L := S.sup id

def tightEdgeSurvivalDownset
    (t₁ t₂ t₃ j jStar : L)
    (_ht₁ : joinIrreducible t₁)
    (_ht₂ : joinIrreducible t₂)
    (_ht₃ : joinIrreducible t₃)
    (_hj : joinIrreducible j)
    (_hjT : j ∉ threeElementSet t₁ t₂ t₃)
    (_hcover : lowerCover jStar j)
    (S : Finset L) : Prop :=
  S ⊆ threeElementSet t₁ t₂ t₃ ∧
    jStar ⊔ finiteJoin S < j ⊔ finiteJoin S

end MathlibPlus.Open.FormalizationBatch.Claim20854
