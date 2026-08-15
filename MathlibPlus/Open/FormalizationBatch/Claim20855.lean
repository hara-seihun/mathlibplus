import Mathlib

open scoped BigOperators Matrix

namespace MathlibPlus.Open.FormalizationBatch.Claim20855

variable {L : Type*} [Fintype L] [Lattice L] [BoundedOrder L]
  [DecidableEq L] [DecidableLE L]

def meetIrreducible (x : L) : Prop :=
  x ≠ ⊤ ∧ ∀ a b : L, x = a ⊓ b → x = a ∨ x = b

def threeElementSet (t₁ t₂ t₃ : L) : Finset L := {t₁, t₂, t₃}

def tightTrace
    (t₁ t₂ t₃ m : L) (_hm : meetIrreducible m) (t : L) : Prop :=
  t ∈ threeElementSet t₁ t₂ t₃ ∧ t ≤ m

def separatorSet (j jStar m : L) : Prop :=
  meetIrreducible m ∧ jStar ≤ m ∧ ¬ j ≤ m

end MathlibPlus.Open.FormalizationBatch.Claim20855
