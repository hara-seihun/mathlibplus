import Mathlib

namespace MathlibPlus.Open.Combinatorics.TreeAttachment

variable {V : Type*} [Fintype V] [DecidableEq V]

def attachedLeafAdj (G : SimpleGraph V) (v : V) : Option V → Option V → Prop
  | some x, some y => G.Adj x y
  | none, some y => y = v
  | some x, none => x = v
  | none, none => False

def attachLeaf (G : SimpleGraph V) (v : V) : SimpleGraph (Option V) where
  Adj := attachedLeafAdj G v
  symm := ⟨by
    intro x y h
    cases x with
    | none =>
        cases y with
        | none => simp [attachedLeafAdj] at h
        | some y => exact h
    | some x =>
        cases y with
        | none => exact h
        | some y => exact G.symm.symm x y h⟩
  loopless := ⟨by
    intro x
    cases x with
    | none => simp [attachedLeafAdj]
    | some x => exact G.loopless.irrefl x⟩

def graphAutomorphism (G : SimpleGraph V) (e : Equiv.Perm V) : Prop :=
  ∀ x y, G.Adj x y ↔ G.Adj (e x) (e y)

def sameAutomorphismOrbit (G : SimpleGraph V) (v w : V) : Prop :=
  ∃ e : Equiv.Perm V, graphAutomorphism G e ∧ e v = w

def attachmentCodeEquality (G : SimpleGraph V) (v w : V) : Prop :=
  Nonempty (attachLeaf G v ≃g attachLeaf G w)

/-- For a finite tree, unlabelled leaf-attachment codes are exactly automorphism orbits. -/
def attachmentCodeFibersAreAutomorphismOrbits (G : SimpleGraph V) : Prop :=
  G.IsTree → ∀ v w,
    attachmentCodeEquality G v w ↔ sameAutomorphismOrbit G v w

end MathlibPlus.Open.Combinatorics.TreeAttachment
