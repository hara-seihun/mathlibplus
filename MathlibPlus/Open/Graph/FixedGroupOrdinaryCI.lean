import Mathlib

namespace MathlibPlus.Open

abbrev FixedGroup := (ZMod 2 × ZMod 2 × ZMod 2) × (ZMod 3 × ZMod 3)

def OrdinaryUndirectedConnectionSet (S : Set FixedGroup) : Prop :=
  (0 : FixedGroup) ∉ S ∧ ∀ x : FixedGroup, x ∈ S ↔ -x ∈ S

def cayleyGraph (S : Set FixedGroup)
    (hS : OrdinaryUndirectedConnectionSet S) : SimpleGraph FixedGroup where
  Adj x y := x ≠ y ∧ y - x ∈ S
  symm := ⟨by
    intro x y hxy
    constructor
    · exact Ne.symm hxy.1
    · have hneg : -(y - x) ∈ S := (hS.2 (y - x)).1 hxy.2
      simpa [sub_eq_add_neg, add_comm] using hneg⟩
  loopless := ⟨by
    intro x hxx
    exact hxx.1 rfl⟩

def fixedGroupOrdinaryCI : Prop :=
  Fintype.card FixedGroup = 72 ∧
    ∀ (S T : Set FixedGroup)
      (hS : OrdinaryUndirectedConnectionSet S)
      (hT : OrdinaryUndirectedConnectionSet T),
      Nonempty (SimpleGraph.Iso (cayleyGraph S hS) (cayleyGraph T hT)) →
        ∃ φ : FixedGroup ≃+ FixedGroup, φ '' S = T

end MathlibPlus.Open
