import Mathlib

namespace MathlibPlus.Open.Research

universe u

/-- The inverse-closed valency-twelve connection sets of a finite additive group. -/
abbrev connectionSet (G : Type u) [AddGroup G] [Fintype G] [DecidableEq G] : Type u :=
  {S : Finset G // 0 ∉ S ∧ (∀ g : G, g ∈ S ↔ -g ∈ S) ∧ S.card = 12}

/-- The group `C₂³ × C₃²` from the admitted census claim. -/
abbrev censusGroup : Type :=
  ((ZMod 2 × ZMod 2) × ZMod 2) × (ZMod 3 × ZMod 3)

noncomputable instance connectionSetFintype (G : Type u) [AddGroup G] [Fintype G]
    [DecidableEq G] : Fintype (connectionSet G) := Fintype.ofFinite _

def automorphismSetoid (G : Type*) [AddGroup G] [Fintype G] [DecidableEq G] :
    Setoid (connectionSet G) where
  r S T := ∃ e : G ≃+ G, ∀ x : G, x ∈ S.1 ↔ e x ∈ T.1
  iseqv := {
    refl := by
      intro S
      exact ⟨AddEquiv.refl G, by simp⟩
    symm := by
      intro S T h
      rcases h with ⟨e, h⟩
      refine ⟨e.symm, ?_⟩
      intro x
      simpa using (h (e.symm x)).symm
    trans := by
      intro S T U hST hTU
      rcases hST with ⟨e, hST⟩
      rcases hTU with ⟨f, hTU⟩
      refine ⟨e.trans f, ?_⟩
      intro x
      change x ∈ S.1 ↔ f (e x) ∈ U.1
      exact (hST x).trans (hTU (e x))
  }

noncomputable instance automorphismQuotientFintype (G : Type u) [AddGroup G] [Fintype G]
    [DecidableEq G] : Fintype (Quotient (automorphismSetoid G)) := Fintype.ofFinite _

def graphIsomorphismSetoid (G : Type*) [AddGroup G] [Fintype G] [DecidableEq G] :
    Setoid (connectionSet G) where
  r S T := ∃ e : G ≃ G, ∀ x y : G,
    (y - x ∈ S.1 ↔ e y - e x ∈ T.1)
  iseqv := {
    refl := by
      intro S
      exact ⟨Equiv.refl G, by simp⟩
    symm := by
      intro S T h
      rcases h with ⟨e, h⟩
      refine ⟨e.symm, ?_⟩
      intro x y
      simpa using (h (e.symm x) (e.symm y)).symm
    trans := by
      intro S T U hST hTU
      rcases hST with ⟨e, hST⟩
      rcases hTU with ⟨f, hTU⟩
      refine ⟨e.trans f, ?_⟩
      intro x y
      change y - x ∈ S.1 ↔ f (e y) - f (e x) ∈ U.1
      exact (hST x y).trans (hTU (e x) (e y))
  }

noncomputable instance graphQuotientFintype (G : Type u) [AddGroup G] [Fintype G]
    [DecidableEq G] : Fintype (Quotient (graphIsomorphismSetoid G)) := Fintype.ofFinite _

/-- Claim 29174: the exact connection-set, automorphism-orbit, and graph-isomorphism census. -/
def claim29174 : Prop :=
  Fintype.card (connectionSet censusGroup) = 6428408 ∧
    Fintype.card (Quotient (automorphismSetoid censusGroup)) = 3122 ∧
    Fintype.card (Quotient (graphIsomorphismSetoid censusGroup)) = 3122

end MathlibPlus.Open.Research
