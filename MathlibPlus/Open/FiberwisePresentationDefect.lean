import Mathlib

namespace MathlibPlus.Open

open scoped BigOperators

noncomputable section

private abbrev RootedOccurrence (Card : Type*) (Vertex : Card → Type*) :=
  Sigma Vertex

private abbrev RelationSpace (Card : Type*) (Vertex : Card → Type*) :=
  RootedOccurrence Card Vertex →₀ ℚ

private def BasisVector {Card : Type*} {Vertex : Card → Type*}
    (x : RootedOccurrence Card Vertex) : RelationSpace Card Vertex :=
  Finsupp.single x 1

private def MomentVector {Card : Type*} {Vertex : Card → Type*}
    [∀ C, Fintype (Vertex C)]
    (Feature : Type*) (weight : Feature → RootedOccurrence Card Vertex → ℚ)
    (f : Feature) (C : Card) : RelationSpace Card Vertex :=
  ∑ v : Vertex C, weight f ⟨C, v⟩ • BasisVector ⟨C, v⟩

private def MomentSpace {Card : Type*} {Vertex : Card → Type*}
    [Fintype Card] [∀ C, Fintype (Vertex C)]
    (Feature : Type*) [Fintype Feature]
    (weight : Feature → RootedOccurrence Card Vertex → ℚ) :
    Submodule ℚ (RelationSpace Card Vertex) :=
  Submodule.span ℚ (Set.range fun p : Feature × Card => MomentVector Feature weight p.1 p.2)

private def GlobalExchangeSpace {Card : Type*} {Vertex : Card → Type*}
    {Tree : Type*}
    (attach : RootedOccurrence Card Vertex → Tree) :
    Submodule ℚ (RelationSpace Card Vertex) :=
  Submodule.span ℚ {
    z | ∃ x y : RootedOccurrence Card Vertex,
      attach x = attach y ∧ z = BasisVector x - BasisVector y
  }

private def InternalExchangeSpace {Card : Type*} {Vertex : Card → Type*}
    {Tree : Type*}
    (attach : RootedOccurrence Card Vertex → Tree) :
    Submodule ℚ (RelationSpace Card Vertex) :=
  Submodule.span ℚ {
    z | ∃ (C : Card) (v v' : Vertex C),
      attach ⟨C, v⟩ = attach ⟨C, v'⟩ ∧
        z = BasisVector ⟨C, v⟩ - BasisVector ⟨C, v'⟩
  }

/--
The fiberwise presentation defect uses only same-card leaf exchanges, and the
inclusion of those exchanges into the global same-target exchange space gives
a unique quotient map to the global attachment presentation defect.
-/
def fiberwisePresentationDefect
    (Card : Type*) (Vertex : Card → Type*) (Tree : Type*)
    [Fintype Card] [∀ C, Fintype (Vertex C)]
    (attach : RootedOccurrence Card Vertex → Tree)
    (Feature : Type*) [Fintype Feature]
    (weight : Feature → RootedOccurrence Card Vertex → ℚ) : Prop :=
  ∃! q :
      (RelationSpace Card Vertex ⧸
          (MomentSpace Feature weight ⊔ InternalExchangeSpace attach)) →ₗ[ℚ]
        (RelationSpace Card Vertex ⧸
          (MomentSpace Feature weight ⊔ GlobalExchangeSpace attach)),
    ∀ x : RelationSpace Card Vertex,
      q (Submodule.Quotient.mk x) = Submodule.Quotient.mk x

end

end MathlibPlus.Open
