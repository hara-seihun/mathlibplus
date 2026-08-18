import MathlibPlus.Open.Research.FormalizationBatchUPolynomial

namespace MathlibPlus.Open.ResearchFormalization.R0523Claim22330

noncomputable section

open Classical
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev UPolynomial := MvPolynomial ℕ ℤ
abbrev ShiftedPolynomial := MvPolynomial (Option ℕ) ℤ

def zVariable : ShiftedPolynomial :=
  MvPolynomial.X none

def renameUToY (p : UPolynomial) : ShiftedPolynomial :=
  MvPolynomial.rename (fun n : ℕ => some n) p

def deletedVertices {V : Type} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (S : Finset V) : SimpleGraph {v // v ∉ S} :=
  F.induce {v : V | v ∉ S}

def deletedUPolynomial {V : Type} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (S : Finset V) : UPolynomial :=
  MathlibPlus.Open.ResearchFormalizationBatch.forestUPolynomial
    (deletedVertices F S)

def independentVertexSet {V : Type} [DecidableEq V]
    (F : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ ⦃u v : V⦄, u ∈ S → v ∈ S → u ≠ v → ¬F.Adj u v

def rootedComponentVertices {V : Type} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (C : F.ConnectedComponent) : Finset V :=
  Finset.univ.filter (fun v => F.connectedComponentMk v = C)

def rootedForest {V : Type} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (R : Finset V) : Prop :=
  F.IsAcyclic ∧
    ∀ C : F.ConnectedComponent,
      (rootedComponentVertices F C ∩ R).card = 1

def independentDeletionTransform
    {V : Type} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (R : Finset V) : ShiftedPolynomial :=
  ∑ I ∈ ((Finset.univ : Finset V).powerset).filter (fun I =>
      independentVertexSet F I ∧ Disjoint I R),
    (-zVariable) ^ I.card * renameUToY (deletedUPolynomial F I)

def alphaR {V : Type} [DecidableEq V]
    (F : SimpleGraph V) (R J : Finset V) : ℕ :=
  (J.filter (fun v =>
    independentVertexSet F (J.erase v) ∧
      (J.erase v ∩ R).card = 0)).card

def partialYOne (p : ShiftedPolynomial) : ShiftedPolynomial :=
  ∑ d ∈ p.support, if h : d (some 1) = 0 then 0 else
    MvPolynomial.monomial (d - Finsupp.single (some 1) 1)
      (MvPolynomial.coeff d p * (d (some 1) : ℤ))

def inducedStarDerivativeSum
    {V : Type} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (R : Finset V) : ShiftedPolynomial :=
  ∑ J ∈ ((Finset.univ : Finset V).powerset).filter (fun J => J.Nonempty),
    (alphaR F R J : ShiftedPolynomial) *
      (-zVariable) ^ (J.card - 1) * renameUToY (deletedUPolynomial F J)

/-- The y₁ derivative of the rooted-forest independent-deletion transform is
exactly the alpha-weighted induced-star deletion sum. -/
def claim22330 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (R : Finset V),
    rootedForest F R →
      partialYOne (independentDeletionTransform F R) =
        inducedStarDerivativeSum F R

end

end MathlibPlus.Open.ResearchFormalization.R0523Claim22330
