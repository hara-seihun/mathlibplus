import MathlibPlus.Open.ResearchFormalization.R0523Claim22338

namespace MathlibPlus.Open.ResearchFormalization.R0523Claim22326

noncomputable section

open scoped BigOperators
open MathlibPlus.Open.ResearchFormalization.R0523Claim22338

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The cut expansion written on the reviewed shifted rooted-factor carrier. -/
def alternatingDeletionSum {V : Type*} [Fintype V] [DecidableEq V]
    (B : SimpleGraph V) (r : V) : ShiftedPolynomial :=
  ∑ I ∈ ((Finset.univ : Finset V).powerset).filter (fun I =>
      independentVertexSet B I ∧ r ∉ I),
    (-MvPolynomial.X none) ^ I.card *
      renameUToY (deletedUPolynomial B I)

/-- The internal alternating edge-subset factor appearing after grouping cut
    terms by the union of selected nonroot components. -/
def internalAlternatingFactor {V : Type*} [Fintype V] [DecidableEq V]
    (B : SimpleGraph V) (I : Finset V) : ℤ :=
  ∑ A ∈
      ((Finset.univ :
        Finset (↥(B.induce (I : Set V)).edgeSet)).powerset),
    (-1 : ℤ) ^ A.card

def groupedCutFactor {V : Type*} [Fintype V] [DecidableEq V]
    (B : SimpleGraph V) (I : Finset V) (z : ShiftedPolynomial) :
    ShiftedPolynomial :=
  (-z) ^ I.card * (internalAlternatingFactor B I : ShiftedPolynomial)

/-- Claim 22326: the shifted rooted factor is the independent-deletion sum,
    and the actual internal edge-subset alternating factor is one exactly for
    independent unions and zero otherwise. -/
def claim22326_alternatingIndependentDeletionIdentity : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (B : SimpleGraph V) (r : V),
    B.IsTree →
      shiftedRootedFactor B r = alternatingDeletionSum B r ∧
        (∀ I : Finset V,
          internalAlternatingFactor B I =
            if independentVertexSet B I then 1 else 0) ∧
        (∀ I : Finset V, ∀ z : ShiftedPolynomial,
          groupedCutFactor B I z =
            (-z) ^ I.card *
              (if independentVertexSet B I then
                (1 : ShiftedPolynomial) else 0))

end

end MathlibPlus.Open.ResearchFormalization.R0523Claim22326
