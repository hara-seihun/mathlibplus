import MathlibPlus.Open.ResearchFormalizationBatch.UPolynomial

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0523NoSingletonDeck

noncomputable section

open Classical
attribute [local instance] Classical.propDecidable Classical.decEq
open MathlibPlus.Open.ResearchFormalizationBatch

abbrev UPolynomial := MvPolynomial ℕ ℤ
abbrev ShiftedPolynomial := MvPolynomial (Option ℕ) ℤ

def deletedGraph {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (S : Finset V) : SimpleGraph {v // v ∉ S} :=
  F.induce {v : V | v ∉ S}

def renamedDeletedUPolynomial {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (S : Finset V) : ShiftedPolynomial :=
  letI : Fintype (↥(deletedGraph F S).edgeSet) :=
    Fintype.ofFinite (deletedGraph F S).edgeSet
  MvPolynomial.rename (fun n : ℕ => some n)
    (MvPolynomial.map (Nat.castRingHom ℤ)
      (graphUPolynomial (deletedGraph F S)))

def noSingletonSubstitute (p : ShiftedPolynomial) : ShiftedPolynomial :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : ℤ →+* ShiftedPolynomial)
    (fun i : Option ℕ =>
      if i = some 1 then 0 else (MvPolynomial.X i : ShiftedPolynomial)) p

def noSingletonUPolynomial {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (S : Finset V) : ShiftedPolynomial :=
  noSingletonSubstitute (renamedDeletedUPolynomial F S)

def independentVertexSet {V : Type*} [DecidableEq V]
    (F : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ ⦃u v : V⦄, u ∈ S → v ∈ S → u ≠ v → ¬ F.Adj u v

def admissibleDeletionSets {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (R : Finset V) : Finset (Finset V) :=
  ((Finset.univ : Finset V).powerset).filter (fun I =>
    independentVertexSet F I ∧ (I ∩ R).card = 0)

def independentDeletionDeck {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (R : Finset V) : ShiftedPolynomial :=
  ∑ I ∈ admissibleDeletionSets F R,
    (-MvPolynomial.X none) ^ I.card * renamedDeletedUPolynomial F I

def noSingletonIndependentDeletionDeck
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (R : Finset V) : ShiftedPolynomial :=
  noSingletonSubstitute (independentDeletionDeck F R)

def noSingletonIndependentDeletionFormula
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (R : Finset V) : ShiftedPolynomial :=
  ∑ I ∈ admissibleDeletionSets F R,
    (-MvPolynomial.X none) ^ I.card * noSingletonUPolynomial F I

/-- Claim 22332: after the no-singleton substitution, the independent-
deletion deck is exactly the sum of the substituted deleted-forest
component polynomials. -/
def claim22332_noSingletonIndependentDeletionDeck : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (R : Finset V),
    noSingletonIndependentDeletionDeck F R =
      noSingletonIndependentDeletionFormula F R

end

end MathlibPlus.Open.ResearchFormalization.R0523NoSingletonDeck
