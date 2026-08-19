import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch20463

namespace MathlibPlus.Open.ResearchFormalization.Claim23126

open MathlibPlus.Open.ResearchFormalizationBatch20463

noncomputable section

structure PairProfileCoordinate (n : ℕ) where
  adjacency : Bool
  leftDegree : Fin (n + 1)
  rightDegree : Fin (n + 1)
  commonNeighbors : Fin (n + 1)

def finiteCardPairProfile {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (G : SimpleGraph V) (removed : Finset V) :
    PairProfileCoordinate n → ℕ :=
  fun coordinate =>
    cardPairProfile G removed coordinate.adjacency
      coordinate.leftDegree.val coordinate.rightDegree.val
      coordinate.commonNeighbors.val

def cardPairProfileMultiset {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (G : SimpleGraph V) :
    Multiset (PairProfileCoordinate n → ℕ) :=
  Multiset.map
    (fun v => finiteCardPairProfile n G {v})
    (Finset.univ : Finset V).val

def sameCardPairProfileMultiset
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (n : ℕ) (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  cardPairProfileMultiset n G = cardPairProfileMultiset n H

def cardProfilePolynomialMoment
    {V : Type*} [Fintype V] [DecidableEq V]
    {n : ℕ} (G : SimpleGraph V) (v : V)
    {R : Type*} [CommSemiring R]
    (P : MvPolynomial (PairProfileCoordinate n) R) : R :=
  MvPolynomial.eval
    (fun coordinate =>
      (finiteCardPairProfile n G {v} coordinate : R)) P

def graphWitnessLeftRelation (u v : Fin 10) : Prop :=
  (u = 0 ∧ v = 6) ∨
    (u = 0 ∧ v = 8) ∨
    (u = 1 ∧ v = 7) ∨
    (u = 1 ∧ v = 9) ∨
    (u = 2 ∧ v = 5) ∨
    (u = 2 ∧ v = 9) ∨
    (u = 3 ∧ v = 4) ∨
    (u = 3 ∧ v = 8) ∨
    (u = 4 ∧ v = 7) ∨
    (u = 4 ∧ v = 8) ∨
    (u = 4 ∧ v = 9) ∨
    (u = 5 ∧ v = 6) ∨
    (u = 5 ∧ v = 8) ∨
    (u = 5 ∧ v = 9) ∨
    (u = 6 ∧ v = 7) ∨
    (u = 6 ∧ v = 8) ∨
    (u = 6 ∧ v = 9) ∨
    (u = 7 ∧ v = 8) ∨
    (u = 7 ∧ v = 9)

def graphWitnessRightRelation (u v : Fin 10) : Prop :=
  (u = 0 ∧ v = 6) ∨
    (u = 0 ∧ v = 8) ∨
    (u = 1 ∧ v = 7) ∨
    (u = 1 ∧ v = 9) ∨
    (u = 2 ∧ v = 5) ∨
    (u = 2 ∧ v = 9) ∨
    (u = 3 ∧ v = 4) ∨
    (u = 3 ∧ v = 8) ∨
    (u = 4 ∧ v = 6) ∨
    (u = 4 ∧ v = 8) ∨
    (u = 4 ∧ v = 9) ∨
    (u = 5 ∧ v = 7) ∨
    (u = 5 ∧ v = 8) ∨
    (u = 5 ∧ v = 9) ∨
    (u = 6 ∧ v = 7) ∨
    (u = 6 ∧ v = 8) ∨
    (u = 6 ∧ v = 9) ∨
    (u = 7 ∧ v = 8) ∨
    (u = 7 ∧ v = 9)

def explicitWitnessLeft : SimpleGraph (Fin 10) :=
  SimpleGraph.fromRel graphWitnessLeftRelation

def explicitWitnessRight : SimpleGraph (Fin 10) :=
  SimpleGraph.fromRel graphWitnessRightRelation

def equalityOfEverySummedPolynomialCardMoment : Prop :=
  sameCardPairProfileMultiset 10 explicitWitnessLeft explicitWitnessRight ∧
    ∀ {V W : Type*} [Fintype V] [Fintype W]
      [DecidableEq V] [DecidableEq W]
      (n : ℕ) (G : SimpleGraph V) (H : SimpleGraph W),
      Fintype.card V = n → Fintype.card W = n →
      sameCardPairProfileMultiset n G H →
        ∀ {R : Type*} [CommSemiring R]
          (P : MvPolynomial (PairProfileCoordinate n) R),
          (∑ v : V, cardProfilePolynomialMoment G v P) =
            ∑ v : W, cardProfilePolynomialMoment H v P

end

end MathlibPlus.Open.ResearchFormalization.Claim23126
