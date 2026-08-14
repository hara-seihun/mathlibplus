import Mathlib

noncomputable section

namespace MathlibPlus.Open.Research.RootCards

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open scoped BigOperators

def endpointOutside (x y : Fin 4) : Finset (Fin 4) :=
  Finset.univ.filter (fun z => z ≠ x ∧ z ≠ y)

def markedEndpointBlockRow
    (G : SimpleGraph (Fin 4)) (x y : Fin 4) : Bool × ℕ × ℕ :=
  (decide (G.Adj x y),
    (endpointOutside x y).filter (fun z => G.Adj x z) |>.card,
    (endpointOutside x y).filter (fun z => G.Adj y z) |>.card)

def markedEndpointBlockRows : Finset (Bool × ℕ × ℕ) :=
  ((Finset.univ : Finset (SimpleGraph (Fin 4))).biUnion (fun G =>
    (((Finset.univ : Finset (Fin 4)).product
        (Finset.univ : Finset (Fin 4))).filter (fun xy => xy.1 ≠ xy.2)).image
      (fun xy => markedEndpointBlockRow G xy.1 xy.2)))

def markedTwoRootEndpointBlockRow_count : Prop :=
  markedEndpointBlockRows.card = 18

end MathlibPlus.Open.Research.RootCards
