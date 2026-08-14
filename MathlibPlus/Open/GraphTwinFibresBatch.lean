import Mathlib

namespace MathlibPlus.Open.GraphTwinFibres

universe u

/-- Equality of open neighborhoods in a simple graph. -/
def sameOpenNeighborhood {V : Type u} (G : SimpleGraph V) (x y : V) : Prop :=
  ∀ z : V, G.Adj x z ↔ G.Adj y z

/-- Equality of closed neighborhoods in a simple graph. -/
def sameClosedNeighborhood {V : Type u} (G : SimpleGraph V) (x y : V) : Prop :=
  ∀ z : V, (z = x ∨ G.Adj x z) ↔ (z = y ∨ G.Adj y z)

/-- No two distinct quotient vertices are false twins. -/
def noFalseTwins {V : Type u} (G : SimpleGraph V) : Prop :=
  ∀ ⦃x y : V⦄, sameOpenNeighborhood G x y → x = y

/-- No two distinct quotient vertices are true twins. -/
def noTrueTwins {V : Type u} (G : SimpleGraph V) : Prop :=
  ∀ ⦃x y : V⦄, sameClosedNeighborhood G x y → x = y

/-- Claim 57678: open twin classes in the independent two-point lift are the fibres. -/
def claim_57678 {V : Type u} (G : SimpleGraph V) : Prop :=
  noFalseTwins G →
    ∀ (x y : V) (i j : Bool),
      (∀ (z : V) (_k : Bool), G.Adj x z ↔ G.Adj y z) ↔ x = y

/-- Claim 57681: closed twin classes in the clique two-point lift are the fibres. -/
def claim_57681 {V : Type u} (G : SimpleGraph V) : Prop :=
  noTrueTwins G →
    ∀ (x y : V) (i j : Bool),
      (∀ (z : V) (_k : Bool),
        (z = x ∨ G.Adj x z) ↔ (z = y ∨ G.Adj y z)) ↔ x = y

end MathlibPlus.Open.GraphTwinFibres
