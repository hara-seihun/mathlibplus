import Mathlib

namespace MathlibPlus.Open.Research.RookGraphs

abbrev H7 := ZMod 7 × ZMod 7

/-- The connection set of the rook graph in additive coordinates. -/
def rookConnection : Set H7 :=
  {v | (v.1 ≠ 0 ∧ v.2 = 0) ∨ (v.1 = 0 ∧ v.2 ≠ 0)}

def cayleyAdjacency (X : Set H7) (u v : H7) : Prop :=
  v - u ∈ X

def rookAdjacency (u v : H7) : Prop :=
  (u.1 = v.1 ∧ u.2 ≠ v.2) ∨ (u.2 = v.2 ∧ u.1 ≠ v.1)

/-- The explicit connection set has the adjacency relation of `K₇ □ K₇`. -/
def claim28533 : Prop :=
  ∀ u v : H7, cayleyAdjacency rookConnection u v ↔ rookAdjacency u v

noncomputable section

def e7 : H7 := (1, 2)
def f7 : H7 := (1, 4)

def basisMap (u : H7) : H7 := u.1 • e7 + u.2 • f7

def complementaryConnection : Set H7 :=
  {v | ∃ a b : ZMod 7, a ≠ 0 ∧ b ≠ 0 ∧ v = basisMap (a, b)}

def complementaryAdjacency (u v : H7) : Prop :=
  u ≠ v ∧ ¬rookAdjacency u v

/-- The displayed basis gives the complementary rook graph in the new
coordinates. -/
def claim28534 : Prop :=
  (∀ v : H7, ∃! a : ZMod 7, ∃! b : ZMod 7, v = basisMap (a, b)) ∧
    ∀ u v : H7,
      cayleyAdjacency complementaryConnection (basisMap u) (basisMap v) ↔
        complementaryAdjacency u v

end
end MathlibPlus.Open.Research.RookGraphs
