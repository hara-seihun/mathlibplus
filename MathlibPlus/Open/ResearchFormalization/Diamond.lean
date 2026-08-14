import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Diamond

abbrev DiamondState := ℤ × ℤ

def diamondS : DiamondState := (0, 0)
def diamondA : DiamondState := (1, 1)
def diamondB : DiamondState := (0, 1)
def diamondT : DiamondState := (1, 0)

def secondCoordinateResponse (p q : DiamondState) : ℤ := q.2 - p.2

def diamondPathSum (response : DiamondState → DiamondState → ℤ)
    (middle : DiamondState) : ℤ :=
  response diamondS middle + response middle diamondT

def edgeLocalMarker (p q : DiamondState) : ℤ :=
  if p = diamondS ∧ q = diamondA then 1 else 0

def factorsThroughVertexStateRow
    (marker : DiamondState → DiamondState → ℤ) : Prop :=
  ∃ row : DiamondState → ℤ,
    marker diamondS diamondA = row diamondA - row diamondS ∧
    marker diamondA diamondT = row diamondT - row diamondA ∧
    marker diamondS diamondB = row diamondB - row diamondS ∧
    marker diamondB diamondT = row diamondT - row diamondB

/-- The diamond witness separating a vertex-state telescoping row from an
edge-local marker. -/
def ExactDiamondWitness : Prop :=
  secondCoordinateResponse diamondS diamondA = 1 ∧
  secondCoordinateResponse diamondA diamondT = -1 ∧
  secondCoordinateResponse diamondS diamondB = 1 ∧
  secondCoordinateResponse diamondB diamondT = -1 ∧
  secondCoordinateResponse diamondS diamondA ≠ 0 ∧
  secondCoordinateResponse diamondA diamondT ≠ 0 ∧
  secondCoordinateResponse diamondS diamondB ≠ 0 ∧
  secondCoordinateResponse diamondB diamondT ≠ 0 ∧
  diamondPathSum secondCoordinateResponse diamondA = 0 ∧
  diamondPathSum secondCoordinateResponse diamondB = 0 ∧
  diamondPathSum edgeLocalMarker diamondA = 1 ∧
  diamondPathSum edgeLocalMarker diamondB = 0 ∧
  ¬ factorsThroughVertexStateRow edgeLocalMarker

end MathlibPlus.Open.ResearchFormalization.Diamond
