import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- The quotient differences whose binary fiber of a connection set has exactly one point. -/
noncomputable def markedQuotientConnection (H : Type*)
    (S : Set (H × ZMod 2)) : Set H := by
  classical
  exact {h |
    Set.ncard (({(h, (0 : ZMod 2)), (h, (1 : ZMod 2))} : Set (H × ZMod 2)) ∩ S) = 1}

/-- The inter-block adjacency matrix belonging to a quotient difference. -/
def interBlockAdjacency (H : Type*) (S : Set (H × ZMod 2)) (h : H) :
    Matrix (ZMod 2) (ZMod 2) Prop :=
  fun i j => (h, j - i) ∈ S

/-- The four binary inter-block matrices. -/
def zeroBlockMatrix : Matrix (ZMod 2) (ZMod 2) Prop := fun _ _ => False

def fullBlockMatrix : Matrix (ZMod 2) (ZMod 2) Prop := fun _ _ => True

def identityBlockMatrix : Matrix (ZMod 2) (ZMod 2) Prop := fun i j => i = j

def swapBlockMatrix : Matrix (ZMod 2) (ZMod 2) Prop := fun i j => i ≠ j

/-- Formal statement of the marked quotient connection-graph description. -/
def markedQuotientConnectionGraph : Prop :=
  ∀ (H : Type*) [AddGroup H] (S : Set (H × ZMod 2)) (h : H),
    (h ∈ markedQuotientConnection H S ↔
      interBlockAdjacency H S h = identityBlockMatrix ∨
        interBlockAdjacency H S h = swapBlockMatrix) ∧
    (h ∉ markedQuotientConnection H S ↔
      interBlockAdjacency H S h = zeroBlockMatrix ∨
        interBlockAdjacency H S h = fullBlockMatrix)

end MathlibPlus.Open.ResearchFormalization
