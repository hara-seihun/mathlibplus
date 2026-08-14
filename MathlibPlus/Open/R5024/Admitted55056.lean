import Mathlib

namespace MathlibPlus.Open.R5024

/-- The undirected adjacency relation underlying an oriented edge presentation. -/
def underlyingAdjacency {V E : Type*}
    (tail head : E → V) (v w : V) : Prop :=
  ∃ e, (tail e = v ∧ head e = w) ∨ (tail e = w ∧ head e = v)

def graphConnected {V E : Type*}
    (tail head : E → V) : Prop :=
  ∀ v w, Relation.ReflTransGen (underlyingAdjacency tail head) v w

def coboundaryKernel {V E : Type*}
    (tail head : E → V) : Set (V → ℚ) :=
  {f | ∀ e, f (head e) - f (tail e) = 0}

def diagonalCopySpace {V : Type*} : Set (V → ℚ) :=
  {f | ∀ v w, f v = f w}

def familyCoboundaryKernel
    {ι : Type*} {V E : ι → Type*}
    (tail : ∀ c, E c → V c) (head : ∀ c, E c → V c) :
    Set (∀ c, V c → ℚ) :=
  {f | ∀ c e, f c (head c e) - f c (tail c e) = 0}

def familyDiagonalCopySpace
    {ι : Type*} {V : ι → Type*} : Set (∀ c, V c → ℚ) :=
  {f | ∀ c v w, f c v = f c w}

/-- Claim 55056: the direct-sum coboundary kernel is exactly typed diagonal
synchronization precisely when every oriented presentation is connected, and a
disconnected presentation supplies a counterfeit component-constant state. -/
def coboundarySynchronization_55056
    {ι : Type*} {V E : ι → Type*}
    (tail : ∀ c, E c → V c) (head : ∀ c, E c → V c) : Prop :=
  ((∀ c, graphConnected (tail c) (head c)) ↔
    familyCoboundaryKernel tail head = familyDiagonalCopySpace) ∧
  (∀ c, ¬ graphConnected (tail c) (head c) →
    ∃ f : V c → ℚ,
      f ∈ coboundaryKernel (tail c) (head c) ∧
        f ∉ diagonalCopySpace)

end MathlibPlus.Open.R5024
