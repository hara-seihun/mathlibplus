import Mathlib

namespace MathlibPlus.Open.Research.R0384

noncomputable section

/-- A fixed-point-free involution on a vertex type. -/
def fixedPointFreeInvolution {V : Type} (ι : Equiv.Perm V) : Prop :=
  (∀ v, ι (ι v) = v) ∧ ∀ v, ι v ≠ v

/-- The two fibers are distinct. -/
def distinctVertexFibers {V : Type} (ι : Equiv.Perm V) (a b : V) : Prop :=
  ({a, ι a} : Set V) ≠ {b, ι b}

/-- The edge set obtained by replacing an invariant matching by its crossed
matching and leaving every other edge untouched. -/
def switchedEdgeSet {V : Type} (ι : Equiv.Perm V) (a b : V)
    (G : SimpleGraph V) : Set (Sym2 V) :=
  (G.edgeSet \ {Sym2.mk a b, Sym2.mk (ι a) (ι b)}) ∪
    {Sym2.mk a (ι b), Sym2.mk (ι a) b}

/-- One-edge two-lift sign flip. -/
def oneEdgeTwoLiftSignFlip {V : Type} (ι : Equiv.Perm V) (a b : V)
    (G : SimpleGraph V) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (switchedEdgeSet ι a b G)

/-- The construction under the stated fixed-point-free, distinct-fiber, and
invariant-matching hypotheses. -/
def oneEdgeSwitchConstruction : Prop :=
  ∀ {V : Type} (ι : Equiv.Perm V) (a b : V)
    (G : SimpleGraph V),
    fixedPointFreeInvolution ι → distinctVertexFibers ι a b →
      ({Sym2.mk a b, Sym2.mk (ι a) (ι b)} : Set (Sym2 V)) ⊆ G.edgeSet →
        let H := oneEdgeTwoLiftSignFlip ι a b G
        H.edgeSet = switchedEdgeSet ι a b G

end
end MathlibPlus.Open.Research.R0384
