import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- The twelve edges of the graph on vertices `0,…,7` in the admitted witness. -/
def graphCEdges : Set (Sym2 (Fin 8)) :=
  {s(0, 3), s(0, 4), s(0, 7), s(1, 4), s(1, 5), s(1, 6),
    s(2, 5), s(2, 6), s(2, 7), s(3, 6), s(3, 7), s(5, 7)}
def graphC : SimpleGraph (Fin 8) := SimpleGraph.fromEdgeSet graphCEdges

/-- The two nine-vertex leaf extensions of the admitted base graph. -/
def graphG3Edges : Set (Sym2 (Fin 9)) :=
  {s(0, 3), s(0, 4), s(0, 7), s(1, 4), s(1, 5), s(1, 6),
    s(2, 5), s(2, 6), s(2, 7), s(3, 6), s(3, 7), s(5, 7), s(3, 8)}
def graphG5Edges : Set (Sym2 (Fin 9)) :=
  {s(0, 3), s(0, 4), s(0, 7), s(1, 4), s(1, 5), s(1, 6),
    s(2, 5), s(2, 6), s(2, 7), s(3, 6), s(3, 7), s(5, 7), s(5, 8)}
def graphG3 : SimpleGraph (Fin 9) := SimpleGraph.fromEdgeSet graphG3Edges
def graphG5 : SimpleGraph (Fin 9) := SimpleGraph.fromEdgeSet graphG5Edges

/-- Exact construction of the base graph and its two specified leaf extensions. -/
def claim13986 : Prop :=
  graphC.edgeSet = graphCEdges ∧
    graphG3.edgeSet = graphG3Edges ∧
    graphG5.edgeSet = graphG5Edges

/-- The two explicit nine-vertex leaf extensions are nonisomorphic. -/
def claim13987 : Prop := ¬Nonempty (SimpleGraph.Iso graphG3 graphG5)

end MathlibPlus.Open.ResearchFormalization
