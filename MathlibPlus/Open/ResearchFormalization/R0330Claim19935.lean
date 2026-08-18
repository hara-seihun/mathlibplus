import MathlibPlus.Open.ResearchFormalization.R0330Claim19947

namespace MathlibPlus.Open.ResearchFormalization.R0330Claim19935

noncomputable section
open Classical
open scoped BigOperators

/-- The number of connected components of a finite graph, using the graph's
standard connected-component carrier. -/
noncomputable def componentCount {V : Type} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  letI : Fintype G.ConnectedComponent := Fintype.ofFinite _
  Fintype.card G.ConnectedComponent

/-- The vertex-deleted card is the induced graph on the complement of the
singleton vertex set, with the exact carrier used by the deck transform. -/
 def vertexDeletedCard {n : ℕ} (T : SimpleGraph (Fin n)) (v : Fin n) :
    SimpleGraph {w : Fin n // w ∉ ({v} : Finset (Fin n))} :=
  MathlibPlus.Open.ResearchFormalization.R0330Claim19947.deletedGraph T
    ({v} : Finset (Fin n))

/-- Claim 19935: in a finite tree, the degree at a vertex is the number of
connected components of its vertex-deleted card.  Consequently the y-power
attached to that card can use the degree as its exponent. -/
def claim19935 : Prop :=
  ∀ {n : ℕ} (T : SimpleGraph (Fin n)), T.IsTree →
    ∀ v : Fin n,
      T.degree v = componentCount (vertexDeletedCard T v) ∧
      (MvPolynomial.X
          (MathlibPlus.Open.ResearchFormalization.R0330Claim19947.yVar 2) :
          MvPolynomial
            (MathlibPlus.Open.ResearchFormalization.R0330Claim19947.DeckVar 2)
            ℤ) ^ T.degree v =
        (MvPolynomial.X
          (MathlibPlus.Open.ResearchFormalization.R0330Claim19947.yVar 2) :
          MvPolynomial
            (MathlibPlus.Open.ResearchFormalization.R0330Claim19947.DeckVar 2)
            ℤ) ^ componentCount (vertexDeletedCard T v)

end
end MathlibPlus.Open.ResearchFormalization.R0330Claim19935
