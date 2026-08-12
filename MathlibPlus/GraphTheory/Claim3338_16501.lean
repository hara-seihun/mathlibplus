import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

namespace MathlibPlus.GraphTheory

/-- The edge count forced by 43 vertices and regular degree 18. -/
theorem regular_edge_count_claim3338
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (hcard : Fintype.card V = 43)
    (hreg : G.IsRegularOfDegree 18) :
    G.edgeFinset.card = 387 := by
  have hsum := G.sum_degrees_eq_twice_card_edges
  rw [show (∑ v, G.degree v) = 43 * 18 by
    simp_rw [hreg.degree_eq]
    simp [hcard]] at hsum
  omega

/-- Complementation of an SRG, with Mathlib's canonical natural-number
subtraction presentation of the transformed parameters. -/
theorem complement_strongly_regular_claim16501
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    {v k lam mu : ℕ} (h : G.IsSRGWith v k lam mu) :
    Gᶜ.IsSRGWith v (v - k - 1) (v - (2 * k - mu) - 2) (v - (2 * k - lam)) := by
  exact h.compl

end MathlibPlus.GraphTheory
