import Mathlib

namespace MathlibPlus.Combinatorics

/-- A cycle in a finite simple graph forces three distinct edges. -/
theorem edgeFinset_card_ge_three_of_cycle_claim29423
    {V : Type*} [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    {v : V} (w : G.Walk v v) (hw : w.IsCycle) :
    3 ≤ G.edgeFinset.card := by
  exact hw.three_le_length.trans
    (hw.1.1.length_le_card_edgeFinset)

/-- Abstract incidence double counting: if every left object is incident to at least
three right objects and every right object to exactly `c` left objects, then the
number of incidences gives the displayed lower bound. -/
theorem incidence_double_count_lower_bound_claim29423
    {L R : Type*} [Fintype L] [Fintype R]
    (inc : L → R → Prop) [DecidableRel inc] (c : ℕ)
    (hL : ∀ l : L, 3 ≤ (Finset.univ.filter (inc l)).card)
    (hR : ∀ r : R, (Finset.univ.filter (fun l => inc l r)).card = c) :
    Fintype.card L * 3 ≤ Fintype.card R * c := by
  have h := Finset.card_mul_le_card_mul (r := inc)
    (s := (Finset.univ : Finset L)) (t := (Finset.univ : Finset R))
    (m := 3) (n := c)
    (fun l _ => by simpa [Finset.bipartiteAbove] using hL l)
    (fun r _ => by simpa [Finset.bipartiteBelow] using (hR r).le)
  simpa using h

/-- The local first step of the five-set argument: a cycle in every induced
five-vertex subgraph supplies the three-edge hypothesis used by double counting. -/
theorem every_five_vertex_induced_cycle_gives_three_edges_claim29423
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hcycle : ∀ s : Finset V, s.card = 5 →
      ∃ (v : (↑s : Set V)),
        ∃ w : (G.induce (↑s : Set V)).Walk v v, w.IsCycle) :
    ∀ s : Finset V, s.card = 5 →
      3 ≤ (G.induce (↑s : Set V)).edgeSet.ncard := by
  intro s hs
  obtain ⟨v, w, hw⟩ := hcycle s hs
  letI : Finite (G.induce (↑s : Set V)).edgeSet :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (G.induce (↑s : Set V)).edgeSet := Fintype.ofFinite _
  have h := edgeFinset_card_ge_three_of_cycle_claim29423
    (G := G.induce (↑s : Set V)) w hw
  rw [Set.ncard_eq_toFinset_card]
  simpa [SimpleGraph.edgeFinset] using h

end MathlibPlus.Combinatorics

namespace MathlibPlus.Open.GraphTheory

/-! Statement-fidelity registry node for admitted claim 29423.  The source does
not separately name the cycle predicate or the edge/five-set incidence map;
the node keeps the induced-subgraph cycle predicate explicit and writes the
ceiling as natural-number division by twenty after adding nineteen. -/

def threeEdgesPerFiveSetLowerBound_claim29423 : Prop :=
  ∀ (m : ℕ), 5 ≤ m →
    ∀ (G : SimpleGraph (Fin m)) [Fintype G.edgeSet],
      (∀ s : Finset (Fin m), s.card = 5 →
        ∃ (v : (↑s : Set (Fin m))),
          ∃ w : (G.induce (↑s : Set (Fin m))).Walk v v, w.IsCycle) →
      G.edgeFinset.card * Nat.choose (m - 2) 3 ≥
          3 * Nat.choose m 5 ∧
        G.edgeFinset.card ≥ (3 * m * (m - 1) + 19) / 20

end MathlibPlus.Open.GraphTheory
