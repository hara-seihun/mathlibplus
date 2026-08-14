import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-- An isomorphism between two simple graphs on the same finite cardinality. -/
def graphIso {n : ℕ} (G H : SimpleGraph (Fin n)) : Prop :=
  ∃ e : Fin n ≃ Fin n, ∀ u v, G.Adj u v ↔ H.Adj (e u) (e v)

/-- The graph obtained by deleting vertex `i`, with the remaining vertices relabelled. -/
noncomputable def deleteVertex {n : ℕ} (G : SimpleGraph (Fin n)) (i : Fin n) :
    SimpleGraph (Fin (n - 1)) := by
  classical
  by_cases h : 0 < n
  · have hn : 1 ≤ n := h
    let e : (n - 1) + 1 = n := Nat.sub_add_cancel hn
    let j : Fin ((n - 1) + 1) := Fin.cast e.symm i
    exact
      { Adj := fun u v => G.Adj (Fin.cast e (j.succAbove u)) (Fin.cast e (j.succAbove v))
        symm := ⟨fun u v hv => G.symm.symm _ _ hv⟩
        loopless := ⟨fun u hu => G.loopless.irrefl _ hu⟩ }
  · have hn : n = 0 := Nat.eq_zero_of_not_pos h
    subst n
    exact Fin.elim0 i

/-- The multiplicity of a card in the full vertex deck. -/
noncomputable def fullVertexDeck {n : ℕ} (G : SimpleGraph (Fin n))
    (C : SimpleGraph (Fin (n - 1))) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => graphIso (deleteVertex G i) C)).card

/-- The reduced vertex deck is the support of the full deck. -/
def reducedVertexDeck {n : ℕ} (G : SimpleGraph (Fin n)) :
    Set (SimpleGraph (Fin (n - 1))) :=
  {C | fullVertexDeck G C ≠ 0}

/-- Claim 20411: equality of full vertex decks implies equality of reduced decks. -/
def claim20411 : Prop :=
  ∀ {n : ℕ} (G H : SimpleGraph (Fin n)),
    (∀ C, fullVertexDeck G C = fullVertexDeck H C) →
      reducedVertexDeck G = reducedVertexDeck H

/-- The degree of a vertex in a finite graph. -/
noncomputable def graphDegree {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : ℕ :=
  (G.neighborSet v).ncard

/-- The degree multiset of a finite graph. -/
noncomputable def degreeMultiset {n : ℕ} (G : SimpleGraph (Fin n)) : Multiset ℕ :=
  (Finset.univ : Finset (Fin n)).val.map (graphDegree G)

/-- The degree support of a finite graph. -/
def degreeSupport {n : ℕ} (G : SimpleGraph (Fin n)) : Set ℕ :=
  {d | d ∈ degreeMultiset G}

/-- The finite set of degrees occurring in a graph. -/
noncomputable def degreeValues {n : ℕ} (G : SimpleGraph (Fin n)) : Finset ℕ :=
  (Finset.univ : Finset (Fin n)).image (graphDegree G)

/-- The minimum degree, represented as an option for the empty graph. -/
noncomputable def degreeMinimum {n : ℕ} (G : SimpleGraph (Fin n)) : Option ℕ := by
  classical
  by_cases h : (degreeValues G).Nonempty
  · exact some ((degreeValues G).min' h)
  · exact none

/-- The maximum degree, represented as an option for the empty graph. -/
noncomputable def degreeMaximum {n : ℕ} (G : SimpleGraph (Fin n)) : Option ℕ := by
  classical
  by_cases h : (degreeValues G).Nonempty
  · exact some ((degreeValues G).max' h)
  · exact none

/-- Claim 20413: the full deck determines the degree multiset and its extrema/support. -/
def claim20413 : Prop :=
  ∀ {n : ℕ} (G H : SimpleGraph (Fin n)),
    (∀ C, fullVertexDeck G C = fullVertexDeck H C) →
      degreeMultiset G = degreeMultiset H ∧
        degreeMinimum G = degreeMinimum H ∧
        degreeMaximum G = degreeMaximum H ∧
        degreeSupport G = degreeSupport H

/-- Equality of full vertex decks. -/
def fullDeckEqual {n : ℕ} (G H : SimpleGraph (Fin n)) : Prop :=
  ∀ C, fullVertexDeck G C = fullVertexDeck H C

/-- Equality of reduced vertex decks. -/
def reducedDeckEqual {n : ℕ} (G H : SimpleGraph (Fin n)) : Prop :=
  reducedVertexDeck G = reducedVertexDeck H

/-- Reconstruction from the full vertex deck. -/
def reconstructibleFromFull {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ H, fullDeckEqual G H → graphIso G H

/-- Reconstruction from the reduced vertex deck. -/
def reconstructibleFromReduced {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ H, reducedDeckEqual G H → graphIso G H

/-- A graph contains a triangle. -/
def containsTriangle {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ a b c,
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c a

/-- A graph contains a four-cycle on four distinct vertices. -/
def containsFourCycle {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ a b c d,
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a

/-- Triangle-freeness. -/
def triangleFree {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ¬ containsTriangle G

/-- Four-cycle-freeness. -/
def fourCycleFree {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ¬ containsFourCycle G

/-- The complement of a simple graph. -/
def graphComplement {n : ℕ} (G : SimpleGraph (Fin n)) : SimpleGraph (Fin n) :=
  { Adj := fun u v => u ≠ v ∧ ¬ G.Adj u v
    symm := ⟨fun u v huv =>
      ⟨Ne.symm huv.1, fun h => huv.2 (G.symm.symm _ _ h)⟩⟩
    loopless := ⟨fun u huu => huu.1 rfl⟩ }

/-- All degrees lie in the indicated closed interval. -/
def degreesInRange {n : ℕ} (G : SimpleGraph (Fin n)) (lo hi : ℕ) : Prop :=
  ∀ v, lo ≤ graphDegree G v ∧ graphDegree G v ≤ hi

/-- The degree support lies in a specified set. -/
def degreeSupportIn {n : ℕ} (G : SimpleGraph (Fin n)) (s : Set ℕ) : Prop :=
  degreeSupport G ⊆ s

/-- Claim 20414: every finite disconnected graph is reconstructible from its vertex deck. -/
def claim20414 : Prop :=
  ∀ {n : ℕ} (G : SimpleGraph (Fin n)),
    ¬ G.Connected → reconstructibleFromFull G

/-- Claim 20416: triangle-free graphs through order sixteen are reduced-deck reconstructible. -/
def claim20416 : Prop :=
  ∀ {n : ℕ} (G : SimpleGraph (Fin n)),
    n ≤ 16 → triangleFree G → reconstructibleFromReduced G

/-- Claim 20417: four-cycle-free graphs through order nineteen are reduced-deck reconstructible. -/
def claim20417 : Prop :=
  ∀ {n : ℕ} (G : SimpleGraph (Fin n)),
    n ≤ 19 → fourCycleFree G → reconstructibleFromReduced G

/-- Claim 20418: a nonisomorphic full-deck-equal pair on fourteen vertices has
triangles and four-cycles on both sides. -/
def claim20418 : Prop :=
  ∀ (G H : SimpleGraph (Fin 14)),
    fullDeckEqual G H → ¬ graphIso G H →
      containsTriangle G ∧ containsFourCycle G ∧
      containsTriangle H ∧ containsFourCycle H

/-- Claim 20419: the bounded-degree reconstruction result and its order-fourteen
counterexample degree bounds. -/
def claim20419 : Prop :=
  (∀ {n : ℕ} (G : SimpleGraph (Fin n)),
      n ≤ 14 → degreesInRange G 0 5 → reconstructibleFromFull G) ∧
  (∀ (G H : SimpleGraph (Fin 14)),
      fullDeckEqual G H → ¬ graphIso G H →
        (∃ d, degreeMaximum G = some d ∧ 6 ≤ d) ∧
        (∃ d, degreeMaximum H = some d ∧ 6 ≤ d) ∧
        (∃ d, degreeMinimum G = some d ∧ d ≤ 7) ∧
        (∃ d, degreeMinimum H = some d ∧ d ≤ 7) ∧
        (∀ d, degreeMinimum G = some d → 8 ≤ d →
          degreesInRange (graphComplement G) 0 5 ∧
          reconstructibleFromFull (graphComplement G)) ∧
        (∀ d, degreeMinimum H = some d → 8 ≤ d →
          degreesInRange (graphComplement H) 0 5 ∧
          reconstructibleFromFull (graphComplement H)))

/-- Claim 20420: the three stated order-fourteen degree bands are reconstructible. -/
def claim20420 : Prop :=
  ∀ (G : SimpleGraph (Fin 14)),
    (degreeSupportIn G ({5, 6} : Set ℕ) ∨
      degreeSupportIn G ({6, 7} : Set ℕ) ∨
      degreeSupportIn G ({7, 8} : Set ℕ)) →
      reconstructibleFromFull G

/-- Claim 20422: all graphs through order thirteen are reduced-deck reconstructible. -/
def claim20422 : Prop :=
  ∀ {n : ℕ} (G : SimpleGraph (Fin n)),
    n ≤ 13 → reconstructibleFromReduced G

end MathlibPlus.Open.ResearchFormalizationBatch
