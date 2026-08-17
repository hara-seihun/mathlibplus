import Mathlib

namespace MathlibPlus.Open.NewResearch2.R0608SelectedComponentExpansion

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The formal power-sum carrier with disjoint A and B alphabet coordinates. -/
abbrev TwoAlphabetPowerSums26356 := MvPolynomial (Fin 2 × ℕ) ℚ

private def sideIndex26356 (side : Fin 2) (k : ℕ) : Fin 2 × ℕ :=
  (side, k)

/-- The graph formed by a selected finite edge set. -/
private def selectedEdgeGraph26356 {V : Type*}
    (F : Finset (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromRel (fun v w => s(v, w) ∈ F)

/-- The signed component product in one alphabet side. -/
private noncomputable def componentProduct26356
    {V : Type*} [Fintype V]
    (side : Fin 2) (G : SimpleGraph V) : TwoAlphabetPowerSums26356 :=
  ∏ C : G.ConnectedComponent,
    MvPolynomial.X (sideIndex26356 side C.supp.ncard)

/-- The chromatic power-sum expansion on one of the two disjoint alphabet
sides. -/
private noncomputable def chromaticPowerSumSide26356
    {V : Type*} [Fintype V] [DecidableEq V]
    (side : Fin 2) (G : SimpleGraph V) : TwoAlphabetPowerSums26356 :=
  ∑ F ∈ G.edgeFinset.powerset,
    (-1 : TwoAlphabetPowerSums26356) ^ F.card *
      componentProduct26356 side (selectedEdgeGraph26356 F)

/-- The selected root component is forced to the A side. -/
private noncomputable def rootComponentFactor26356
    {V : Type*} [Fintype V] (r : V) (F : Finset (Sym2 V)) :
    TwoAlphabetPowerSums26356 :=
  MvPolynomial.X (sideIndex26356 0
    (((selectedEdgeGraph26356 F).connectedComponentMk r).supp.ncard))

/-- Every nonroot selected component independently chooses A or B. -/
private noncomputable def nonrootComponentFactor26356
    {V : Type*} [Fintype V] (r : V) (F : Finset (Sym2 V)) :
    TwoAlphabetPowerSums26356 :=
  let H := selectedEdgeGraph26356 F
  let root := H.connectedComponentMk r
  ∏ C ∈ (Finset.univ.filter
    (fun C : H.ConnectedComponent => C ≠ root)),
      (MvPolynomial.X (sideIndex26356 0 C.supp.ncard) +
        MvPolynomial.X (sideIndex26356 1 C.supp.ncard))

private def deletedGraph26356 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : SimpleGraph {v // v ∉ S} :=
  G.induce {v : V | v ∉ S}

private def inducedGraph26356 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : SimpleGraph {v // v ∈ S} :=
  G.induce (S : Set V)

/-- The rooted two-alphabet chromatic symmetric function in the formal
power-sum carrier: the root is in the A-side complement, and S is the
B-side. -/
private noncomputable def rootedTwoAlphabetPowerSum26356
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) : TwoAlphabetPowerSums26356 :=
  ∑ S ∈ ((Finset.univ : Finset V).filter (fun v => v ≠ r)).powerset,
    chromaticPowerSumSide26356 0 (deletedGraph26356 G S) *
      chromaticPowerSumSide26356 1 (inducedGraph26356 G S)

/-- Evaluation in two finite disjoint alphabets, retaining the source's
finite-set carrier. -/
def alphabetEvaluation26356 (A B : Finset ℕ)
    (P : TwoAlphabetPowerSums26356) : ℚ :=
  MvPolynomial.eval₂ (algebraMap ℚ ℚ)
    (fun v => if v.1 = 0 then (A.card : ℚ) else (B.card : ℚ)) P

/-- Claim 26356: the exact rooted two-alphabet chromatic function equals its
signed selected-edge expansion.  The formal side tags are the disjoint A and
B alphabets, so the root component uses A and every other component chooses
A or B; the finite-alphabet specialization is retained with its disjointness
hypothesis. -/
def claim26356 : Prop :=
  (∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V),
    rootedTwoAlphabetPowerSum26356 G r =
      ∑ F ∈ G.edgeFinset.powerset,
        (-1 : TwoAlphabetPowerSums26356) ^ F.card *
          rootComponentFactor26356 r F *
          nonrootComponentFactor26356 r F) ∧
    (∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (r : V) (A B : Finset ℕ),
      Disjoint A B →
        alphabetEvaluation26356 A B (rootedTwoAlphabetPowerSum26356 G r) =
          alphabetEvaluation26356 A B
            (∑ F ∈ G.edgeFinset.powerset,
              (-1 : TwoAlphabetPowerSums26356) ^ F.card *
                rootComponentFactor26356 r F *
                nonrootComponentFactor26356 r F))

end

end MathlibPlus.Open.NewResearch2.R0608SelectedComponentExpansion
