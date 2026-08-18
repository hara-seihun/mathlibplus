import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0608Claim26358Repair

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Universal power-sum coordinates for two formally disjoint alphabets. -/
abbrev TwoAlphabetPowerSums26358 := MvPolynomial (Fin 2 × ℕ) ℚ

private def sideIndex26358 (side : Fin 2) (k : ℕ) : Fin 2 × ℕ :=
  (side, k)

private def selectedEdgeGraph26358 {V : Type*}
    (F : Finset (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromRel (fun v w => s(v, w) ∈ F)

private noncomputable def componentProduct26358
    {V : Type*} [Fintype V]
    (side : Fin 2) (G : SimpleGraph V) : TwoAlphabetPowerSums26358 :=
  ∏ C : G.ConnectedComponent,
    MvPolynomial.X (sideIndex26358 side C.supp.ncard)

/-- The ordinary chromatic symmetric function in one tagged alphabet, in
Stanley's signed power-sum expansion. -/
private noncomputable def chromaticPowerSumSide26358
    {V : Type*} [Fintype V] [DecidableEq V]
    (side : Fin 2) (G : SimpleGraph V) : TwoAlphabetPowerSums26358 :=
  ∑ F ∈ G.edgeFinset.powerset,
    (-1 : TwoAlphabetPowerSums26358) ^ F.card *
      componentProduct26358 side (selectedEdgeGraph26358 F)

private def deletedGraph26358
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : SimpleGraph {v // v ∉ S} :=
  G.induce {v : V | v ∉ S}

private def inducedGraph26358
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : SimpleGraph {v // v ∈ S} :=
  G.induce (S : Set V)

/-- The `χ_B` crossing companion stores B (side 1) on the root-containing
complement of the selected subset. -/
private noncomputable def rootCrossingCompanion26358
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (_r : V) : Finset V → TwoAlphabetPowerSums26358 :=
  fun S => chromaticPowerSumSide26358 1 (deletedGraph26358 G S)

/-- Scalar character evaluation by A (side 0) of the `χ_B` crossing
companion, without collapsing either alphabet to its cardinality. -/
private noncomputable def evaluateRootCrossing26358
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) : TwoAlphabetPowerSums26358 :=
  ∑ S ∈ ((Finset.univ : Finset V).filter (fun v => v ≠ r)).powerset,
    chromaticPowerSumSide26358 0 (inducedGraph26358 G S) *
      rootCrossingCompanion26358 G r S

/-- The rooted two-alphabet chromatic function with a specified root side and
selected side. -/
private noncomputable def rootedTwoAlphabetOrientation26358
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V)
    (rootSide selectedSide : Fin 2) : TwoAlphabetPowerSums26358 :=
  ∑ S ∈ ((Finset.univ : Finset V).filter (fun v => v ≠ r)).powerset,
    chromaticPowerSumSide26358 rootSide (deletedGraph26358 G S) *
      chromaticPowerSumSide26358 selectedSide (inducedGraph26358 G S)

/-- Claim 26358: evaluating the `χ_B` root-crossing companion by `χ_A` is
exactly the swapped rooted orientation `X^bullet[B|A]`. The conclusion lives
in the universal two-alphabet power-sum ring, so it retains color weights
rather than only the two alphabet cardinalities. -/
def claim26358_rootCrossingSwappedOrientation : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V),
    evaluateRootCrossing26358 G r =
      rootedTwoAlphabetOrientation26358 G r 1 0

end

end MathlibPlus.Open.ResearchFormalization.R0608Claim26358Repair
