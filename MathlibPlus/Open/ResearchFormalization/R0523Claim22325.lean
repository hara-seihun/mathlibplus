import MathlibPlus.Open.ResearchFormalization.R0523Claim22338

open scoped BigOperators
open Classical
attribute [local instance] Classical.propDecidable Classical.decEq

namespace MathlibPlus.Open.ResearchFormalization.R0523Claim22325

noncomputable section

open MathlibPlus.Open.ResearchFormalizationBatch
open MathlibPlus.Open.ResearchFormalization.R0523Claim22338

abbrev ShiftedPolynomial := MvPolynomial (Option ℕ) ℤ

def zVariable : ShiftedPolynomial := MvPolynomial.X none

def cutComponentFactor {V : Type*} [Fintype V] [DecidableEq V]
    (B : SimpleGraph V) (A : Finset (↥B.edgeSet))
    (C : (selectedSpanningGraph B A).ConnectedComponent) : ShiftedPolynomial :=
  yVariable (selectedComponentSize B A C) -
    zVariable ^ selectedComponentSize B A C

noncomputable def cutTerm {V : Type*} [Fintype V] [DecidableEq V]
    (B : SimpleGraph V) (r : V) (A : Finset (↥B.edgeSet)) : ShiftedPolynomial :=
  letI : Fintype (selectedSpanningGraph B A).ConnectedComponent :=
    Fintype.ofFinite _
  yVariable (selectedComponentSize B A
      (SimpleGraph.connectedComponentMk (selectedSpanningGraph B A) r)) *
    ∏ C ∈ (Finset.univ : Finset
      (selectedSpanningGraph B A).ConnectedComponent).filter
        (fun C => C ≠
          SimpleGraph.connectedComponentMk (selectedSpanningGraph B A) r),
      cutComponentFactor B A C

noncomputable def cutExpansion {V : Type*} [Fintype V] [DecidableEq V]
    (B : SimpleGraph V) (r : V) : ShiftedPolynomial :=
  letI : Fintype (↥B.edgeSet) := Fintype.ofFinite _
  ∑ A ∈ (Finset.univ : Finset (↥B.edgeSet)).powerset,
    cutTerm B r A

/-- The shifted rooted factor is the cut expansion over the actual selected
edge-subset component carrier, including the root component and every other
component. -/
def claim22325 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (B : SimpleGraph V) (r : V),
    B.IsTree →
      shiftedRootedFactor B r = cutExpansion B r

end

end MathlibPlus.Open.ResearchFormalization.R0523Claim22325
