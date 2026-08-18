import Mathlib

namespace MathlibPlus.Open.NewResearch2.R0608Claim26358Repair

noncomputable section

open scoped BigOperators
open scoped Sym2
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev RootedSplitIndex (V : Type*) (r : V) := {S : Finset V // r ∉ S}

noncomputable def chromaticCharacter
    {α V : Type*} [Fintype V] [DecidableEq V]
    [Fintype α] [DecidableEq α]
    (G : SimpleGraph V) (A : Finset α) : MvPolynomial α ℚ :=
  ∑ f : V → α,
    if (∀ v, f v ∈ A) ∧
        (∀ ⦃v w⦄, G.Adj v w → f v ≠ f w) then
      ∏ v : V, MvPolynomial.X (f v)
    else 0

noncomputable def deletedGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : SimpleGraph {v // v ∉ S} :=
  G.induce {v : V | v ∉ S}

noncomputable def inducedGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : SimpleGraph {v // v ∈ S} :=
  G.induce (S : Set V)

noncomputable def rootedTwoAlphabetChromatic
    {α V : Type*} [Fintype V] [DecidableEq V]
    [Fintype α] [DecidableEq α]
    (G : SimpleGraph V) (r : V) (B A : Finset α) : MvPolynomial α ℚ :=
  ∑ i : RootedSplitIndex V r,
    chromaticCharacter (deletedGraph G i.1) B *
      chromaticCharacter (inducedGraph G i.1) A

noncomputable def rootCrossingCompanion
    {α V : Type*} [Fintype V] [DecidableEq V]
    [Fintype α] [DecidableEq α]
    (G : SimpleGraph V) (r : V) (B : Finset α) :
    RootedSplitIndex V r →₀ MvPolynomial α ℚ :=
  ∑ i : RootedSplitIndex V r,
    Finsupp.single i (chromaticCharacter (deletedGraph G i.1) B)

noncomputable def scalarEvaluateRootCrossing
    {α V : Type*} [Fintype V] [DecidableEq V]
    [Fintype α] [DecidableEq α]
    (G : SimpleGraph V) (r : V) (A : Finset α)
    (K : RootedSplitIndex V r →₀ MvPolynomial α ℚ) : MvPolynomial α ℚ :=
  ∑ i : RootedSplitIndex V r,
    K i * chromaticCharacter (inducedGraph G i.1) A

/-- Scalar A-evaluation of the B-rooted crossing companion is the exact
swapped rooted two-alphabet chromatic orientation. -/
def chromaticRootCrossing_swappedOrientation_claim26358 : Prop :=
  ∀ {α V : Type*} [Fintype V] [DecidableEq V]
    [Fintype α] [DecidableEq α]
    (G : SimpleGraph V) (r : V) (A B : Finset α),
    Disjoint A B →
      scalarEvaluateRootCrossing G r A
        (rootCrossingCompanion G r B) =
        rootedTwoAlphabetChromatic G r B A

end

end MathlibPlus.Open.NewResearch2.R0608Claim26358Repair
