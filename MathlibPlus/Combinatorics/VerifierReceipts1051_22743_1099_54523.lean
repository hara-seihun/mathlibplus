import MathlibPlus.Basic

open scoped BigOperators

namespace MathlibPlus.Combinatorics

/--
The finite pattern-space verifier receipt from claim 1051.  The enumerated
pattern carriers and four rejection certificates are explicit inputs; this is
a certificate summary, not a replacement for the verifier implementation.
-/
def completePatternSpaceRepair_claim1051
    {Pattern : Type*} [DecidableEq Pattern]
    (patterns threePrimePatterns : Finset Pattern)
    (actualSequencePresent initialStateDropRejected terminalOnlyRejected
      endpointOnlyRejected fabricatedIntermediateRejected : Prop) : Prop :=
  patterns.card = 142 ∧
    threePrimePatterns.card = 104 ∧
    actualSequencePresent ∧
    initialStateDropRejected ∧
    terminalOnlyRejected ∧
    endpointOnlyRejected ∧
    fabricatedIntermediateRejected

/--
The standard length-two path graph adjacency relation from claim 22743.
The rooted-wedge, shared-edge, path, and triangle predicates are supplied as
source carriers so that no graph encoding is silently chosen here.
-/
def standardLengthTwoPathGraph_claim22743
    {Vertex : Type*}
    (isRootedWedge : Vertex → Prop)
    (adjacent sharesEdge unionIsLengthThreePath unionIsTriangle :
      Vertex → Vertex → Prop) : Prop :=
  ∀ u v : Vertex,
    adjacent u v ↔
      isRootedWedge u ∧
        isRootedWedge v ∧
        sharesEdge u v ∧
        (unionIsLengthThreePath u v ∨ unionIsTriangle u v)

/--
The exact definition of the zeta zero-counting function in claim 1099.  The
finite `Zero` carrier is the source's nontrivial-zero list, and multiplicity is
summed over precisely the stated half-strip and height conditions.
-/
noncomputable def zetaZeroCountingFunction_claim1099
    {Zero : Type*} [Fintype Zero]
    (N : ℝ → ℝ → ℕ)
    (isNontrivial : Zero → Prop)
    (beta gamma : Zero → ℝ)
    (multiplicity : Zero → ℕ) : Prop := by
  classical
  exact
    ∀ sigma T : ℝ,
      N sigma T =
        Finset.sum (Finset.univ.filter (fun z =>
          isNontrivial z ∧ sigma ≤ beta z ∧ 0 < gamma z ∧ gamma z ≤ T))
          multiplicity

/--
The finite negative-screen receipt from claim 54523.  The reported counts and
agreement predicates are exposed without turning a bounded replay into an
all-order theorem.
-/
def exactNegativeScreen_claim54523
    (atomCount componentChecks mapCount mismatchCount : ℕ)
    (allSourceTargetPairsAgree allThreeInvariantsAgree : Prop) : Prop :=
  atomCount = 135 ∧
    componentChecks = 1354 ∧
    mapCount = 27 ∧
    mismatchCount = 0 ∧
    allSourceTargetPairsAgree ∧
    allThreeInvariantsAgree

end MathlibPlus.Combinatorics
