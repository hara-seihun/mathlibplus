import MathlibPlus.Open.NewResearch2.R0390AtomisticClosure

namespace MathlibPlus.Open.NewResearch2.R0390AtomisticClosure

noncomputable section

/-- The canonical cube vertex above the fixed outside singleton coordinate. -/
def cubeVertex20808 (j : ℕ) (S : Finset ℕ) : ℕ :=
  joinOf (insert j S)

/-- The eight vertices obtained from all subsets of the fixed tight triple. -/
def cubeVertices20808 (j : ℕ) (T : Finset ℕ) : Finset ℕ :=
  T.powerset.image (cubeVertex20808 j)

/-- The tight-coordinate trace of a canonical cube vertex. -/
def tightTrace20808 (j : ℕ) (T S : Finset ℕ) : Finset ℕ :=
  singletonMasksBelow (cubeVertex20808 j S) ∩ T

/-- The transported lower-cover edge in the fixed singleton-coordinate carrier. -/
def transportedEdge20808 (jStar j : ℕ) (S : Finset ℕ) : Finset ℕ :=
  singletonMasksBelow (cubeVertex20808 j S) \
    singletonMasksBelow (joinOf (insert jStar S))

/-- The actual lower-cover relation in the displayed closure lattice. -/
def closureLowerCover20808 (jStar j : ℕ) : Prop :=
  jStar ∈ closureLattice ∧
    j ∈ closureLattice ∧
      jStar ≠ j ∧
        below jStar j ∧
          ∀ x ∈ closureLattice,
            below jStar x → below x j → x = jStar ∨ x = j

/-- Claim 20808: in the explicit R-0390 closure lattice, the fixed outside
coordinate 3 has an eight-vertex tight cube with all eight tight traces, but
its concrete lower-cover edge from 0 is not parallel across that cube; at the
full tight subset its transported edge is empty. -/
def claim20808 : Prop :=
  let T : Finset ℕ := {1, 2, 4}
  let j : ℕ := 8
  let jStar : ℕ := 0
  closureLowerCover20808 jStar j ∧
    T.card = 3 ∧
      T ⊆ singletonMasks ∧
        j ∈ singletonMasks ∧
          j ∉ T ∧
            T.powerset.card = 8 ∧
              (cubeVertices20808 j T).card = 8 ∧
                (∀ S ∈ T.powerset,
                  cubeVertex20808 j S ∈ closureLattice) ∧
                  (∀ S ∈ T.powerset,
                    j ∈ singletonMasksBelow (cubeVertex20808 j S)) ∧
                    (∀ S ∈ T.powerset,
                      tightTrace20808 j T S = S) ∧
                      transportedEdge20808 jStar j T = ∅ ∧
                        ¬ (∀ S ∈ T.powerset,
                          transportedEdge20808 jStar j S = {j})

end

end MathlibPlus.Open.NewResearch2.R0390AtomisticClosure
