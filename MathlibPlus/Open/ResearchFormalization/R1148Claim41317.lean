import MathlibPlus.Open.ResearchFormalization.R1148Claim31555

namespace MathlibPlus.Open.ResearchFormalization.R1148Claim41317

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1148

abbrev C7_41317 := ZMod 7
abbrev A41317 := AffinePlane31555

/-- The two outer connection sets occurring in the four indexed graphs. -/
def outerStepsTwo41317 : Finset C7_41317 := {-1, 1}

def outerStepsFour41317 : Finset C7_41317 := {-1, 1, -2, 2}

/-- The empty and nonzero inner connection sets. -/
def innerStepsEmpty41317 : Finset C7_41317 := ∅

def innerStepsNonzero41317 : Finset C7_41317 :=
  (Finset.univ : Finset C7_41317).erase 0

/-- The four graph labels in the order used by the admitted statement. -/
def kernelGraphIndex41317 : Fin 4 → ℕ :=
  ![49, 52, 2769, 2772]

/-- The outer and inner connection sets paired with those graph labels. -/
def kernelOuterSteps41317 : Fin 4 → Finset C7_41317 :=
  ![outerStepsTwo41317, outerStepsTwo41317,
    outerStepsFour41317, outerStepsFour41317]

def kernelInnerSteps41317 : Fin 4 → Finset C7_41317 :=
  ![innerStepsEmpty41317, innerStepsNonzero41317,
    innerStepsEmpty41317, innerStepsNonzero41317]

/-- The displayed connection-set formula on `𝔽₇²`. -/
def explicitKernelConnectionSet41317
    (Q I : Finset C7_41317) : Set A41317 :=
  {v | (∃ i, i ∈ I ∧ v = pairVector31555 0 i) ∨
    (∃ q, q ∈ Q ∧ ∃ y : C7_41317,
      v = pairVector31555 q y)}

/-- The connection set assigned to one of the four indexed kernel graphs. -/
def kernelConnectionSet41317 (j : Fin 4) : Set A41317 :=
  kernelConnectionSet31555 (kernelOuterSteps41317 j) (kernelInnerSteps41317 j)

/-- The corresponding Cayley adjacency relation. -/
def kernelAdjacency41317 (j : Fin 4) (x y : A41317) : Prop :=
  kernelAdjacency31555 (kernelOuterSteps41317 j) (kernelInnerSteps41317 j) x y

/-- Adjacency in the cyclic Cayley graph with connection set `S`. -/
def cyclicAdjacency41317
    (S : Finset C7_41317) (u v : C7_41317) : Prop :=
  u ≠ v ∧ v - u ∈ (S : Set C7_41317)

/-- The adjacency relation of the lexicographic product of the two displayed
cyclic Cayley graphs. -/
def lexicographicProductAdjacency41317
    (Q I : Finset C7_41317) (x y : A41317) : Prop :=
  cyclicAdjacency41317 Q (x 0) (y 0) ∨
    (x 0 = y 0 ∧ cyclicAdjacency41317 I (x 1) (y 1))

/-- Claim 41317: the four indexed `C₇²` kernel graphs have the displayed
connection sets, and their Cayley relations are the corresponding
lexicographic-product relations. -/
def claim41317 : Prop :=
  kernelGraphIndex41317 0 = 49 ∧
    kernelGraphIndex41317 1 = 52 ∧
      kernelGraphIndex41317 2 = 2769 ∧
        kernelGraphIndex41317 3 = 2772 ∧
          (∀ j : Fin 4,
            kernelConnectionSet41317 j =
              explicitKernelConnectionSet41317
                (kernelOuterSteps41317 j) (kernelInnerSteps41317 j)) ∧
            (∀ (j : Fin 4) (x y : A41317),
              kernelAdjacency41317 j x y ↔
                lexicographicProductAdjacency41317
                  (kernelOuterSteps41317 j) (kernelInnerSteps41317 j) x y)

end

end MathlibPlus.Open.ResearchFormalization.R1148Claim41317
