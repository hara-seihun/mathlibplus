import Mathlib
import MathlibPlus.GraphTheory.Claim28295
import MathlibPlus.Open.Combinatorics.TreeDeck

namespace MathlibPlus.Open.ResearchFormalization.R0337

open scoped BigOperators
open ProjectsResearch.TreeDeck
open MathlibPlus.GraphTheory.Claim28295

noncomputable section

abbrev TreeSpan (n : ℕ) := TreeState n
abbrev PowerSum := MvPolynomial ℕ ℚ

/-- The power-sum realization of the homogeneous symmetric-function carrier. -/
def powerSumWeight (d : ℕ →₀ ℕ) : ℕ :=
  ∑ i ∈ d.support, i * d i

def isHomogeneousPowerSum (n : ℕ) (p : PowerSum) : Prop :=
  ∀ d ∈ p.support, powerSumWeight d = n

/-- The spanning graph on the same vertices determined by a selected edge set. -/
def selectedEdgeGraph {V : Type*} (S : Finset (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (S : Set (Sym2 V))

/-- The chromatic symmetric function in the power-sum basis. -/
noncomputable def treeChromaticSymmetric {n : ℕ}
    (T : SimpleGraph (Fin n)) : PowerSum :=
  ∑ S ∈ T.edgeFinset.powerset,
    MvPolynomial.C ((-1 : ℚ) ^ S.card) *
      ((componentSizes (selectedEdgeGraph S)).map
        (fun k => MvPolynomial.X k)).prod

/-- The vertex-deleted graph transported to the canonical finite carrier. -/
def vertexDeletedGraph {n : ℕ} (G : SimpleGraph (Fin (n + 1))) (v : Fin (n + 1)) :
    SimpleGraph (Fin n) :=
  G.comap (Fin.succAbove v)

/-- The actual chromatic-deck basis value on an unlabelled tree class. -/
noncomputable def chromaticDeckBasis : (n : ℕ) → UnlabelledTree n → PowerSum
  | 0, _ => 0
  | n + 1, T =>
      ∑ v : Fin (n + 1),
        treeChromaticSymmetric (vertexDeletedGraph (Quotient.out T).1 v)

/-- The linear chromatic-deck map on the rational span of unlabelled trees. -/
noncomputable def chromaticDeck (n : ℕ) : TreeSpan n →ₗ[ℚ] PowerSum :=
  Finsupp.linearCombination ℚ (chromaticDeckBasis (n := n))

/-- The actual leaf-deck map, retaining exactly the degree-one deletions. -/
noncomputable def actualLeafDeck (n : ℕ) : TreeSpan n →ₗ[ℚ] TreeSpan (n - 1) :=
  ProjectsResearch.TreeDeck.leafDeck n

def kernelInclusion (n : ℕ) : Prop :=
  LinearMap.ker (chromaticDeck n) ≤ LinearMap.ker (actualLeafDeck n)

/-- The chromatic-deck image at order six. -/
def chromaticDeckImage6 : Submodule ℚ PowerSum :=
  LinearMap.range (chromaticDeck 6)

/-- The individual chromatic-deck column of an unlabelled tree class. -/
def chromaticDeckColumn (T : UnlabelledTree 6) : PowerSum :=
  chromaticDeck 6 (Finsupp.single T 1)

def treeClass {n : ℕ} (T : LabelledTree n) : UnlabelledTree n :=
  Quotient.mk' T

def graphIsomorphic {n : ℕ} (G H : SimpleGraph (Fin n)) : Prop :=
  Nonempty (G ≃g H)

/-- Edge sets for the four reviewed six-vertex witness presentations. -/
def witnessEdges0 : Set (Sym2 (Fin 6)) :=
  {Sym2.mk 0 1, Sym2.mk 0 4, Sym2.mk 1 2, Sym2.mk 2 3, Sym2.mk 4 5}

def witnessEdges1 : Set (Sym2 (Fin 6)) :=
  {Sym2.mk 0 1, Sym2.mk 0 4, Sym2.mk 1 2, Sym2.mk 1 3, Sym2.mk 4 5}

def witnessEdges2 : Set (Sym2 (Fin 6)) :=
  {Sym2.mk 0 1, Sym2.mk 0 4, Sym2.mk 0 5, Sym2.mk 1 2, Sym2.mk 1 3}

def witnessEdges3 : Set (Sym2 (Fin 6)) :=
  {Sym2.mk 0 1, Sym2.mk 0 3, Sym2.mk 0 5, Sym2.mk 1 2, Sym2.mk 3 4}

def witnessGraph0 : SimpleGraph (Fin 6) :=
  SimpleGraph.fromEdgeSet witnessEdges0

def witnessGraph1 : SimpleGraph (Fin 6) :=
  SimpleGraph.fromEdgeSet witnessEdges1

def witnessGraph2 : SimpleGraph (Fin 6) :=
  SimpleGraph.fromEdgeSet witnessEdges2

def witnessGraph3 : SimpleGraph (Fin 6) :=
  SimpleGraph.fromEdgeSet witnessEdges3

/-- Kernel inclusion first fails at order six, for the actual chromatic and
leaf-deck maps on the rational spans of unlabelled trees. -/
def claim20065_firstKernelFailure : Prop :=
  kernelInclusion 4 ∧
    kernelInclusion 5 ∧
      ¬ kernelInclusion 6

/-- No rational linear map on the actual chromatic-deck image recovers the
actual leaf deck at order six. -/
def claim20066_noLinearRecovery : Prop :=
  ¬ ∃ A₆ : chromaticDeckImage6 →ₗ[ℚ] TreeSpan 5,
      ∀ x : TreeSpan 6, ∀ y : chromaticDeckImage6,
        y.1 = chromaticDeck 6 x → A₆ y = actualLeafDeck 6 x

/-- The four displayed six-vertex tree presentations have pairwise distinct
individual chromatic-deck columns; the assertion is not a two-tree collision. -/
def claim20067_witnessColumnsPairwiseDistinct : Prop :=
  ∃ (T₀ T₁ T₂ T₃ : LabelledTree 6),
    T₀.1 = witnessGraph0 ∧
      T₁.1 = witnessGraph1 ∧
        T₂.1 = witnessGraph2 ∧
          T₃.1 = witnessGraph3 ∧
            ¬ graphIsomorphic T₀.1 T₁.1 ∧
              ¬ graphIsomorphic T₀.1 T₂.1 ∧
                ¬ graphIsomorphic T₀.1 T₃.1 ∧
                  ¬ graphIsomorphic T₁.1 T₂.1 ∧
                    ¬ graphIsomorphic T₁.1 T₃.1 ∧
                      ¬ graphIsomorphic T₂.1 T₃.1 ∧
                        chromaticDeckColumn (treeClass T₀) ≠
                            chromaticDeckColumn (treeClass T₁) ∧
                          chromaticDeckColumn (treeClass T₀) ≠
                            chromaticDeckColumn (treeClass T₂) ∧
                            chromaticDeckColumn (treeClass T₀) ≠
                              chromaticDeckColumn (treeClass T₃) ∧
                              chromaticDeckColumn (treeClass T₁) ≠
                                chromaticDeckColumn (treeClass T₂) ∧
                                chromaticDeckColumn (treeClass T₁) ≠
                                  chromaticDeckColumn (treeClass T₃) ∧
                                  chromaticDeckColumn (treeClass T₂) ≠
                                    chromaticDeckColumn (treeClass T₃)

end
end MathlibPlus.Open.ResearchFormalization.R0337
