import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationD0079

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Labeled finite graph presentations of a fixed vertex cardinality are identified by graph isomorphism. -/
def graphIsoRel (n : ℕ) (G H : SimpleGraph (Fin n)) : Prop :=
  Nonempty (G ≃g H)

def graphSetoid (n : ℕ) : Setoid (SimpleGraph (Fin n)) where
  r := graphIsoRel n
  iseqv := by
    constructor
    · intro G
      exact ⟨SimpleGraph.Iso.refl⟩
    · intro G H h
      rcases h with ⟨f⟩
      exact ⟨f.symm⟩
    · intro G H K h₁ h₂
      rcases h₁ with ⟨f⟩
      rcases h₂ with ⟨g⟩
      exact ⟨g.comp f⟩

/-- Isomorphism classes of finite graphs on `n` vertices. -/
def GraphShape (n : ℕ) := Quotient (graphSetoid n)

/-- The unlabelled `n`-vertex tree shapes.  The quotient representative is
used only through isomorphism-invariant graph data below. -/
def Tree (n : ℕ) :=
  {G : GraphShape n // (Quotient.out G).IsTree}

def treeGraph {n : ℕ} (T : Tree n) : SimpleGraph (Fin n) := Quotient.out T.1

abbrev V (n : ℕ) := Tree n →₀ ℚ

/-- Ordinary subgraph copies, counted as subgraphs rather than labelled
embeddings, so automorphisms of the motif do not create extra copies. -/
def ordinarySubgraphCopies {m n : ℕ} (H : Tree m) (T : Tree n) : ℕ :=
  Nat.card {S : (treeGraph T).Subgraph // Nonempty (treeGraph H ≃g S.coe)}

abbrev Motif := Σ m, Tree m

def motifEdgeCount (H : Motif) : ℕ := H.1 - 1

def motifCopies {n : ℕ} (H : Motif) (T : Tree n) : ℕ :=
  ordinarySubgraphCopies H.2 T

abbrev RetainedMotif (q : ℕ) :=
  {H : Motif // 2 ≤ motifEdgeCount H ∧ motifEdgeCount H ≤ q + 1}

def jointMotifProfile (q n : ℕ) (T : Tree n) : RetainedMotif q → ℕ :=
  fun H => motifCopies H.1 T

def motifOperatorRaw {n : ℕ} (H : Motif) : V n →ₗ[ℚ] V n :=
  Finsupp.linearCombination ℚ (fun T =>
    Finsupp.single T (motifCopies H T : ℚ))

def motifOperator (q n : ℕ) (H : RetainedMotif q) : V n →ₗ[ℚ] V n :=
  motifOperatorRaw H.1

def profileEigenspace (q n : ℕ) (profileValue : RetainedMotif q → ℕ) : Submodule ℚ (V n) :=
  Submodule.span ℚ {x | ∃ T : Tree n, jointMotifProfile q n T = profileValue ∧ x = Finsupp.single T 1}

def claim5082 : Prop :=
  ∀ (q n : ℕ) (profileValue : RetainedMotif q → ℕ) (H : RetainedMotif q)
    (x : profileEigenspace q n profileValue),
    motifOperator q n H x = (profileValue H : ℚ) • (x : V n)

/-- The graph obtained by deleting one vertex, transported to `Fin k`. -/
def deletedGraphShape {k : ℕ} (T : Tree (k + 1)) (v : Fin (k + 1)) : GraphShape k :=
  Quotient.mk'' ((treeGraph T).comap (Fin.succAbove v))

def leafVertex {n : ℕ} (T : Tree n) (v : Fin n) : Prop :=
  Nat.card ((treeGraph T).neighborSet v) = 1

/-- A deleted leaf card is present exactly when the resulting graph is a tree;
for a genuine leaf in the nontrivial cases this is the usual tree card. -/
def deletedLeafCard {k : ℕ} (T : Tree (k + 1)) (v : Fin (k + 1)) : Option (Tree k) :=
  let C := deletedGraphShape T v
  if h : (Quotient.out C).IsTree then some ⟨C, h⟩ else none

def leafDeckBasisSucc (k : ℕ) (T : Tree (k + 1)) : V k :=
  (Finset.univ.filter (leafVertex T)).sum fun v =>
    match deletedLeafCard T v with
    | some C => Finsupp.single C 1
    | none => 0

def leafDeck : (n : ℕ) → V n →ₗ[ℚ] V (n - 1)
  | 0 => 0
  | k + 1 => Finsupp.linearCombination ℚ (fun T => leafDeckBasisSucc k T)

def attachmentMotif (q : ℕ) :=
  {H : Motif // 1 ≤ motifEdgeCount H ∧ motifEdgeCount H ≤ q + 1}

def observabilityMap (q n : ℕ) : V n →ₗ[ℚ] (attachmentMotif q → V (n - 1)) :=
  LinearMap.pi fun H => (leafDeck n).comp (motifOperatorRaw H.1)

def observabilityDefect (q n : ℕ) : Submodule ℚ (V n) :=
  LinearMap.ker (observabilityMap q n)

def observabilityColumn (q n : ℕ) (T : Tree n) : attachmentMotif q → V (n - 1) :=
  observabilityMap q n (Finsupp.single T 1)

def pairwiseColumnSeparation (q n : ℕ) : Prop :=
  Pairwise (fun T₁ T₂ : Tree n => observabilityColumn q n T₁ ≠ observabilityColumn q n T₂)

def nontrivialObservabilityKernel (q n : ℕ) : Prop :=
  ∃ x : V n, x ≠ 0 ∧ x ∈ observabilityDefect q n

def claim5091 : Prop :=
  ¬ (∀ (q n : ℕ), pairwiseColumnSeparation q n → ¬ nontrivialObservabilityKernel q n)

end
end MathlibPlus.Open.ResearchFormalizationD0079
