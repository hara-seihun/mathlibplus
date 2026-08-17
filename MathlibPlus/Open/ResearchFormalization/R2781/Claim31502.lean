import MathlibPlus.Open.ResearchFormalizationBatch_01a000eb
import MathlibPlus.Open.ResearchFormalization.GraphDeckBatch

namespace MathlibPlus.Open.ResearchFormalization.R2781

open MathlibPlus.Open.ResearchFormalizationBatch_01a000eb

/-- Claim 31502: the connected spanning edge endpoint is the spanning-tree
reconstruction endpoint, with the lower Fourier terms separated from the tree
term. -/
def claim31502 : Prop :=
  let graphFrom : ∀ n : ℕ, LabeledGraph n → SimpleGraph (Fin n) :=
    fun n G =>
      SimpleGraph.fromRel (fun u v =>
        ∃ e : CompleteEdge n, e ∈ G ∧ u ∈ e.1 ∧ v ∈ e.1)
  let connected : ∀ n : ℕ, LabeledGraph n → Prop :=
    fun n G => (graphFrom n G).Connected
  let tree : ∀ n : ℕ, LabeledGraph n → Prop :=
    fun n G => (graphFrom n G).IsTree
  let lowerCharacterDeckDetermined : Prop :=
    ∀ (n m : ℕ) (Y : LabeledGraph n),
      m < n - 1 → Y.card = m →
        ∀ G H : LabeledGraph n,
          MathlibPlus.Open.ResearchFormalization.vertexDeckEqual
              (graphFrom n G) (graphFrom n H) →
            shapeCharacterQ Y G = shapeCharacterQ Y H
  let treeCharacterDeckDetermined : Prop :=
    ∀ (n : ℕ) (T : LabeledGraph n), tree n T →
      ∀ G H : LabeledGraph n,
        MathlibPlus.Open.ResearchFormalization.vertexDeckEqual
            (graphFrom n G) (graphFrom n H) →
          shapeCharacterQ T G = shapeCharacterQ T H
  let spanningTreeCountReconstruction : Prop :=
    ∀ (n : ℕ) (T : LabeledGraph n), tree n T →
      ∀ G H : LabeledGraph n,
        MathlibPlus.Open.ResearchFormalization.vertexDeckEqual
            (graphFrom n G) (graphFrom n H) →
          spanningSubgraphCount T G = spanningSubgraphCount T H
  (∀ (f : ℕ → ℕ) (n : ℕ), f n < n - 1 →
      ∀ Y : LabeledGraph n,
        connected n Y → Y.card ≤ f n → False) ∧
    (∀ (n : ℕ) (Y : LabeledGraph n), connected n Y →
      (Y.card = n - 1 ↔ tree n Y)) ∧
    (∀ (n : ℕ) (T : LabeledGraph n), tree n T →
      ∀ G : LabeledGraph n,
        fourierTop (fun H => (spanningSubgraphCount T H : ℚ)) (n - 1) G =
          ((-1 : ℚ) ^ (n - 1) / (2 : ℚ) ^ (n - 1)) * shapeCharacterQ T G) ∧
    lowerCharacterDeckDetermined ∧
    (treeCharacterDeckDetermined ↔ spanningTreeCountReconstruction)

end MathlibPlus.Open.ResearchFormalization.R2781
