import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatch019ffedf

/-- The matching relation between the two clique components. -/
def twoCliqueRelation (a d k : ℕ) (x y : Fin a ⊕ Fin d) : Prop :=
  match x, y with
  | Sum.inl _, Sum.inl _ => True
  | Sum.inr _, Sum.inr _ => True
  | Sum.inl i, Sum.inr j => i.1 = j.1 ∧ i.1 < k
  | Sum.inr j, Sum.inl i => i.1 = j.1 ∧ i.1 < k

/-- `L(a,d,k)`: two disjoint cliques with a size-`k` matching between them. -/
def L (a d k : ℕ) : SimpleGraph (Fin a ⊕ Fin d) :=
  SimpleGraph.fromRel (twoCliqueRelation a d k)

/-- Graph isomorphism written as a vertex equivalence preserving adjacency. -/
def GraphIso {α β : Type} (G : SimpleGraph α) (H : SimpleGraph β) : Prop :=
  ∃ e : α ≃ β, ∀ x y, G.Adj x y ↔ H.Adj (e x) (e y)

/-- The graph obtained by deleting one vertex. -/
def deleteVertex {α : Type} (G : SimpleGraph α) (u : α) : SimpleGraph {x : α // x ≠ u} :=
  G.induce {x | x ≠ u}

/-- The number of edges of a finite simple graph. -/
noncomputable def edgeCount {α : Type} [Fintype α] (G : SimpleGraph α) : ℕ :=
  G.edgeSet.ncard

def H (c b : ℕ) : SimpleGraph (Fin (c + 1) ⊕ Fin (c - 1)) := L (c + 1) (c - 1) b

def A (c b : ℕ) : SimpleGraph (Fin c ⊕ Fin (c - 1)) := L c (c - 1) (b - 1)

def B (c b : ℕ) : SimpleGraph (Fin c ⊕ Fin (c - 1)) := L c (c - 1) b

def E (c b : ℕ) : SimpleGraph (Fin (c + 1) ⊕ Fin (c - 2)) := L (c + 1) (c - 2) (b - 1)

/-- Claim 26552. -/
def claim26552 : Prop :=
  ∀ (c b : ℕ), c ≥ 3 → 2 ≤ b → b ≤ c - 1 →
    edgeCount (B c b) = edgeCount (A c b) + 1 ∧
    edgeCount (E c b) = edgeCount (A c b) + 2 ∧
    ¬ GraphIso (A c b) (B c b) ∧
    ¬ GraphIso (A c b) (E c b) ∧
    ¬ GraphIso (B c b) (E c b)

/-- Claim 26555. -/
def claim26555 : Prop :=
  ∀ (c b : ℕ), c ≥ 3 → 2 ≤ b → b ≤ c - 1 →
    ∀ {V : Type} [Fintype V] (X : SimpleGraph V) (u v w : V),
      u ≠ v → u ≠ w → v ≠ w →
      GraphIso (deleteVertex X u) (A c b) →
      GraphIso (deleteVertex X v) (B c b) →
      GraphIso (deleteVertex X w) (E c b) →
      GraphIso X (H c b)

end MathlibPlus.Open.Research.FormalizationBatch019ffedf
