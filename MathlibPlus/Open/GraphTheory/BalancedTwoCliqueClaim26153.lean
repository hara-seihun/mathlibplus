import Mathlib
import MathlibPlus.GraphTheory.Claim26137

namespace MathlibPlus.Open.GraphTheory.BalancedTwoCliqueClaim26153

noncomputable section

open MathlibPlus.GraphTheory.Claim26137

/-- Edge cardinality of a finite simple graph. -/
def edgeCount {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  G.edgeSet.ncard

/-- The source's independence-number bound, written as a bound on every
independent vertex set (equivalently, every clique of the complement). -/
def independenceNumberAtMostTwo {V : Type*} [Fintype V]
    (G : SimpleGraph V) : Prop :=
  ∀ S : Finset V, Gᶜ.IsClique (S : Set V) → S.card ≤ 2

/-- Triangle-freeness of a finite simple graph. -/
def triangleFree {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ¬ ∃ S : Finset V, S.card = 3 ∧ G.IsClique (S : Set V)

/-- The balanced disjoint union of two complete graphs. -/
def balancedCliqueUnion (n : ℕ) :
    SimpleGraph (Fin (n / 2) ⊕ Fin ((n + 1) / 2)) :=
  SimpleGraph.sum
    (SimpleGraph.completeGraph (Fin (n / 2)))
    (SimpleGraph.completeGraph (Fin ((n + 1) / 2)))

/-- The balanced complete bipartite graph on the same two blocks. -/
def balancedCompleteBipartite (n : ℕ) :
    SimpleGraph (Fin (n / 2) ⊕ Fin ((n + 1) / 2)) :=
  SimpleGraph.fromRel (fun x y =>
    match x, y with
    | Sum.inl _, Sum.inr _ => True
    | Sum.inr _, Sum.inl _ => True
    | _, _ => False)

/-- Isomorphism of simple graphs with possibly different vertex carriers. -/
def graphIso {α β : Type*}
    (G : SimpleGraph α) (H : SimpleGraph β) : Prop :=
  ∃ e : α ≃ β, ∀ x y, G.Adj x y ↔ H.Adj (e x) (e y)

/-- The exact natural ceiling and floor edge counts in the equality case. -/
def equalityEdgeCount (n : ℕ) : ℕ :=
  Nat.ceil ((n : ℚ) * ((n - 2 : ℕ) : ℚ) / 4)

def complementMantelCount (n : ℕ) : ℕ :=
  Nat.floor ((n : ℚ) ^ 2 / 4)

/-- Claim 26153: the cyclic-five equality graph has independence number at
most two, a triangle-free complement at the Mantel bound, and is the
balanced disjoint union of two cliques. -/
def claim26153 : Prop :=
  ∀ (n : ℕ), 8 ≤ n →
    ∀ {V : Type*} [Fintype V] (H : SimpleGraph V),
      Fintype.card V = n →
      cyclicFive H →
      edgeCount H = equalityEdgeCount n →
        independenceNumberAtMostTwo H ∧
        triangleFree (Hᶜ) ∧
        edgeCount (Hᶜ) = complementMantelCount n ∧
        graphIso (Hᶜ) (balancedCompleteBipartite n) ∧
        graphIso H (balancedCliqueUnion n)

end
end MathlibPlus.Open.GraphTheory.BalancedTwoCliqueClaim26153
