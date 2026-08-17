import MathlibPlus.GraphTheory.Claim26137

namespace MathlibPlus.Open.ResearchFormalization.R0554

noncomputable section

open MathlibPlus.GraphTheory.Claim26137

private def graphDegree {V : Type*} [Fintype V]
    (G : SimpleGraph V) (v : V) : ℕ :=
  Set.ncard (G.neighborSet v)

private def graphEdgeCount {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  Set.ncard G.edgeSet

private def equalityEdgeCount (n : ℕ) : ℕ :=
  Nat.ceil (((n : ℚ) * ((n - 2 : ℕ) : ℚ)) / 4)

private def independentWithin {V : Type*}
    (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → ¬ G.Adj x y

private def traceSet {V : Type*}
    (G : SimpleGraph V) (T : Set V) (u : V) : Set V :=
  G.neighborSet u ∩ T

private def traceMultiplicity {V : Type*} [Fintype V]
    (G : SimpleGraph V) (T R : Set V) : ℕ :=
  Set.ncard {u : V | u ∉ T ∧ traceSet G T u = R}

/-- Claim 26152: with the inherited order-nine equality-graph hypotheses,
the independent degree-four triple has exactly the three doubled two-element
trace types, different trace types are completely joined, and every outside
vertex has degree at least six. -/
def claim26152 : Prop :=
  ∀ (H : SimpleGraph (Fin 9)) (T : Finset (Fin 9)),
    cyclicFive H →
    graphEdgeCount H = equalityEdgeCount 9 →
    T.card = 3 →
    independentWithin H (T : Set (Fin 9)) →
    (∀ v : Fin 9, v ∈ T → graphDegree H v = 4) →
    (∀ u : Fin 9, u ∉ (T : Set (Fin 9)) →
      (traceSet H (T : Set (Fin 9)) u).ncard = 2) ∧
    (∀ R : Finset (Fin 9),
      (R : Set (Fin 9)) ⊆ (T : Set (Fin 9)) → R.card = 2 →
        traceMultiplicity H (T : Set (Fin 9)) (R : Set (Fin 9)) = 2) ∧
    (∀ u v : Fin 9,
      u ∉ (T : Set (Fin 9)) → v ∉ (T : Set (Fin 9)) →
      traceSet H (T : Set (Fin 9)) u ≠ traceSet H (T : Set (Fin 9)) v →
      H.Adj u v) ∧
    (∀ u : Fin 9, u ∉ (T : Set (Fin 9)) → graphDegree H u ≥ 6)

end
end MathlibPlus.Open.ResearchFormalization.R0554
