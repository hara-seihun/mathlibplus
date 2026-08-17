import MathlibPlus.GraphTheory.Claim26137

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0554Claim26149

noncomputable section

open MathlibPlus.GraphTheory.Claim26137

private noncomputable def graphDegree {V : Type*} [Fintype V]
    (G : SimpleGraph V) (v : V) : ℕ :=
  Set.ncard (G.neighborSet v)

private noncomputable def graphEdgeCount {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  Set.ncard G.edgeSet

private noncomputable def equalityEdgeCount (n : ℕ) : ℕ :=
  Nat.ceil (((n : ℚ) * ((n - 2 : ℕ) : ℚ)) / 4)

private def equalityDegreeProfile {n : ℕ}
    (G : SimpleGraph (Fin n)) : Prop :=
  (∃ k : ℕ,
    n = 2 * k ∧ ∀ v : Fin n, graphDegree G v = k - 1) ∨
  (∃ k : ℕ,
    n = 2 * k + 1 ∧
      (Finset.univ.filter (fun v : Fin n => graphDegree G v = k - 1)).card = k ∧
      (Finset.univ.filter (fun v : Fin n => graphDegree G v = k)).card = k + 1)

private def independentWithin {V : Type*}
    (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → ¬ G.Adj x y

private def traceSet {V : Type*}
    (G : SimpleGraph V) (T : Set V) (u : V) : Set V :=
  G.neighborSet u ∩ T

private def inducedForestOn {V : Type*}
    (G : SimpleGraph V) (S : Set V) : Prop :=
  (G.induce S).IsAcyclic

private noncomputable def traceMultiplicity {V : Type*} [Fintype V]
    (G : SimpleGraph V) (T R : Set V) : ℕ :=
  Set.ncard {u : V | u ∉ T ∧ traceSet G T u = R}

/-- Claim 26149: the exact equality edge count and the even/odd degree
    profiles for cyclic-five graphs of order at least eight. -/
def equalityDegreeProfiles_claim26149 : Prop :=
  ∀ n : ℕ, 8 ≤ n → ∀ H : SimpleGraph (Fin n),
    cyclicFive H →
    graphEdgeCount H = equalityEdgeCount n →
      equalityDegreeProfile H


end

end MathlibPlus.Open.ResearchFormalization.R0554Claim26149
