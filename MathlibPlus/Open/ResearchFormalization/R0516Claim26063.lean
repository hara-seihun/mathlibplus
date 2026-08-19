import MathlibPlus.Open.Combinatorics.FixedSupportClaim26067

namespace MathlibPlus.Open.ResearchFormalization.R0516

noncomputable section

open MathlibPlus.Open.Combinatorics.FixedSupportClaim26067

/-- The component profile of the state after restricting to the complement of a
selected support. -/
def residualStateProfile {V : Type*} [Fintype V]
    {T : SimpleGraph V} (A : EdgeState T) (S : Finset V) : ℕ →₀ ℕ :=
  letI : Fintype {v : V // v ∈ (S : Set V)ᶜ} := Fintype.ofFinite _
  componentProfile
    (SimpleGraph.induce ((S : Set V)ᶜ) (stateGraph A))

def residualComponentProfile {V : Type*} [Fintype V]
    {T : SimpleGraph V} (S : Finset V)
    (R : EdgeState (deletedGraph T S)) : ℕ →₀ ℕ :=
  letI : Fintype {v : V // v ∉ (S : Set V)} := Fintype.ofFinite _
  componentProfile (stateGraph R)

/-- Claim 26063: for positive component order, the exact marked-component
carrier and the connected-support/residual-state carrier are mutually inverse,
with forced internal edges, omitted boundary edges, and preserved residual
profile. -/
def claim26063 : Prop :=
  ∀ {V : Type*} [Fintype V]
    (T : SimpleGraph V), T.IsTree →
    ∀ (k : ℕ), 1 ≤ k →
      (∀ (A : EdgeState T)
          (C : (stateGraph A).ConnectedComponent),
        componentOrder (stateGraph A) C = k →
          ∃! S : Finset V,
            S.card = k ∧
              componentSupport (stateGraph A) C = (S : Set V) ∧
              (∃! R : EdgeState (deletedGraph T S),
                A.1 = reconstructedEdges T S R ∧
                  (∀ e ∈ internalEdges T S, e ∈ A.1) ∧
                  (∀ e, e ∈ boundaryEdgeCarrier S → e ∉ A.1) ∧
                  residualStateProfile A S = residualComponentProfile S R)) ∧
      (∀ (S : Finset V),
          S.card = k →
            (T.induce (S : Set V)).Preconnected →
              ∀ R : EdgeState (deletedGraph T S),
                ∃! A : EdgeState T,
                  A.1 = reconstructedEdges T S R ∧
                    (∃ C : (stateGraph A).ConnectedComponent,
                      componentSupport (stateGraph A) C = (S : Set V) ∧
                        componentOrder (stateGraph A) C = k) ∧
                    residualStateProfile A S = residualComponentProfile S R)

end
end MathlibPlus.Open.ResearchFormalization.R0516
