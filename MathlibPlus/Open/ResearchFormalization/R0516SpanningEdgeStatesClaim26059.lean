import MathlibPlus.Open.Combinatorics.FixedSupportClaim26067

namespace MathlibPlus.Open.ResearchFormalization.R0516SpanningEdgeStatesClaim26059

noncomputable section

/-- Claim 26059: a spanning edge state is carried by the host edge set, and
its profile at every positive order is the multiplicity of actual connected
components of that order, with each profile occurrence represented by one of
those components. -/
def claim26059 : Prop :=
  ∀ {V : Type*} [Fintype V]
    (G : SimpleGraph V)
    (A : MathlibPlus.Open.Combinatorics.FixedSupportClaim26067.EdgeState G),
    ∀ k : ℕ,
      0 < k →
        MathlibPlus.Open.Combinatorics.FixedSupportClaim26067.componentProfile
            (MathlibPlus.Open.Combinatorics.FixedSupportClaim26067.stateGraph A) k =
          Nat.card
            {C : (MathlibPlus.Open.Combinatorics.FixedSupportClaim26067.stateGraph A).ConnectedComponent //
              MathlibPlus.Open.Combinatorics.FixedSupportClaim26067.componentOrder
                  (MathlibPlus.Open.Combinatorics.FixedSupportClaim26067.stateGraph A) C = k} ∧
        Nonempty
          (Fin
              (MathlibPlus.Open.Combinatorics.FixedSupportClaim26067.componentProfile
                (MathlibPlus.Open.Combinatorics.FixedSupportClaim26067.stateGraph A) k) ≃
            {C : (MathlibPlus.Open.Combinatorics.FixedSupportClaim26067.stateGraph A).ConnectedComponent //
              MathlibPlus.Open.Combinatorics.FixedSupportClaim26067.componentOrder
                  (MathlibPlus.Open.Combinatorics.FixedSupportClaim26067.stateGraph A) C = k})

end

end MathlibPlus.Open.ResearchFormalization.R0516SpanningEdgeStatesClaim26059
