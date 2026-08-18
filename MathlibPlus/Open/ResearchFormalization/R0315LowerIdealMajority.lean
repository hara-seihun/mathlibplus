import MathlibPlus.Open.ResearchFormalization.R0315ExtensionClaims

namespace MathlibPlus.Open.ResearchFormalization.R0315ExtensionClaims

/-- Claim 19733: a nontrivial lower ideal has a majority coordinate, and the
corresponding comparable-region count is bounded by 23. -/
def claim19733 : Prop :=
  ∀ {X : Type*} [Fintype X] [DecidableEq X]
    (G : Family X) (T : Finset X) (tight : Fin 3 → X)
    (topTight : Fin 2 → X) (tops : Fin 2 → Finset X),
    exactExtensionCoreContext G T tight topTight tops →
      principalUpsetAndIncomparabilityBounds G T topTight tops →
      ∀ i : Fin 2,
        let D := lowerIdeal G (tops i)
        let K := principalUpset G (tops i)
        (∃ A ∈ D, A.Nonempty) →
          (∃ x : X, frequency D x ≥ (D.card + 1) / 2) ∧
            K.card + (D.card + 1) / 2 ≤ 23

end MathlibPlus.Open.ResearchFormalization.R0315ExtensionClaims
