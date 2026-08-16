import Mathlib
import MathlibPlus.Open.ProjectsResearch.CayleyCIClaims

namespace MathlibPlus.Open.ProjectsResearch.CI

/-- Claim 60268: every ordinary undirected valency-four Cayley graph on the
scalar-cubic extension V ⋊ C₃ is CI, uniformly in the finite nonzero rank. -/
def allRankScalarCubicValencyFour : Prop :=
  ∀ (p : ℕ),
    ∀ hp : Nat.Prime p,
      letI : Fact (Nat.Prime p) := ⟨hp⟩
      ∀ (V : Type*) [AddCommGroup V] [Module (ZMod p) V]
      [FiniteDimensional (ZMod p) V] [Nontrivial V],
      ∀ (omega : ZMod p),
        orderOf omega = 3 →
        ∀ (S T : Set (vCarrier V)),
          vIdentityFree S →
          vInverseClosed omega S →
          vIdentityFree T →
          vInverseClosed omega T →
          Set.ncard S = 4 →
          vCayleyGraphIso omega S T →
          ∃ alpha : vCarrier V ≃ vCarrier V,
            vAutomorphism omega alpha ∧ vTransports alpha S T

end MathlibPlus.Open.ProjectsResearch.CI
