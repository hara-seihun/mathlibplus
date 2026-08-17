import MathlibPlus.Open.ResearchFormalization.BatchQ0134Claim16879

namespace MathlibPlus.Open.ResearchFormalization.BatchQ0134Claim16878

/-- Claim 16878: every bad strict-convex planar configuration has at least
nine vertices, on the exact finite planar carrier of Claim 16879. -/
def claim16878_minimumOrderNine : Prop :=
  ∀ P : Finset MathlibPlus.Open.ResearchFormalization.BatchQ0134Claim16879.Plane,
    MathlibPlus.Open.ResearchFormalization.BatchQ0134Claim16879.badConfiguration P →
      9 ≤ P.card

end MathlibPlus.Open.ResearchFormalization.BatchQ0134Claim16878
