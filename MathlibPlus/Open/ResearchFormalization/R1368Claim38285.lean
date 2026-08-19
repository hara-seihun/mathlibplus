import MathlibPlus.Open.ResearchFormalization.R1368Claim38282
import MathlibPlus.Open.ResearchFormalization.R1368Valency57

namespace MathlibPlus.Open.ResearchFormalization.R1368Claim38285

open MathlibPlus.Open.Research.R1468

/-- Claim 38285: the settled ordinary-undirected CI boundary is the entire
low/high valency range on the exact R-1468 Cayley carrier. -/
def claim38285_settledOrdinaryCIBoundary : Prop :=
  ∀ k : ℕ,
    (k ≤ 14 ∨ 57 ≤ k) →
      isCI k

end MathlibPlus.Open.ResearchFormalization.R1368Claim38285
