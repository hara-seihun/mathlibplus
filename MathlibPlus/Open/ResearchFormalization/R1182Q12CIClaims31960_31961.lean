import MathlibPlus.Open.GroupTheory.NR2CayleyCI
import MathlibPlus.Open.ResearchFormalization.Claim31958

namespace MathlibPlus.Open.ResearchFormalization.R1182.Q12CI

open MathlibPlus.Open.ResearchFormalization.Claim31958

noncomputable section

/-- The ordinary undirected Cayley-CI predicate, written without a
proof-carrying finiteness instance so that the prime-indexed quaternion
carrier remains the exact displayed group. -/
def ordinaryUndirectedCI31960 (G : Type*) [Group G] : Prop :=
  ∀ (S T : Set G),
    S = S⁻¹ →
      T = T⁻¹ →
        1 ∉ S →
          1 ∉ T →
            Nonempty
                (SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T) →
              ∃ φ : G ≃* G, φ '' S = T

/-- Claim 31960: the exact generalized-quaternion carrier Q_(12p) is an
ordinary undirected CI-group for every prime p>3 with p congruent to 2
modulo 3. -/
def claim31960 : Prop :=
  ∀ p : ℕ,
    Nat.Prime p →
      3 < p →
        p % 3 = 2 →
          ordinaryUndirectedCI31960 (Q12p p)

/-- Claim 31961: the p=11 specialization is the ordinary CI group
Q_132 = Dic(33). -/
def claim31961 : Prop :=
  ordinaryUndirectedCI31960 (Q12p 11)

end

end MathlibPlus.Open.ResearchFormalization.R1182.Q12CI
