import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.C0002Claim41

/-- A finite product of independent factors with nonnegative weights has first
cluster coefficient equal to the total weight and nonpositive second pair
cluster, under the two displayed first formal-log coefficient identities. -/
def independentFactorizationPairCluster_claim41 : Prop :=
  ∀ {ι : Type} [DecidableEq ι] (s : Finset ι) (w : ι → ℝ)
    (P : Polynomial ℝ) (c1 c2 : ℝ),
    (∀ r ∈ s, 0 ≤ w r) →
    P = ∏ r ∈ s,
      (Polynomial.C 1 + Polynomial.C (w r) * Polynomial.X) →
    c1 = P.coeff 1 →
    c2 = P.coeff 2 - c1 ^ 2 / 2 →
    c1 = ∑ r ∈ s, w r ∧
      c2 = -(1 / 2 : ℝ) * ∑ r ∈ s, (w r) ^ 2 ∧
      c2 ≤ 0

end MathlibPlus.Open.ResearchFormalization.C0002Claim41
