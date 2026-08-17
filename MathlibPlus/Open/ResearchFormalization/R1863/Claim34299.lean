import MathlibPlus.Open.Algebra.PathSwitchM0

namespace MathlibPlus.Open.ResearchFormalization.R1863

open MathlibPlus.Open.Algebra.PathSwitchM0

/-- Claim 34299: on the exact abstract same-host path-switch carrier, the
opposite-end path boundary lies in the unrooted selector kernel. -/
def claim34299 : Prop :=
  let N : PathRing → PathRing := fun p => A p + zVar * p
  ∀ (P Q U_H : PathRing),
    A P = U_H ∧ A Q = U_H ∧
      (∀ k : ℕ,
        A (N^[k] P) = A ((N^[k] (1 : PathRing)) * P)) ∧
      (∀ k : ℕ,
        A (N^[k] Q) = A ((N^[k] (1 : PathRing)) * Q)) ∧
      (∀ k : ℕ,
        A (P * N^[k] Q) = A (Q * N^[k] P)) →
      ∀ m : ℕ,
        A (P * N^[m] Q - Q * N^[m] P) = 0

end MathlibPlus.Open.ResearchFormalization.R1863
