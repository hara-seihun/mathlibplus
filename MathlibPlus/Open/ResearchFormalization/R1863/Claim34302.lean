import MathlibPlus.Open.Algebra.PathSwitchM0

namespace MathlibPlus.Open.ResearchFormalization.R1863

open MathlibPlus.Open.Algebra.PathSwitchM0

/-- Claim 34302: the exact all-order path-switch boundary factors through
its common host and the scalar extension seed on the abstract path-switch
carrier. -/
def claim34302 : Prop :=
  let N : PathRing → PathRing := fun p => A p + zVar * p
  let L : PathRing := N 1
  ∀ (P Q U_H : PathRing),
    A P = U_H ∧ A Q = U_H ∧
      (∀ k : ℕ,
        A (N^[k] P) = A ((N^[k] (1 : PathRing)) * P)) ∧
      (∀ k : ℕ,
        A (N^[k] Q) = A ((N^[k] (1 : PathRing)) * Q)) ∧
      (∀ k : ℕ,
        A (P * N^[k] Q) = A (Q * N^[k] P)) →
      ∀ m : ℕ, 1 ≤ m →
        A (L * (P * N^[m] Q - Q * N^[m] P)) =
          U_H * A ((N^[m] (1 : PathRing)) * (P - Q))

end MathlibPlus.Open.ResearchFormalization.R1863
