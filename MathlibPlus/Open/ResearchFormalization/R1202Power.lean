import MathlibPlus.Open.Algebra.AffinePower

namespace MathlibPlus.Open.ResearchFormalization.R1202Power

open MathlibPlus.Algebra.AffinePower

/-- Claim 32189: the explicit q1/q2 power formula gives unique regular
orbits of the elementary abelian subgroup Q of the affine F_p^2 action. -/
def claim32189 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → 2 < p →
    (∀ (a b : Fin p),
      (((q₁ p) ^ a.val) * ((q₂ p) ^ b.val)) (0, 0) =
        ((a.val : ZMod p),
          (Nat.choose a.val 2 : ZMod p) + (b.val : ZMod p))) ∧
    Function.Bijective (fun q : Q p => q.1 (0, 0)) ∧
    Nat.card (Q p) = p ^ 2 ∧
    (∀ q : Q p, q ^ p = 1) ∧
    (∀ q₁ q₂ : Q p, q₁ * q₂ = q₂ * q₁)

end MathlibPlus.Open.ResearchFormalization.R1202Power
