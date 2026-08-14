import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch01a000eb6a9472cb9ce282c616a63864

noncomputable section

/-- The order parameter from the short-leaf depth-two-spider calculation. -/
def spiderOrder (a b : ℕ) : ℕ := 1 + a + 2 * b

/-- The two factors occurring in the zero-`x₂` coefficient. -/
def spiderLinear : Polynomial ℚ := 1 + Polynomial.X

def spiderQuadratic : Polynomial ℚ :=
  Polynomial.X ^ 2 + Polynomial.X + 1

def spiderH (a b : ℕ) : Polynomial ℚ :=
  spiderLinear ^ (a - 1) * spiderQuadratic ^ b

def shortLeafB (a b : ℕ) : Polynomial ℚ :=
  spiderH a b + Polynomial.X ^ (spiderOrder a b - 1) * spiderLinear

/--
Claim 30456: the explicit `y⁰` coefficient has degree `n`, subtracting its
specified monomial factor recovers `h`, and unique factorization recovers the
parameters from that factor.
-/
def claim30456 : Prop :=
  (∀ a b : ℕ, 1 ≤ a →
    Polynomial.natDegree (shortLeafB a b) = spiderOrder a b ∧
    shortLeafB a b -
        Polynomial.X ^ (spiderOrder a b - 1) * spiderLinear = spiderH a b) ∧
  (∀ a₁ b₁ a₂ b₂ : ℕ,
    1 ≤ a₁ → 1 ≤ a₂ →
    shortLeafB a₁ b₁ = shortLeafB a₂ b₂ →
    a₁ = a₂ ∧ b₁ = b₂)

end

end MathlibPlus.Open.ResearchFormalizationBatch01a000eb6a9472cb9ce282c616a63864
