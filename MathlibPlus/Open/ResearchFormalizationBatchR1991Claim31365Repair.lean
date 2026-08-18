import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch019ffedf

open scoped BigOperators ArithmeticFunction.Moebius

noncomputable section

namespace MathlibPlus.Open.ResearchFormalizationBatchR1991Claim31365Repair

open Filter Set Topology Classical
open MathlibPlus.Open.ResearchFormalizationBatch019ffedf

private def primitiveNode (d : ℕ) (θ : ℝ) : Prop :=
  ∃ m : ℕ,
    Odd m ∧ Nat.Coprime m d ∧ 0 < m ∧ m < 2 * d ∧
      θ = (m : ℝ) * Real.pi / (2 * (d : ℝ))

private def primitiveMass (θ₀ : ℝ) (d : ℕ) : ℝ :=
  ∑ k : Fin d,
    if primitiveNode d (chebyshevAngle d k) then
      |explicitLambdaWeight θ₀ d k|
    else 0

private def finiteSpikeCoefficient (θ₀ : ℝ) (n s : ℕ) : ℝ :=
  (ArithmeticFunction.moebius s : ℝ) *
      (-1 : ℝ) ^ ((s - 1) / 2) *
        Real.cos (((n * s : ℕ) : ℝ) * θ₀) /
    ((s : ℝ) * Real.cos ((n : ℝ) * θ₀))

private def finiteNodeSpike (θ₀ : ℝ) (R n : ℕ) (v : ℝ → ℝ) : Prop :=
  angleRowValue v θ₀ n = 1 ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n →
      angleRowValue v θ₀ j = 0) ∧
    (∀ s : ℕ, Odd s → s ≤ R → ∀ k : Fin (n * s),
      primitiveNode (n * s) (chebyshevAngle (n * s) k) →
        v (chebyshevAngle (n * s) k) =
          finiteSpikeCoefficient θ₀ n s /
            primitiveMass θ₀ (n * s) *
              Real.sign (explicitLambdaWeight θ₀ (n * s) k)) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ R * n → ∀ k : Fin j,
      (¬ ∃ s : ℕ, Odd s ∧ s ≤ R ∧ j = n * s ∧
        primitiveNode j (chebyshevAngle j k)) →
          v (chebyshevAngle j k) = 0)

private def tentReplacement (θ₀ : ℝ) (R n : ℕ) (v ψ : ℝ → ℝ) : Prop :=
  ContinuousOn ψ (Icc 0 Real.pi) ∧
    angleVanishingNear ψ θ₀ ∧
    (∀ s : ℕ, Odd s → s ≤ R → ∀ k : Fin (n * s),
      primitiveNode (n * s) (chebyshevAngle (n * s) k) →
        ψ (chebyshevAngle (n * s) k) =
          v (chebyshevAngle (n * s) k))

private def supNormOn (ψ : ℝ → ℝ) : ℝ :=
  sSup ((fun θ : ℝ => |ψ θ|) '' Icc 0 Real.pi)

/-- Claim 31365: for a fixed evaluation angle, one fixed positive cosine
lower bound works on arbitrarily large good dyadic rows.  On every sufficiently
large such row, continuous triangular-tent replacement of the finite primitive
node spike preserves the finite cancellation window, has the prescribed future
control, and obeys the `C_R / log n` norm bound. -/
def claim31365 : Prop :=
  ∀ θ₀ : ℝ, θ₀ ∈ Icc 0 Real.pi →
    ∃ eta : ℕ → ℝ,
      Tendsto eta atTop (𝓝 0) ∧
        ∃ C : ℕ → ℝ,
          ∀ R : ℕ, Odd R → 0 < R →
            ∃ κ : ℝ, 0 < κ ∧
              ∃ N : ℕ,
                (∀ n : ℕ, N ≤ n → goodDyadicRow θ₀ R n κ →
                  ∀ delta : ℝ, 0 < delta →
                    ∃ v ψ : ℝ → ℝ,
                      finiteNodeSpike θ₀ R n v ∧
                        tentReplacement θ₀ R n v ψ ∧
                        angleRowValue ψ θ₀ n = 1 ∧
                        (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n →
                          angleRowValue ψ θ₀ j = 0) ∧
                        (∀ j : ℕ, R * n < j →
                          |angleRowValue ψ θ₀ j| ≤ eta R + delta) ∧
                        supNormOn ψ ≤ C R / Real.log (n : ℝ)) ∧
                (∀ B : ℕ, ∃ n : ℕ, B ≤ n ∧ N ≤ n ∧
                  goodDyadicRow θ₀ R n κ)

end MathlibPlus.Open.ResearchFormalizationBatchR1991Claim31365Repair
