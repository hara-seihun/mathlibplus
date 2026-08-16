import Mathlib
import MathlibPlus.Open.Analysis.ConsecutiveNormDenominator

namespace MathlibPlus.Open.ResearchFormalization.CompactLambertNormTargetRefutation15202

open Filter
open MathlibPlus.Open.Analysis

noncomputable section

/-- The primitive moment-ratio carrier `rho_n = t_n/t_(n-1)`. -/
noncomputable def primitiveRatio
    (t : ℕ → ℝ) (n : ℕ) : ℝ :=
  t n / t (n - 1)

/-- The normalized terminal ratio whose old target is one and whose
corrected one-sixteenth law gives limit two. -/
noncomputable def normalizedTerminalRatio
    (h t : ℕ → ℝ) (n : ℕ) : ℝ :=
  32 * h n /
    (h (n - 1) * (primitiveRatio t n) ^ 2)

/-- The item-16 premises: the exact scalar product identity, the additive
compact-Lambert law, and the primitive ratio with its `1+o(1)` factor. -/
def oneSixteenthTerminalNormPremises
    (h a t : ℕ → ℝ) : Prop :=
  (∀ n : ℕ, 1 ≤ n →
    h n / h (n - 1) = (a (2 * n - 1) * a (2 * n)) ^ 2) ∧
  Tendsto
    (fun j : ℕ => 4 * (j : ℝ) * a j - compactLambertW j)
    atTop (nhds 0) ∧
  (∃ ε : ℕ → ℝ,
    Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        primitiveRatio t n =
          (compactLambertW (4 * n)) ^ 2 /
              (16 * (n : ℝ) ^ 2) *
            (1 + ε n))

/-- Claim 15202: under item 16's exact premises, the accepted one-sixteenth
law gives normalized limit two, so the repeated one-thirty-second target with
normalized limit one is asymptotically impossible. -/
def refuteOneThirtySecondNormTarget15202 : Prop :=
  ∀ (h a t : ℕ → ℝ),
    oneSixteenthTerminalNormPremises h a t →
      Tendsto
        (normalizedTerminalRatio h t)
        atTop (nhds 2) ∧
      ¬ Tendsto
        (normalizedTerminalRatio h t)
        atTop (nhds 1)

end

end MathlibPlus.Open.ResearchFormalization.CompactLambertNormTargetRefutation15202
