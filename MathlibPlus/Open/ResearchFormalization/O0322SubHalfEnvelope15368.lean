import Mathlib
import MathlibPlus.Open.ResearchFormalization.O0322TruncatedExponential
import MathlibPlus.Open.ResearchFormalization.LaguerreEnvelope15369

open Filter
open scoped Topology

namespace MathlibPlus.Open.ResearchFormalization.O0322

noncomputable section

/-- Eventual polynomial growth of a Laguerre-transform sequence. -/
def polynomialTransformBound15368 (F : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ,
    ∀ᶠ d : ℕ in atTop,
      |F d| ≤ C * (1 + (d : ℝ)) ^ k

/-- Eventual tempered growth of a Laguerre-transform sequence. -/
def temperedTransformBound15368 (F : ℕ → ℝ) : Prop :=
  ∃ C p : ℝ, 0 < C ∧ 0 ≤ p ∧
    ∀ᶠ d : ℕ in atTop,
      |F d| ≤ C * Real.rpow (1 + (d : ℝ)) p

/-- Subexponential growth in the transform degree. -/
def expLittleOBound15368 (F : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ d : ℕ in atTop,
      |F d| ≤ Real.exp (ε * (d : ℝ))

/-- Claim 15368: every eventually positive envelope whose logarithmic
limsup rate is below one half dominates a fixed truncated exponential whose
canonical Laguerre transforms grow exponentially. -/
def claim15368 : Prop :=
  ∀ E : ℝ → ℝ,
    (∀ᶠ t : ℝ in atTop, 0 < E t) ∧
      limsup (fun t : ℝ => -Real.log (E t) / t) atTop < 1 / 2 →
    ∃ δ T : ℝ,
      0 < δ ∧ δ < 1 / 2 ∧ 0 < T ∧
        (∀ t : ℝ, t < T →
          truncatedExponential15367 δ T t = 0) ∧
        (∀ t : ℝ, 0 ≤ t →
          truncatedExponential15367 δ T t ≤ E t) ∧
        ∃ c : ℝ,
          0 < c ∧
            (∀ᶠ d : ℕ in atTop,
              c * ((1 - δ) / δ) ^ d ≤
                  |laguerreTransform15367
                    (truncatedExponential15367 δ T) d| ∧
                0 < (-1 : ℝ) ^ d *
                  laguerreTransform15367
                    (truncatedExponential15367 δ T) d) ∧
            ¬ polynomialTransformBound15368
                (laguerreTransform15367 (truncatedExponential15367 δ T)) ∧
            ¬ temperedTransformBound15368
                (laguerreTransform15367 (truncatedExponential15367 δ T)) ∧
            ¬ expLittleOBound15368
                (laguerreTransform15367 (truncatedExponential15367 δ T))

end

end MathlibPlus.Open.ResearchFormalization.O0322
