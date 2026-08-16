import Mathlib
import MathlibPlus.Open.ResearchFormalization.O0353Batch

namespace MathlibPlus.Open.ResearchFormalization

/--
Claim 15595.  The quartet is the explicitly displayed finite set, so its
conjugation and reflection closure records the manually inserted symmetry;
there is deliberately no functional-equation identity in this statement.
The corrected product is the displayed meromorphic shifted-zeta quotient.
-/
def claim15595 : Prop :=
  ∃ (α τ : ℝ) (u : ℕ → ℝ) (C : ℝ) (Y₀ : ℕ),
    0 < α ∧ α < (1 : ℝ) / 2 ∧ 0 < τ ∧ 0 ≤ C ∧
      (∀ a ∈ symmetricQuartet α τ,
        star a ∈ symmetricQuartet α τ ∧
          1 - a ∈ symmetricQuartet α τ) ∧
      (∀ Y : ℕ, Y₀ ≤ Y →
        |u Y| ≤ C * Real.rpow (Y : ℝ) (-α) ∧
          weightedPerturbation α τ Y + correctionMass Y (u Y) = 0 ∧
          (∀ a ∈ symmetricQuartet α τ,
            correctedZetaProduct α τ Y (u Y) a = 0 ∧
              ∃ d : ℂ,
                HasDerivAt (correctedZetaProduct α τ Y (u Y)) d a ∧
                  d ≠ 0) ∧
          Meromorphic (correctedZetaProduct α τ Y (u Y)) ∧
          ¬ Differentiable ℂ (correctedZetaProduct α τ Y (u Y)))

end MathlibPlus.Open.ResearchFormalization
