import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R2605PairedSignConjugation

noncomputable section

/-- Claim 42775: opposite-sign exponential stacks on shared real source and
target nodes are obtained from one sign by conjugating coefficients and output. -/
def pairedSignConjugation_claim42775 : Prop :=
  ∀ (n m : ℕ) (x : Fin n → ℝ) (s : Fin m → ℝ)
    (c : Fin n → ℂ),
    let F : ℝ → (Fin n → ℂ) → Fin m → ℂ :=
      fun σ d k =>
        ∑ j : Fin n,
          d j * Complex.exp
            (Complex.I * (σ : ℂ) * (s k : ℂ) * (x j : ℂ))
    let cbar : Fin n → ℂ := fun j => (starRingEnd ℂ) (c j)
    ∀ k : Fin m,
      F (-1) c k = (starRingEnd ℂ) (F 1 cbar k)

end

end MathlibPlus.Open.ResearchFormalization.R2605PairedSignConjugation
