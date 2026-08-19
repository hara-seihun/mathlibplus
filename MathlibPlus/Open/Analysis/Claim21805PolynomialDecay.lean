import Mathlib

open Filter
open _root_.Asymptotics
noncomputable section

namespace MathlibPlus.Open.Analysis.Claim21805PolynomialDecay

/-- Claim 21805: a cubic scale and norm decay exponent above one third give
summability of the norm sequence. -/
def claim21805_polynomialLocalDecayThreshold : Prop :=
  ∀ {E : Type*} [Norm E]
    (V : ℕ → E) (T : ℕ → ℝ) (C p : ℝ),
    0 ≤ C →
    1 / 3 < p →
    (∀ j : ℕ, T j = C * (j : ℝ) ^ 3) →
    (fun j : ℕ => ‖V j‖) =O[atTop]
      (fun j : ℕ => (T j) ^ (-p : ℝ)) →
    Summable (fun j : ℕ => ‖V j‖)

end MathlibPlus.Open.Analysis.Claim21805PolynomialDecay
