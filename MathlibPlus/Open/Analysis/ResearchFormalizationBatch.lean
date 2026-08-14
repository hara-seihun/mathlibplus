import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

/--
The shifted Blaschke-product logarithmic identity from admitted Claim 3320.
The node convention is the one supplied by its exact repair context,
`s_j = y_j - i t_j`; the displayed identity is retained verbatim.
-/
def shiftedBlaschkeLogIdentity (y t : ℕ → ℝ) : Prop :=
  ∀ (θ : ℝ) (n : ℕ) (ξ : ℝ),
    0 < θ → θ < 1 →
      let σ_n : ℝ := θ * y n
      let w : ℂ := -(σ_n : ℂ) + Complex.I * (ξ : ℂ)
      let B : ℂ :=
        Finset.prod (Finset.range n) (fun k =>
          (w - ((y k : ℂ) - Complex.I * (t k : ℂ))) /
            (w + star ((y k : ℂ) - Complex.I * (t k : ℂ))))
      Real.log (‖B‖ ^ 2) =
        Finset.sum (Finset.range n) (fun k =>
          Real.log (((y k + σ_n) ^ 2 + (ξ - t k) ^ 2) /
            ((y k - σ_n) ^ 2 + (ξ - t k) ^ 2)))

end MathlibPlus.Open.Analysis
