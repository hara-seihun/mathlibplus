import Mathlib

/-!
# Order-two completed-zeta curvature criterion

This registry node formalizes admitted claim 202. To bind the statement to the
completed-zeta radial kernel rather than to an arbitrary function, the standard
completed zeta `ξ`, its centered restriction `X`, logarithmic derivative `L`, and
radial descent `H` are all defined locally in the proposition. Both the non-strict
concavity-to-PSD inequality and strict-concavity-to-strict-determinant reading of
the source's converse are retained for fidelity review.
-/

namespace MathlibPlus.Open.Analysis

/-- The completed-zeta order-two local curvature inequalities, the exact second
 derivative of `w = (-H')⁻¹ᐟ²`, and the converse global two-node criterion. -/
def orderTwoCurvatureConcavityCriterion : Prop :=
  let xi : ℝ → ℝ := fun s =>
    ((1 / 2 : ℂ) * s * (s - 1) *
      Complex.cpow (Real.pi : ℂ) (-(s : ℂ) / 2) *
      Complex.Gamma ((s : ℂ) / 2) * riemannZeta s).re
  let X : ℝ → ℝ := fun r => xi (1 / 2 + r)
  let L : ℝ → ℝ := fun r => deriv X r / X r
  let H : ℝ → ℝ := fun x => L (Real.sqrt x) / Real.sqrt x
  let w : ℝ → ℝ := fun x =>
    1 / Real.sqrt (-deriv H x)
  (∀ x : ℝ, 1 / 4 < x →
    deriv H x < 0 ∧
    0 < 2 * deriv H x * iteratedDeriv 3 H x -
      3 * (iteratedDeriv 2 H x) ^ 2 ∧
    iteratedDeriv 2 w x =
      -(2 * deriv H x * iteratedDeriv 3 H x -
          3 * (iteratedDeriv 2 H x) ^ 2) /
        (4 * Real.rpow (-deriv H x) (5 / 2)) ∧
    iteratedDeriv 2 w x < 0) ∧
  StrictConcaveOn ℝ (Set.Ioi (1 / 4)) w ∧
  (ConcaveOn ℝ (Set.Ioi (1 / 4)) w →
    ∀ x y : ℝ, 1 / 4 < x → 1 / 4 < y → x ≠ y →
      ((H x - H y) / (y - x)) ^ 2 ≤ deriv H x * deriv H y) ∧
  (StrictConcaveOn ℝ (Set.Ioi (1 / 4)) w →
    ∀ x y : ℝ, 1 / 4 < x → 1 / 4 < y → x ≠ y →
      ((H x - H y) / (y - x)) ^ 2 < deriv H x * deriv H y)

end MathlibPlus.Open.Analysis
