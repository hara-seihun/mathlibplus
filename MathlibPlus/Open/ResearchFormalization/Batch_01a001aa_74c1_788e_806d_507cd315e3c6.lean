import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Batch_01a001aa_74c1_788e_806d_507cd315e3c6

/-- A positive slope-rate pair reconstructs the real and squared-imaginary
coordinates of a selected zero, leaving only complex conjugation. -/
def reconstruction_up_to_conjugation : Prop :=
  ∀ (beta gamma d kappa : ℝ),
    0 < d →
    d = 1 / ((beta - 1)^2 + gamma^2) →
    kappa = (2 * beta - 1) * d →
    beta = (1 / 2) * (1 + kappa / d) ∧
      gamma^2 = 1 / d - (1 / 4) * (1 - kappa / d)^2 ∧
        ∀ (beta' gamma' : ℝ),
          d = 1 / ((beta' - 1)^2 + gamma'^2) →
          kappa = (2 * beta' - 1) * d →
          beta' = beta ∧
            gamma'^2 = gamma^2 ∧
              ((beta' = beta ∧ gamma' = gamma) ∨
                (beta' = beta ∧ gamma' = -gamma))

/-- The local rate profile has peak height κ and curvature -1/d, and these
observables together with the Cayley slope-rate coordinates determine the
selected zero up to conjugation. -/
def height_and_curvature_recover_slope_rate : Prop :=
  ∀ (d kappa : ℝ),
    0 < d →
    let Ψ : ℝ → ℝ := fun q =>
      kappa - (d - q + q * Real.log (q / d))
    (∀ q : ℝ, 0 < q → Ψ q ≤ kappa) ∧
      Ψ d = kappa ∧
        (∀ q : ℝ, 0 < q → (Ψ q = kappa ↔ q = d)) ∧
          HasDerivAt (deriv Ψ) (-1 / d) d ∧
            (∀ (d' kappa' : ℝ),
              0 < d' →
              kappa' = kappa →
              -1 / d' = -1 / d →
              d' = d ∧ kappa' = kappa) ∧
              (∀ (rho rho' : ℂ),
                d = Complex.normSq (1 / (rho - 1)) →
                kappa = Complex.normSq (rho / (rho - 1)) - 1 →
                d = Complex.normSq (1 / (rho' - 1)) →
                kappa = Complex.normSq (rho' / (rho' - 1)) - 1 →
                rho' = rho ∨ rho' = star rho)

/-- The exact midpoint Jensen gap obeys the stated quantitative
strong-convexity lower bound on the positive quadrant. -/
def quantitative_strong_convexity_gap : Prop :=
  let D : ℝ → ℝ → ℝ := fun t s =>
    (Real.rpow t (2 / 3 : ℝ) + Real.rpow s (2 / 3 : ℝ)) / 2 -
      Real.rpow ((Real.sqrt t + Real.sqrt s) / 2) (4 / 3 : ℝ)
  ∀ (t s : ℝ),
    0 < t →
    0 < s →
    D t s ≥
      (Real.sqrt t - Real.sqrt s)^2 /
        (18 * Real.rpow (max t s) (1 / 3 : ℝ))

/-- Equality of derivatives on a two-sided unbounded set, together with a
monotone derivative difference and one anchor value, reconstructs the two
functions globally. -/
def anchored_monotone_unbounded_derivative_reconstruction : Prop :=
  ∀ (f g : ℝ → ℝ) (S : Set ℝ) (a : ℝ),
    Differentiable ℝ f →
    Differentiable ℝ g →
    (∀ x : ℝ, x ∈ S → deriv f x = deriv g x) →
    Monotone (fun x : ℝ => deriv f x - deriv g x) →
    (∀ B : ℝ, ∃ x : ℝ, x ∈ S ∧ B < x) →
    (∀ B : ℝ, ∃ x : ℝ, x ∈ S ∧ x < B) →
    f a = g a →
    f = g

end MathlibPlus.Open.ResearchFormalization.Batch_01a001aa_74c1_788e_806d_507cd315e3c6
