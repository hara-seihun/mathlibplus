import Mathlib

namespace MathlibPlus.Open.NumberTheory.RiemannZeta

/-- Squaring `u + iγ` gives the exact angular defect from the negative real
axis, together with the stated positive-height bound. -/
def squareMapAngularDefect_claim451 : Prop :=
  ∀ (u γ : ℝ), γ ≠ 0 →
    let z : ℂ := ((u : ℂ) + Complex.I * (γ : ℂ)) ^ 2
    Real.pi - |Complex.arg z| =
        2 * Real.arctan (|u| / |γ|) ∧
      ∀ T : ℝ, 0 < T → |u| < 1 / 2 → T < |γ| →
        Real.pi - |Complex.arg z| <
          2 * Real.arctan (1 / (2 * T))

end MathlibPlus.Open.NumberTheory.RiemannZeta
