import Mathlib

/-!
# Single-shell boundary-flux and coordinate-Weyl positivity

Statement-fidelity registry node for admitted claim 240 (C-0015).  Both
kernels are expanded from the source formulas so the assertion is not
weakened to positivity of an unspecified family.
-/

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.BesselK

/-- For every positive shell parameter and every positive vertical shift,
the real boundary-flux kernel and the original coordinate Weyl kernel of
`cosh (α t) * exp (-β cosh (2t))` are positive semidefinite at every finite
set of real coordinates.

The Fourier transform convention is the source convention
`Xi z = ∫ t, Phi t * exp (i z t)`.  The diagonal branch of the flux retains
the load-bearing minus sign in the confluent limit. -/
noncomputable def singleShellFluxAndCoordinateWeylPositivity : Prop :=
  ∀ α β ω : ℝ, 0 < α → 0 < β → 0 < ω →
    let Φ : ℝ → ℝ := fun t =>
      Real.cosh (α * t) * Real.exp (-β * Real.cosh (2 * t))
    let Ξ : ℂ → ℂ := fun z =>
      ∫ t : ℝ, (Φ t : ℂ) * Complex.exp (Complex.I * z * (t : ℂ))
    let A : ℝ → ℝ → ℂ := fun η q => Ξ ((q : ℂ) + Complex.I * (η : ℂ))
    let dotA : ℝ → ℂ := fun q => deriv (fun η : ℝ => A η q) ω
    let boundaryFlux : ℝ → ℝ → ℝ := fun p q =>
      if p = q then
        -(1 / 4 : ℝ) *
          ((deriv dotA p * starRingEnd ℂ (A ω p)).im -
            (dotA p * starRingEnd ℂ (deriv (A ω) p)).im)
      else
        ((dotA q * starRingEnd ℂ (A ω p)).im -
          (dotA p * starRingEnd ℂ (A ω q)).im) / (4 * (p - q))
    let coordinateWeyl : ℝ → ℝ → ℝ := fun a b =>
      (1 / 2 : ℝ) * ∫ y in Set.Ici |(a + b) / 2|,
        y * Real.cosh (2 * ω * y) *
          Φ (y + (a - b) / 2) * Φ (y - (a - b) / 2)
    (∀ (n : ℕ) (p : Fin n → ℝ),
      Matrix.PosSemidef (fun i j => boundaryFlux (p i) (p j))) ∧
    ∀ (n : ℕ) (a : Fin n → ℝ),
      Matrix.PosSemidef (fun i j => coordinateWeyl (a i) (a j))

end MathlibPlus.Open.Analysis.BesselK
