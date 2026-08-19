import Mathlib

/-!
# Boundary parameter-flux pencil

The coordinate formula from admitted claim 234. Evenness and Fourier-source reality
are not needed to define the pencil, so the definitions accept an arbitrary complex
transform `Xi`; later positivity claims may impose the source hypotheses.
-/

namespace MathlibPlus.Analysis.BoundaryFlux

/-- The shifted boundary profile `A(q) = Xi(q + iω)`. -/
noncomputable def profile (Xi : ℂ → ℂ) (ω q : ℝ) : ℂ :=
  Xi ((q : ℂ) + (ω : ℂ) * Complex.I)

/-- The real-parameter derivative `Ȧ(q) = ∂_ω A(q)`, represented as a real
Fréchet derivative applied to `1`. -/
noncomputable def parameterDerivative (Xi : ℂ → ℂ) (ω q : ℝ) : ℂ :=
  (fderiv ℝ (fun η : ℝ => profile Xi η q) ω) 1

/-- Real-coordinate derivative of a complex-valued profile. -/
noncomputable def coordinateDerivative (f : ℝ → ℂ) (q : ℝ) : ℂ :=
  (fderiv ℝ f q) 1

/-- The boundary parameter-flux kernel. The diagonal branch deliberately carries
the essential leading minus sign from the diagonal limit in admitted claim 234. -/
noncomputable def boundaryParameterFlux (Xi : ℂ → ℂ) (ω p q : ℝ) : ℝ :=
  let A := profile Xi ω
  let dotA := parameterDerivative Xi ω
  if p = q then
    -(1 / 4 : ℝ) *
      ((coordinateDerivative dotA p * star (A p)).im -
        (dotA p * star (coordinateDerivative A p)).im)
  else
    ((dotA q * star (A p)).im - (dotA p * star (A q)).im) /
      (4 * (p - q))

/-- Off the diagonal, the boundary flux is the divided antisymmetrized imaginary
pairing. -/
theorem boundaryParameterFlux_of_ne (Xi : ℂ → ℂ) (ω : ℝ) {p q : ℝ}
    (hpq : p ≠ q) :
    boundaryParameterFlux Xi ω p q =
      (((parameterDerivative Xi ω q) * star (profile Xi ω p)).im -
        ((parameterDerivative Xi ω p) * star (profile Xi ω q)).im) /
          (4 * (p - q)) := by
  simp [boundaryParameterFlux, hpq]

/-- On the diagonal, the exact limit formula has the essential minus sign. -/
theorem boundaryParameterFlux_self (Xi : ℂ → ℂ) (ω p : ℝ) :
    boundaryParameterFlux Xi ω p p =
      -(1 / 4 : ℝ) *
        ((coordinateDerivative (parameterDerivative Xi ω) p *
            star (profile Xi ω p)).im -
          ((parameterDerivative Xi ω p) *
            star (coordinateDerivative (profile Xi ω) p)).im) := by
  simp [boundaryParameterFlux]

end MathlibPlus.Analysis.BoundaryFlux
