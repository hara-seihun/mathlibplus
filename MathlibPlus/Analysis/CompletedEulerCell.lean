import MathlibPlus.Basic

namespace MathlibPlus.Analysis.CompletedEulerCell

/-!
Claim 18066.  The packet does not specify a different branch for complex
powers, so the definitions use Mathlib's principal `Complex.cpow` convention.
-/

/-- The completed gamma factor `g(s) = π^(-s/2) Γ(1+s/2)`. -/
noncomputable def completedEulerGammaFactor (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (1 + s / 2)

/-- The completed Euler cell
`C_n(s) = g(s) ((n+s)(n+1)^(-s) - n^(1-s))`. -/
noncomputable def completedEulerCell (n : ℕ) (s : ℂ) : ℂ :=
  completedEulerGammaFactor s *
    (((n : ℂ) + s) * ((n : ℂ) + 1) ^ (-s) - (n : ℂ) ^ (1 - s))

end MathlibPlus.Analysis.CompletedEulerCell
