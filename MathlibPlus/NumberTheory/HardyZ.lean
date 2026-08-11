import Mathlib

/-!
# Hardy's Z function

The exact normalization used by the certified zero computations in admitted claim 265
from packet `C-0017`.
-/

namespace MathlibPlus.NumberTheory

/-- The Riemann--Siegel theta normalization
`Im(log Γ(1/4 + it/2)) - (t/2) log π`. -/
noncomputable def hardyTheta (t : ℝ) : ℝ :=
  (Complex.log (Complex.Gamma ((1 / 4 : ℂ) + (t / 2 : ℝ) * Complex.I))).im -
    (t / 2) * Real.log Real.pi

/-- Hardy's function in the normalization used by the certificate. -/
noncomputable def hardyZ (t : ℝ) : ℂ :=
  Complex.exp (Complex.I * hardyTheta t) *
    riemannZeta ((1 / 2 : ℂ) + t * Complex.I)

end MathlibPlus.NumberTheory
