import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim12833

/-- The centered Niemeier variation has the null Lorentz coordinates recorded
in claim 12833 (source O-0074, Eq. 2.10). -/
theorem claim12833_centeredLorentzNull (hL : ℝ) :
    let aL : ℝ := 24 * (hL - 2730 / 691)
    let δh : Fin 3 → ℝ := ![aL / 2, 0, -aL / 2]
    δh 0 ^ 2 - δh 1 ^ 2 - δh 2 ^ 2 = 0 := by
  dsimp
  ring

/-- The null identity is independent of the value of the centered class
coordinate itself. -/
theorem claim12833_lorentzNull_forAny (aL : ℝ) :
    (aL / 2) ^ 2 - (0 : ℝ) ^ 2 - (-aL / 2) ^ 2 = 0 := by
  ring

end MathlibPlus.LinearAlgebra.Claim12833
