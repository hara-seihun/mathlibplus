import Mathlib

namespace MathlibPlus.Open.Research.O0020

open Matrix

private def r00 : ℚ := 160496426371809 / (10 : ℚ) ^ 12
private def r01 : ℚ := 43660509388231 / (10 : ℚ) ^ 12
private def r11 : ℚ := 11297772918323 / (10 : ℚ) ^ 12

/-- The reported symmetric rational approximation, with the decimal entries
retained exactly as rationals. -/
def reportedScarweaveSusceptibility : Matrix (Fin 2) (Fin 2) ℚ :=
  fun i j =>
    if i.val = 0 then
      if j.val = 0 then r00 else r01
    else
      if j.val = 0 then r01 else r11

end MathlibPlus.Open.Research.O0020
