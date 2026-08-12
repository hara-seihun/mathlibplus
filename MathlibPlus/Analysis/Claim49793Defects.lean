import Mathlib

namespace MathlibPlus.Analysis.Claim49793

/-- Signed first-block defect from admitted claim 49793, written with natural
powers of reciprocal rationals (equivalent to the source's 2^-m and 4^-m). -/
def signedDefect_claim49793 (m : ℕ) : ℚ :=
  5 / 27 - (68 / 9) * ((2 : ℚ)⁻¹)^m +
    (64 / 27) * ((4 : ℚ)⁻¹)^m

/-- Exact PL defect from admitted claim 49793. -/
def plDefect_claim49793 (m : ℕ) : ℚ :=
  -(64 / 9) * ((2 : ℚ)⁻¹)^m +
    (16 / 9) * ((4 : ℚ)⁻¹)^m

end MathlibPlus.Analysis.Claim49793
