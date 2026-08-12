import Mathlib

namespace MathlibPlus.Analysis.Claim54103

/-- The exact post-allowance comparison displayed in R-4947. -/
theorem postAllowanceArithmetic :
    ((8545729448836918 / 10000000000000000 : ℝ) - 3 / 2500 =
        8533729448836918 / 10000000000000000) ∧
      (8533729448836918 / 10000000000000000 : ℝ) >
        8501142797379526 / 10000000000000000 := by
  norm_num

end MathlibPlus.Analysis.Claim54103
