import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

namespace MathlibPlus.Analysis.Claim49137

/--
The exact decrement profiles and the resulting four-coordinate max-root gap
from claim 49137.  The finite maximum is expanded over `Fin 4`; all four
coordinate sums are equal, so this is independent of the displayed nesting.
-/
theorem decrementProfiles_and_rootExchangeGap_claim49137 :
    let ah : Fin 4 → ℚ := ![3 / 4, 3 / 4, 0, 0]
    let ak : Fin 4 → ℚ := ![0, 0, 3 / 4, 3 / 4]
    let ahk : Fin 4 → ℚ := ![15 / 16, 15 / 16, 15 / 16, 15 / 16]
    ah = ![3 / 4, 3 / 4, 0, 0] ∧
      ak = ![0, 0, 3 / 4, 3 / 4] ∧
      ahk = ![15 / 16, 15 / 16, 15 / 16, 15 / 16] ∧
      (15 / 16 : ℚ) - max (ah 0 + ak 0)
        (max (ah 1 + ak 1) (max (ah 2 + ak 2) (ah 3 + ak 3))) = 3 / 16 ∧
      (0 : ℚ) < 3 / 16 := by
  dsimp
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · norm_num
  · norm_num

end MathlibPlus.Analysis.Claim49137
