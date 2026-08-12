import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Ring

namespace MathlibPlus.NumberTheory

/--
Claim 29535 (packet `R-0754`): the depth-two Newton identity for a monic
integer polynomial forces the second Newton sum to be congruent to the
square of the first modulo two.  Here `a₁` and `a₂` are the first two
monic-polynomial coefficients, so `S = -a₁` and `p₂ = a₁² - 2*a₂`.
-/
theorem claim29535_newton_parity
    (a₁ a₂ : ℤ) :
    let S : ℤ := -a₁
    let p₂ : ℤ := a₁ ^ 2 - 2 * a₂
    Int.ModEq 2 p₂ (S ^ 2) := by
  dsimp
  rw [Int.modEq_iff_dvd]
  use a₂
  ring

end MathlibPlus.NumberTheory
