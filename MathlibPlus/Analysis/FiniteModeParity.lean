import Mathlib

namespace MathlibPlus.Analysis

/--
Claim 12434: for positive modes and an odd function `ψ`, the difference of
its even and odd divided-difference blocks is
`2 * (ψ m + ψ n) / (m + n)`.  The diagonal branch of the divided difference
is explicitly interpreted as `deriv ψ`.
-/
theorem finiteModeParityDifference_claim12434
    (ψ : ℝ → ℝ) (hodd : ∀ x : ℝ, ψ (-x) = -ψ x)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    let Q : ℝ → ℝ → ℝ :=
      fun x y => if x = y then deriv ψ x else (ψ x - ψ y) / (x - y)
    let E : ℝ → ℝ → ℝ := fun x y => Q x y + Q x (-y)
    let O : ℝ → ℝ → ℝ := fun x y => Q x y - Q x (-y)
    E m n - O m n = 2 * (ψ m + ψ n) / (m + n) := by
  dsimp
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmn : (m : ℝ) ≠ -(n : ℝ) := by
    nlinarith
  rw [if_neg hmn]
  have hoddn : ψ (-(n : ℝ)) = -ψ (n : ℝ) := hodd (n : ℝ)
  rw [hoddn]
  ring

end MathlibPlus.Analysis
