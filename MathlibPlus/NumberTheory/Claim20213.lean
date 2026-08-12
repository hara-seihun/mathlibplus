import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

namespace MathlibPlus.NumberTheory

/--
Formalization of claim 20213.  The source says "integer `k`" while using a
natural binomial coefficient; the Lean statement uses `k : ℕ`, which is the
unambiguous domain of `Nat.choose` on the displayed range.
-/
theorem claim20213 :
    (∀ k : ℕ, 3 ≤ k → k ≤ 8 →
      (7 * (k : ℚ)) / (10 * ((Nat.choose 30000 k : ℚ) - 1))
        < 1 / (3 * (690989 : ℚ)^2)) ∧
      Nat.choose 30000 3 = 4499550010000 ∧
      3 * (690989 : ℕ)^2 = 1432397394363 ∧
      (7 : ℚ) / 14998500033330 < 1 / 1432397394363 := by
  constructor
  · intro k hk3 hk8
    interval_cases k <;>
      rw [Nat.choose_eq_descFactorial_div_factorial] <;>
      norm_num [Nat.descFactorial]
  constructor
  · rw [Nat.choose_eq_descFactorial_div_factorial]
    norm_num [Nat.descFactorial]
  constructor <;> norm_num

end MathlibPlus.NumberTheory
