import Mathlib.Tactic

namespace MathlibPlus
namespace Analysis

/--
The exact finite gate calculation in claim 48764.  The truth-table,
mean, three nonconstant Fourier coefficients, and the displayed arithmetic
for `Γ` are retained.  The source's expected-cost-optimal-tree interface and
its query-probability semantics are not reconstructed without an admitted
policy API.
-/
theorem exactTwoBitGateArithmetic_claim48764 :
    let G : ℚ → ℚ → ℚ := fun a b => if a = -1 then 1 else b
    let mean : ℚ :=
      (G (-1) (-1) + G (-1) 1 + G 1 (-1) + G 1 1) / 4
    let coeffA : ℚ :=
      ((-1) * G (-1) (-1) + (-1) * G (-1) 1 +
        1 * G 1 (-1) + 1 * G 1 1) / 4
    let coeffB : ℚ :=
      ((-1) * G (-1) (-1) + 1 * G (-1) 1 +
        (-1) * G 1 (-1) + 1 * G 1 1) / 4
    let coeffAB : ℚ :=
      (1 * G (-1) (-1) + (-1) * G (-1) 1 +
        (-1) * G 1 (-1) + 1 * G 1 1) / 4
    (∀ a b : ℚ, (a = -1 ∨ a = 1) → (b = -1 ∨ b = 1) →
      G a b = 1 / 2 - a / 2 + b / 2 + a * b / 2) ∧
      mean = 1 / 2 ∧
      coeffA = -1 / 2 ∧ coeffB = 1 / 2 ∧ coeffAB = 1 / 2 ∧
      |coeffA| = 1 / 2 ∧ |coeffB| = 1 / 2 ∧ |coeffAB| = 1 / 2 ∧
      ((1 / 4 : ℚ) + (1 / 4) / (1 / 2) +
        (1 / 4) / (1 / 2) = 5 / 4) := by
  dsimp
  constructor
  · intro a b ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num
  · norm_num

end Analysis
end MathlibPlus
