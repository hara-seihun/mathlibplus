import Mathlib

namespace MathlibPlus.Combinatorics.SpiderWeights

noncomputable section
local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Claim 43160: the full coefficient weight from the displayed midpoint
 defect is antisymmetric on the odd diagonal. -/
theorem spiderWeight_antisymm_full
    (a b i j : ℕ)
    (_ha : 0 < a)
    (hab : a ≤ b)
    (hi : i ≤ a + b)
    (hsum : i + j = 2 * a + 2 * b + 1) :
    let ind : Prop → ℤ := fun p => if p then 1 else 0
    let w : ℕ → ℕ → ℤ := fun x y =>
      -ind (y > 2 * b) + 2 * ind (y > a + b) - ind (y > 2 * a) +
        ind (x > a) * ind (y > a) +
        2 * ind (x > a) * ind (y > 2 * b) -
        2 * ind (x > a) * ind (y > b) -
        2 * ind (x > a) * ind (y > a + b) -
        2 * ind (x > b) * ind (y > a + b) +
        2 * ind (x > 2 * a) * ind (y > b) +
        ind (x > b) * ind (y > b)
    (w i j =
        ind (i > 2 * a) - ind (i > a) - ind (i > b)) ∧
      w j i = -w i j := by
  classical
  have hj : a + b < j := by omega
  have hia_b : ¬ i > a + b := by omega
  have hja : j > a := by omega
  have hjb : j > b := by omega
  have hj2a : j > 2 * a := by omega
  dsimp
  constructor <;>
    by_cases hia : i > a <;>
    by_cases hib : i > b <;>
    by_cases hi2a : i > 2 * a <;>
    by_cases hj2b : j > 2 * b <;>
    simp_all <;> omega

end

end MathlibPlus.Combinatorics.SpiderWeights
