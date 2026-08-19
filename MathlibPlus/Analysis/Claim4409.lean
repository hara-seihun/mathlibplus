import Mathlib

namespace MathlibPlus.Analysis.Claim4409

noncomputable section

/-- Claim 4409: the normalized parameter-two Laguerre recurrence and its
literal shifted-feature consequence. -/
def shiftedFeatureRecurrence : Prop :=
  ∀ (L : ℕ → Polynomial ℚ),
    L 0 = 1 →
    L 1 = 3 - Polynomial.X →
    (∀ n : ℕ,
      Polynomial.C (n + 2 : ℚ) * L (n + 2) =
        (Polynomial.C ((2 : ℚ) * (n : ℚ) + 5) - Polynomial.X) * L (n + 1) -
          Polynomial.C ((n : ℚ) + 3) * L n) →
    let v : ℕ → Polynomial ℚ := fun k =>
      match k with
      | 0 => 0
      | 1 => 0
      | k + 2 => L k
    ∀ n : ℕ,
      Polynomial.C (n + 2 : ℚ) * v (n + 4) =
        (Polynomial.C ((2 : ℚ) * (n : ℚ) + 5) - Polynomial.X) * v (n + 3) -
          Polynomial.C ((n : ℚ) + 3) * v (n + 2)

end

end MathlibPlus.Analysis.Claim4409
