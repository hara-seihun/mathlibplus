import Mathlib

namespace MathlibPlus.Open.Research.Batch_01a00468_FreeJacobi

noncomputable section

/-- The pivot data and free block hypotheses used by Claims 8531, 8534, and 8535. -/
def freeJacobiData (a b : ℕ) (c : ℝ)
    (α β q : ℕ → ℝ) : Prop :=
  1 ≤ a ∧ a ≤ b ∧ 0 < c ∧
  (∀ n : ℕ, 0 < β n) ∧
  q 0 = α 0 ∧
  (∀ n : ℕ, q (n + 1) = α (n + 1) - β (n + 1) ^ 2 / q n) ∧
  (∀ n : ℕ, 0 < q n) ∧
  (∀ n : ℕ, a ≤ n → n ≤ b → α n = 2 * c ∧ β n = c)

def freePivotR (q : ℕ → ℝ) (k : ℕ) : ℝ := Real.sqrt (q k)

def freePivotS (β q : ℕ → ℝ) (k : ℕ) : ℝ :=
  β k / Real.sqrt (q (k - 1))

/-- Claim 8531: the two-sided inverse-distance pivot bound. -/
def claim8531 : Prop :=
  ∀ (a b : ℕ) (c : ℝ) (α β q : ℕ → ℝ),
    freeJacobiData a b c α β q →
    ∀ k : ℕ, a ≤ k → k ≤ b →
      -1 / ((b - k + 1 : ℕ) : ℝ) < q k / c - 1 ∧
      q k / c - 1 ≤ 1 / ((k - a + 1 : ℕ) : ℝ)

/-- Claim 8534: the boundary-sensitive logarithmic estimate. -/
def claim8534 : Prop :=
  ∀ (a b : ℕ) (c : ℝ) (α β q : ℕ → ℝ),
    freeJacobiData a b c α β q →
    ∀ k : ℕ, a ≤ k → k < b →
      |Real.log (freePivotR q k / freePivotS β q (k + 1))| ≤
        max
          (Real.log (1 + 1 / ((k - a + 1 : ℕ) : ℝ)))
          (-Real.log (1 - 1 / ((b - k + 1 : ℕ) : ℝ)))

/-- Claim 8535: the uniform interior free-coefficient estimate. -/
def claim8535 : Prop :=
  ∀ (a b : ℕ) (c : ℝ) (α β q : ℕ → ℝ) (ℓ : ℕ),
    1 ≤ ℓ → freeJacobiData a b c α β q →
    ∀ k : ℕ,
      a + ℓ - 1 ≤ k → k ≤ b - ℓ →
      |Real.log (freePivotR q k / freePivotS β q (k + 1))| ≤
          Real.log (1 + 1 / (ℓ : ℝ)) ∧
      |Real.log (freePivotR q k / Real.sqrt c)| ≤
          (1 / 2 : ℝ) * Real.log (1 + 1 / (ℓ : ℝ)) ∧
      |Real.log (freePivotS β q (k + 1) / Real.sqrt c)| ≤
          (1 / 2 : ℝ) * Real.log (1 + 1 / (ℓ : ℝ))

end
end MathlibPlus.Open.Research.Batch_01a00468_FreeJacobi
