import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Claim 21928: the scalar maximum has only the stated endpoint and
interior critical-point candidates; a zero of the affine factor has value
zero. -/
def claim21928 : Prop :=
  ∀ (n : ℕ) (δ η B : ℝ),
    0 < n → 0 < η → 0 ≤ B →
      let f : ℝ → ℝ := fun s => s ^ (n - 1) * |δ + η * s|
      let s₀ : ℝ := -((n : ℝ) - 1) * δ / ((n : ℝ) * η)
      (∃ s : ℝ,
        0 ≤ s ∧ s ≤ B ∧
        (∀ t : ℝ, 0 ≤ t → t ≤ B → f t ≤ f s) ∧
        (s = B ∨ (0 ≤ s₀ ∧ s₀ ≤ B ∧ s = s₀))) ∧
      (∀ s : ℝ, 0 ≤ s → s ≤ B → δ + η * s = 0 →
        f s = 0 ∧ ¬(0 < f s))

/-- Claim 21929: the explicit affine target evaluation is positive on a
positive interior chamber whenever the slice parameter is at least the
normalizing constant, so a zero requires a smaller slice parameter. -/
def claim21929 : Prop :=
  ∀ (n : ℕ) (a m K : ℝ) (η z : Fin (n - 1) → ℝ),
    2 ≤ n → 0 < K →
      (∀ i, 0 < η i) → (∀ i, 0 < z i) →
        let cT : ℝ :=
          K * ((m - a) / 2 + Finset.univ.sum (fun i => η i * z i))
        (a ≤ m → 0 < cT) ∧ (cT = 0 → m < a)

/-- Claim 21930: with the Lehmer value a=3, the 3- and 5-slices are
strictly positive, and among the 1-, 3-, and 5-slices only the 1-slice can
lie on the target-evaluation wall. -/
def claim21930 : Prop :=
  ∀ (n : ℕ) (K : ℝ) (η z : Fin (n - 1) → ℝ),
    2 ≤ n → 0 < K →
      (∀ i, 0 < η i) → (∀ i, 0 < z i) →
        let σ : ℝ := Finset.univ.sum (fun i => η i * z i)
        (0 < K * (((3 : ℝ) - 3) / 2 + σ)) ∧
        (0 < K * (((5 : ℝ) - 3) / 2 + σ)) ∧
        (∀ m : ℤ,
          (m = 1 ∨ m = 3 ∨ m = 5) →
            K * (((m : ℝ) - 3) / 2 + σ) = 0 → m = 1)

end MathlibPlus.Open.Analysis
