import Mathlib

namespace MathlibPlus.Open.NumberTheory

/-- The divisor-closed, lower-triangular prefix structure in admitted claim 15214. -/
def claim15214 : Prop :=
  let divisors : ℕ → Finset ℕ := fun n =>
    (Finset.Icc 1 n).filter (fun d => d ∣ n)
  let properDivisors : ℕ → Finset ℕ := fun n =>
    (Finset.Icc 2 (n - 1)).filter (fun d => d ∣ n)
  let convolution : (ℕ → ℝ) → ℕ → ℝ := fun a n =>
    ∑ d ∈ divisors n, a d * a (n / d)
  let S : (ℕ → ℝ) → ℕ → ℝ := fun a n =>
    a n * Real.log n + convolution a n
  ∀ (N : ℕ) (a : ℕ → ℝ),
    a 1 = 0 →
    ∀ n, 2 ≤ n → n ≤ N →
      (∀ d, d ∈ divisors n →
        a d * a (n / d) ≠ 0 →
          d ∈ properDivisors n ∧ n / d ∈ properDivisors n) ∧
      S a n = a n * Real.log n +
        ∑ d ∈ properDivisors n, a d * a (n / d) ∧
      (∀ d, d ∣ n → d ≤ N ∧ n / d ≤ N) ∧
      (∀ b : ℕ → ℝ, b 1 = 0 →
        (∀ k, k < n → a k = b k) →
        S a n - S b n = (a n - b n) * Real.log n)

end MathlibPlus.Open.NumberTheory
