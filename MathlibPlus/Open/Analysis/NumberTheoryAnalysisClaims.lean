import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open

/-- The exact summable packet majorant and Euler product identity. -/
def summablePacketMajorant : Prop :=
  let h : ℕ → ℝ := fun k =>
    1 / ((k : ℝ) * (∏ q ∈ k.primeFactors, ((q : ℝ) + 1)))
  let rad : ℕ → ℕ := fun k => ∏ q ∈ k.primeFactors, q
  let R : ℕ → ℝ → ℝ := fun q s =>
    (1 - Real.rpow (q : ℝ) (1 - s)) /
      (1 - Real.rpow (q : ℝ) (1 - s) / ((q : ℝ) + 1))
  (∀ s : ℝ, 1 ≤ s → ∀ k : ℕ, 0 < k →
      0 ≤ h k * (∏ q ∈ k.primeFactors, R q s) ∧
      h k * (∏ q ∈ k.primeFactors, R q s) ≤
        1 / ((k : ℝ) * (rad k : ℝ))) ∧
    Summable (fun k : {n : ℕ // 0 < n} =>
      1 / ((k.1 : ℝ) * (rad k.1 : ℝ))) ∧
    Multipliable (fun q : {p : ℕ // Nat.Prime p} =>
      (1 : ℝ) + 1 / ((q.1 : ℝ) * ((q.1 : ℝ) - 1))) ∧
    (∑' k : {n : ℕ // 0 < n},
      1 / ((k.1 : ℝ) * (rad k.1 : ℝ))) =
      (∏' q, (fun q : {p : ℕ // Nat.Prime p} =>
        (1 : ℝ) + 1 / ((q.1 : ℝ) * ((q.1 : ℝ) - 1))) q)

private def evenCharlierPolynomials : ℕ → Polynomial ℝ
  | 0 => 1
  | n + 1 =>
      Polynomial.X * (evenCharlierPolynomials n).derivative +
        (Polynomial.C (5 / 4 : ℝ) - Polynomial.X) * evenCharlierPolynomials n

/-- The even-Charlier recurrence and folded-kernel all-order identity. -/
def evenCharlierRecurrenceFoldedKernel : Prop :=
  let a : ℝ := 5 / 4
  evenCharlierPolynomials 0 = 1 ∧
    (∀ n : ℕ,
      evenCharlierPolynomials (n + 1) =
        Polynomial.X * (evenCharlierPolynomials n).derivative +
          (Polynomial.C a - Polynomial.X) * evenCharlierPolynomials n) ∧
    (∀ (j : ℕ) (q : ℝ),
      iteratedDeriv (2 * j)
          (fun t : ℝ =>
            Real.exp (-2 * a * t - q * Real.exp (-2 * t)) +
              Real.exp (2 * a * t - q * Real.exp (2 * t))) 0 =
        2 * (4 : ℝ) ^ j * Real.exp (-q) *
          (evenCharlierPolynomials (2 * j)).eval q)

private def basePolynomial (r : ℕ) : Polynomial ℝ :=
  (1 + Polynomial.X) ^ r * (1 + 2 * Polynomial.X) *
    (1 + 3 * Polynomial.X + Polynomial.X ^ 2) ^ 2

/-- The real-rooted base polynomial, its root multiplicities, and the stated
coefficient consequences. -/
def realRootedBasePolynomial : Prop :=
  ∀ r : ℕ,
    let A : Polynomial ℝ := basePolynomial r
    A ≠ 0 ∧
      A.roots =
        Multiset.replicate r (-1 : ℝ) +
          ({(-1 / 2 : ℝ)} : Multiset ℝ) +
          Multiset.replicate 2 ((-3 + Real.sqrt 5) / 2) +
          Multiset.replicate 2 ((-3 - Real.sqrt 5) / 2) ∧
      (∀ z ∈ A.roots, z < 0) ∧
      (∀ n : ℕ, 0 ≤ A.coeff n) ∧
      (∀ n : ℕ, 0 < n →
        A.coeff n ^ 2 ≥ A.coeff (n - 1) * A.coeff (n + 1)) ∧
      (∀ i j k : ℕ, i < j → j < k →
        A.coeff i ≠ 0 → A.coeff k ≠ 0 → A.coeff j ≠ 0)

/-- The positive-sequence B/H/rho recurrence. -/
def positiveSequenceHRecurrence : Prop :=
  ∀ t : ℕ → ℝ, (∀ k : ℕ, 0 < t k) →
    let B : ℕ → ℕ → ℝ := fun r c =>
      (∑ ell ∈ Finset.range (c + 1),
        ((r : ℝ) + (c : ℝ) + 1 - 2 * (ell : ℝ)) *
          t ell * t (r + c + 1 - ell))
    let H : ℕ → ℕ → ℝ := fun r c =>
      B r c / (t c * t (r + 1))
    let rho : ℕ → ℝ := fun k => t (k + 1) / t k
    (∀ r : ℕ, H r 0 = (r : ℝ) + 1) ∧
      (∀ r c : ℕ, 1 ≤ c →
        H r c = (r : ℝ) - (c : ℝ) + 1 +
          (rho (r + 1) / rho (c - 1)) * H (r + 1) (c - 1))

end MathlibPlus.Open
