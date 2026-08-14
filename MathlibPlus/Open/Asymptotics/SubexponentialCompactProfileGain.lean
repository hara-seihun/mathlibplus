import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Asymptotics

/--
For an admissible cutoff-dependent real polynomial family, the compact profile
has subexponential logarithmic growth on every fixed interval `[-U, U]` with
`U ≥ 1`.
-/
def subexponentialCompactProfileGain
    (P : ℕ → Polynomial ℝ) (d : ℕ → ℕ) (B : ℕ → ℝ)
    (a : ℕ → ℕ → ℝ) (k : ℕ) (U : ℝ) : Prop :=
  1 ≤ k ∧
  1 ≤ U ∧
  (∀ L, 1 ≤ B L) ∧
  (∀ L, P L =
    (1 : Polynomial ℝ) +
      (Finset.Icc 1 (d L)).sum (fun j =>
        Polynomial.C (a L j) * Polynomial.X ^ j)) ∧
  (∀ L j, j ∈ Finset.Icc 1 (d L) → |a L j| ≤ (B L) ^ j) ∧
  Filter.Tendsto (fun L : ℕ => (B L) ^ k * (d L : ℝ) / (L : ℝ))
    Filter.atTop (nhds 0) ∧
  Asymptotics.IsLittleO Filter.atTop
    (fun L : ℕ => (d L : ℝ) * Real.log (B L))
    (fun L : ℕ => (L : ℝ)) →
  let S := fun L : ℕ =>
    sSup {x : ℝ | ∃ u : ℝ, |u| ≤ U ∧ x = |Polynomial.eval u (P L)|}
  (∀ L, S L ≤ ((d L : ℝ) + 1) * (B L * U) ^ d L) ∧
  (∀ L, max (Real.log (S L)) 0 ≤
    Real.log ((d L : ℝ) + 1) + (d L : ℝ) * Real.log (B L) +
      (d L : ℝ) * Real.log U) ∧
  Asymptotics.IsLittleO Filter.atTop
    (fun L : ℕ =>
      Real.log ((d L : ℝ) + 1) + (d L : ℝ) * Real.log (B L) +
        (d L : ℝ) * Real.log U)
    (fun L : ℕ => (L : ℝ))

end MathlibPlus.Open.Asymptotics
