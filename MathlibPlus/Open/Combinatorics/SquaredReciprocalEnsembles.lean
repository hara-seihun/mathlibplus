import Mathlib

namespace MathlibPlus.Open.Combinatorics

/-- Claim 8916: positive ordered reciprocal-root sites, their squared support,
    and positive attached weights. -/
def squaredReciprocalRootSupport
    (n : ℕ) (z x ω : ℕ → ℕ+ → ℝ) : Prop :=
  (∀ i : ℕ+, 0 < z n i) ∧
    (∀ i j : ℕ+, i < j → z n j < z n i) ∧
    (∀ i : ℕ+, x n i = (z n i) ^ 2) ∧
    (∀ i : ℕ+, 0 < ω n i)

/-- Claim 8917: the squared-Vandermonde weights and their normalized law on
    n-element finite subsets of the positive-index support. -/
def squaredVandermondeOrthogonalPolynomialEnsemble
    (n : ℕ) (z x ω : ℕ → ℕ+ → ℝ)
    (P : Finset ℕ+ → ℝ) : Prop :=
  squaredReciprocalRootSupport n z x ω ∧
    (let W : Finset ℕ+ → ℝ := fun S =>
      (∏ i ∈ S, ω n i) *
        (∏ i ∈ S, ∏ j ∈ S,
          if i < j then ((z n i) ^ 2 - (z n j) ^ 2) ^ 2 else 1)
     let Z : ℝ := ∑' S : Finset ℕ+, if S.card = n then W S else 0
     0 < Z ∧
       (∀ S : Finset ℕ+, 0 ≤ P S) ∧
       (∑' S : Finset ℕ+, P S = 1) ∧
       (∀ S : Finset ℕ+, S.card ≠ n → P S = 0) ∧
       (∀ S : Finset ℕ+, S.card = n → P S = W S / Z))

/-- Claim 8918: the discrete Heine representation for the monic degree-n
    polynomial orthogonal for the squared-support discrete measure. -/
def discreteHeineFormula
    (n : ℕ) (z x ω : ℕ → ℕ+ → ℝ)
    (p : Polynomial ℝ) (P : Finset ℕ+ → ℝ) : Prop :=
  squaredVandermondeOrthogonalPolynomialEnsemble n z x ω P →
    (p.Monic ∧
      p.degree = (n : WithBot ℕ) ∧
      (∀ q : Polynomial ℝ, q.degree < (n : WithBot ℕ) →
        (∑' i : ℕ+, ω n i * p.eval ((z n i) ^ 2) * q.eval ((z n i) ^ 2)) = 0) →
      ∀ t : ℝ,
        p.eval t =
          ∑' S : Finset ℕ+, P S *
            (∏ i ∈ S, (t - (z n i) ^ 2)))

/-- Claim 8919: positivity on the negative real axis, including the
    expectation identity for the same ensemble law. -/
def positivityOnNegativeAxis
    (n : ℕ) (z x ω : ℕ → ℕ+ → ℝ)
    (p : Polynomial ℝ) (P : Finset ℕ+ → ℝ) : Prop :=
  squaredVandermondeOrthogonalPolynomialEnsemble n z x ω P →
    (p.Monic ∧
      p.degree = (n : WithBot ℕ) ∧
      (∀ q : Polynomial ℝ, q.degree < (n : WithBot ℕ) →
        (∑' i : ℕ+, ω n i * p.eval ((z n i) ^ 2) * q.eval ((z n i) ^ 2)) = 0) →
      ∀ s : ℝ, 0 < s →
        (((-1 : ℝ) ^ n) * p.eval (-s) =
            ∑' S : Finset ℕ+, P S *
              (∏ i ∈ S, (s + (z n i) ^ 2))) ∧
          (0 < ∑' S : Finset ℕ+, P S *
              (∏ i ∈ S, (s + (z n i) ^ 2))))

end MathlibPlus.Open.Combinatorics
