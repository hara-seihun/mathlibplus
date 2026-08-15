import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

noncomputable section

open scoped BigOperators

/-- A finite Jacobi matrix with diagonal `alpha` and off-diagonal `beta`. -/
def jacobiMatrix (n : ℕ) (alpha beta : ℕ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    if i = j then alpha i.1
    else if i.1 + 1 = j.1 then beta j.1
    else if j.1 + 1 = i.1 then beta i.1
    else 0

/-- The real positive-definiteness predicate used for `J ≻ 0`. -/
def positiveDefiniteMatrix {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ v : Fin n → ℝ, v ≠ 0 →
    0 < Finset.sum Finset.univ (fun i =>
      Finset.sum Finset.univ (fun j => v i * J i j * v j))

/-- The Jacobi and positivity hypotheses supplied by the admitted context. -/
def positiveJacobi {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ)
    (alpha beta : ℕ → ℝ) : Prop :=
  J = jacobiMatrix n alpha beta ∧
    positiveDefiniteMatrix J ∧
      ∀ k : ℕ, 0 < k → k < n → 0 < beta k

/-- The leading principal determinant `D_k`. -/
def leadingPrincipalDet {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ)
    (k : ℕ) : ℝ :=
  if hk : k ≤ n then
    Matrix.det (fun i j : Fin k =>
      J ⟨i.1, lt_of_lt_of_le i.isLt hk⟩
        ⟨j.1, lt_of_lt_of_le j.isLt hk⟩)
  else 0

/-- The resistance-gauge normalized solution from the admitted context. -/
def resistanceGaugeY {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ)
    (beta : ℕ → ℝ) (a k : ℕ) : ℝ :=
  leadingPrincipalDet J k /
    (leadingPrincipalDet J (a - 1) *
      Finset.prod (Finset.Icc a k) (fun ell => beta ell))

/-- The source coordinate in the admitted statement. -/
def sourceCoordinate (alpha beta : ℕ → ℝ) (k : ℕ) : ℝ :=
  alpha k - beta k - beta (k + 1)

/-- The flux coordinate in the admitted statement. -/
def fluxCoordinate (beta Y : ℕ → ℝ) (k : ℕ) : ℝ :=
  beta (k + 1) * (Y (k + 1) - Y k)

/-- The resistance coordinate in the admitted statement. -/
def resistanceCoordinate (beta : ℕ → ℝ) (a k : ℕ) : ℝ :=
  if k = a - 1 then 0
  else Finset.sum (Finset.Icc a k) (fun p => (beta p)⁻¹)

/-- Source, flux, and resistance coordinates with the exact Jacobi context and
index ranges supplied by the admitted same-locator claims. -/
def sourceFluxResistanceCoordinate : Prop :=
  ∀ (n a b : ℕ) (J : Matrix (Fin n) (Fin n) ℝ)
    (alpha beta : ℕ → ℝ),
    1 ≤ a → a ≤ b → b ≤ n - 2 →
    positiveJacobi J alpha beta →
    ∃ (S G T : ℕ → ℝ),
      (∀ k : ℕ, a ≤ k → k ≤ b →
        S k = alpha k - beta k - beta (k + 1)) ∧
      (∀ k : ℕ, a - 1 ≤ k → k ≤ b →
        G k = beta (k + 1) *
          (resistanceGaugeY J beta a (k + 1) - resistanceGaugeY J beta a k)) ∧
      T (a - 1) = 0 ∧
      (∀ k : ℕ, a ≤ k → k ≤ b →
        T k = Finset.sum (Finset.Icc a k) (fun p => (beta p)⁻¹))

end

end MathlibPlus.Open.ResearchFormalization
