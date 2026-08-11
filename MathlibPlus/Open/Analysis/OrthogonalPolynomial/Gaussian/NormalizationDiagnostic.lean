import Mathlib

/-!
# Gaussian normalization and index-shift diagnostic

This registry node records admitted claim 474.  The phrase “MRS radius” is made
explicit using the standard MRS integral for the base exponent `V`; the diagnostic
conclusion about conventions is represented by the exact same-index ratio, without
inventing a separate formal notion of “index-shift error”.
-/

namespace MathlibPlus.Open.Analysis.OrthogonalPolynomial.Gaussian

/-- For the base weight `W(x) = exp (-x²)`, its squared orthogonality density is
`exp (-2x²)`, the MRS radius is `sqrt n`, and the corresponding orthonormal Hermite
recurrence coefficient is `sqrt n / 2`, so their same-index ratio is exactly `1/2`. -/
noncomputable def normalizationDiagnostic : Prop :=
  let V : ℝ → ℝ := fun x => x ^ 2
  let W : ℝ → ℝ := fun x => Real.exp (-V x)
  let density : ℝ → ℝ := fun x => Real.exp (-2 * x ^ 2)
  let R : ℕ → ℝ := fun n => Real.sqrt n
  let b : ℕ → ℝ := fun n => Real.sqrt n / 2
  (∀ x : ℝ, W x ^ 2 = density x) ∧
    (∀ n : ℕ, 0 < n →
      (n : ℝ) = (2 / Real.pi) *
        ∫ t in (0 : ℝ)..1,
          (R n * t * deriv V (R n * t)) / Real.sqrt (1 - t ^ 2)) ∧
    (∃ p : ℕ → Polynomial ℝ,
      (∀ n : ℕ, p n ≠ 0 ∧ (p n).natDegree = n) ∧
      (∀ n m : ℕ,
        ∫ x : ℝ, (p n).eval x * (p m).eval x * density x =
          if n = m then 1 else 0) ∧
      (∀ n : ℕ, ∀ x : ℝ,
        x * (p n).eval x =
          b (n + 1) * (p (n + 1)).eval x +
            if n = 0 then 0 else b n * (p (n - 1)).eval x)) ∧
    (∀ n : ℕ, 0 < n → b n / R n = (1 / 2 : ℝ))

end MathlibPlus.Open.Analysis.OrthogonalPolynomial.Gaussian
