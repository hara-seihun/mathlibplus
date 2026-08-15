import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.Analysis.FormalizationBatch

/-- A Toeplitz minor of the zero-extended integer-indexed coefficient sequence. -/
def toeplitzMinor (f : ℤ → ℝ) (s : ℕ)
    (rows cols : Fin s → ℤ) : Matrix (Fin s) (Fin s) ℝ :=
  fun i j => f (cols j - rows i)

/-- The finite-order Pólya-frequency condition used by Claims 8179 and 8183. -/
def PF (r : ℕ) (f : ℤ → ℝ) : Prop :=
  (∀ n : ℤ, n < 0 → f n = 0) ∧
    ∀ s : ℕ, 1 ≤ s → s ≤ r →
      ∀ rows cols : Fin s → ℤ,
        StrictMono rows → StrictMono cols →
          0 ≤ Matrix.det (toeplitzMinor f s rows cols)

/-- Positivity of all nonnegative coefficients. -/
def PositiveCoefficients (f : ℤ → ℝ) : Prop :=
  ∀ n : ℕ, 0 < f (n : ℤ)

/-- An entire function represented by the specified real coefficient series. -/
def EntireWithCoefficients (f : ℤ → ℝ) (F : ℂ → ℂ) : Prop :=
  (∀ z : ℂ,
      HasSum (fun n : ℕ => (f (n : ℤ) : ℂ) * z ^ n) (F z)) ∧
    Differentiable ℂ F

/-- Nonpolynomiality of the entire function in the admitted claims. -/
def NonPolynomial (F : ℂ → ℂ) : Prop :=
  ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, F z = p.eval z

/-- The complete positivity, entireness, and PF package for the coefficient sequence. -/
def PositiveNonPolynomialEntirePF (r : ℕ) (f : ℤ → ℝ) (F : ℂ → ℂ) : Prop :=
  PositiveCoefficients f ∧ EntireWithCoefficients f F ∧
    NonPolynomial F ∧ PF r f

/-- Claim 8179: a positive nonpolynomial entire PF₃ series is strictly PF₂. -/
def claim8179_strict_pf2 : Prop :=
  ∀ (f : ℤ → ℝ) (F : ℂ → ℂ),
    PositiveNonPolynomialEntirePF 3 f F →
      ∀ n : ℕ, 1 ≤ n →
        f (n : ℤ) / f ((n - 1 : ℕ) : ℤ) ≠
            f ((n + 1 : ℕ) : ℤ) / f (n : ℤ) ∧
          f (n : ℤ) ^ 2 >
            f ((n - 1 : ℕ) : ℤ) * f ((n + 1 : ℕ) : ℤ)

/-- The row index retained after deleting row m from rows 0 through r. -/
def deletedRowIndex (r m : ℕ) (i : Fin r) : ℕ :=
  if i.1 < m then i.1 else i.1 + 1

/-- A restricted source column on the deleted-row set I_m. -/
def restrictedSourceColumn (f : ℤ → ℝ) (r m s : ℕ) : Fin r → ℝ :=
  fun i => f ((s : ℤ) - (deletedRowIndex r m i : ℤ))

/-- The deleted-row cofactor Δ_m(r,k) from the endpoint Laurent block. -/
def endpointCofactor (d : ℤ → ℝ) (r k m : ℕ) : ℝ :=
  Matrix.det (fun i j : Fin r =>
    d (((k + j.1 : ℕ) : ℤ) - (deletedRowIndex r m i : ℤ)))

/-- The exterior Laurent expansion required to define the endpoint block. -/
def ExteriorLaurentExpansion (F : ℂ → ℂ) (α : ℝ) (d : ℤ → ℝ) : Prop :=
  ∀ z : ℂ, (α : ℝ) < ‖z‖ →
    HasSum (fun n : ℤ => (d n : ℂ) * z ^ n)
      (F z / (z - (α : ℂ)))

/-- Claim 8183: independent initial restricted columns force a strict cofactor. -/
def claim8183_strict_cofactor : Prop :=
  ∀ (r k m : ℕ) (α : ℝ) (f : ℤ → ℝ) (F : ℂ → ℂ) (d : ℤ → ℝ),
    0 < r → m ≤ r → 0 < α →
      PositiveNonPolynomialEntirePF r f F →
      ExteriorLaurentExpansion F α d →
      LinearIndependent ℝ
        (fun j : Fin (r - 1) =>
          restrictedSourceColumn f r m (k + 1 + j.1)) →
        0 < endpointCofactor d r k m

end MathlibPlus.Open.Analysis.FormalizationBatch
