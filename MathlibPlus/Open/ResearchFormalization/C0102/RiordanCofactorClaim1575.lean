import Mathlib
import MathlibPlus.Open.ResearchFormalization.InverseRiordanCofactor

namespace MathlibPlus.Open.ResearchFormalization.C0102

open scoped BigOperators

/-- The leading square of the proper Riordan array with pair
`((1 + x)^e, x * (1 + x))`. -/
noncomputable def properRiordanLeadingSquare (e n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
  fun i j =>
    Polynomial.coeff
      (MathlibPlus.Open.ResearchFormalization.riordanGeneratingPolynomial e j.1)
      i.1

/-- The determinant of the minor obtained by deleting row `0` and column `n`
from the leading `(n+1)`-square. -/
noncomputable def deletedRowZeroColumnNMinor (e n : ℕ) : ℚ :=
  Matrix.det (fun (i j : Fin n) =>
    properRiordanLeadingSquare e n (Fin.succ i)
      (Fin.castLE (Nat.le_succ n) j))

/-- The binomial determinant in Claim 1575, with the usual zero convention for
negative lower binomial indices made explicit by `riordanEntry`. -/
noncomputable def riordanCofactorDeterminant (e n : ℕ) : ℚ :=
  Matrix.det (fun (i j : Fin n) =>
    MathlibPlus.Open.ResearchFormalization.riordanEntry e (i.1 + 1) j.1)

/-- The rising factorial `(e + n + 1)_(n-1)` in the rational normalization of
Claim 1575. -/
noncomputable def riordanRisingFactorial (e n : ℕ) : ℚ :=
  ∏ r ∈ Finset.range (n - 1),
    ((e + n + 1 + r : ℕ) : ℚ)

/-- Claim 1575: the Riordan cofactor determinant and both exact closed forms. -/
def claim1575 : Prop :=
  ∀ e n : ℕ, 1 ≤ e → 1 ≤ n →
    riordanCofactorDeterminant e n =
        (e : ℚ) / (n : ℚ) *
          (Nat.choose (e + 2 * n - 1) (n - 1) : ℚ) ∧
      (e : ℚ) / (n : ℚ) *
          (Nat.choose (e + 2 * n - 1) (n - 1) : ℚ) =
        (e : ℚ) * riordanRisingFactorial e n /
          (Nat.factorial n : ℚ) ∧
      riordanCofactorDeterminant e n =
        deletedRowZeroColumnNMinor e n

end MathlibPlus.Open.ResearchFormalization.C0102
