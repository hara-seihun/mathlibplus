import Mathlib

namespace MathlibPlus.Open.Algebra.Claim12509

noncomputable def shellPolynomial (N : ℕ) : Polynomial ℝ :=
  ((1 : Polynomial ℝ) + Polynomial.X) *
    ((1 : Polynomial ℝ) +
      Polynomial.C (2 * Real.cos (2 * Real.pi / (N : ℝ))) * Polynomial.X +
      Polynomial.X ^ 2)

noncomputable def coefficient (N : ℕ) (q : ℤ) : ℝ :=
  if h : 0 ≤ q then (shellPolynomial N).coeff q.toNat else 0

noncomputable def rectangularMinor (N r k : ℕ) : ℝ :=
  Matrix.det (fun i j : Fin r =>
    coefficient N ((k : ℤ) + (j.val : ℤ) - (i.val : ℤ)))

noncomputable def shiftValue (N r : ℕ) : ℝ :=
  (Real.sin (((r + 1 : ℕ) : ℝ) * Real.pi / (N : ℝ)) *
    Real.sin (((r + 2 : ℕ) : ℝ) * Real.pi / (N : ℝ))) /
    (Real.sin (Real.pi / (N : ℝ)) * Real.sin (2 * Real.pi / (N : ℝ)))

def rectangularShiftFormula : Prop :=
  ∀ N r : ℕ, 4 ≤ N → 1 ≤ r →
    rectangularMinor N r 1 = shiftValue N r ∧
    rectangularMinor N r 2 = shiftValue N r ∧
    rectangularMinor N r 3 = 1 ∧
    ∀ k : ℕ, 3 < k → rectangularMinor N r k = 0

end MathlibPlus.Open.Algebra.Claim12509
