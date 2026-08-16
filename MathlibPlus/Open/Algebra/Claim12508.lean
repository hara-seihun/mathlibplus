import Mathlib

namespace MathlibPlus.Open.Algebra.Claim12508

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

def allRectangularMinorsNonnegative : Prop :=
  ∀ N r k : ℕ, 4 ≤ N → 1 ≤ r → 1 ≤ k →
    0 ≤ rectangularMinor N r k

end MathlibPlus.Open.Algebra.Claim12508
