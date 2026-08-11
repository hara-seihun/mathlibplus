import Mathlib

/-!
# Open total-even Loewner certificates

Statement-faithful registry nodes for finite certificates built from the completed logarithmic
derivative.  The finite-cutoff interval computation is proof provenance, not an additional
mathematical hypothesis.
-/

namespace MathlibPlus.Open.Analysis.TotalEvenLoewner

open ArithmeticFunction
open scoped ArithmeticFunction

/-- The exact total even Loewner matrix at rates `(3,5)` is strictly positive definite.
The logarithmic derivative is expanded with the von Mangoldt Dirichlet series, so the node binds
the matrix to the completed prime-side function rather than leaving it as an arbitrary parameter. -/
noncomputable def twoRatePositiveDefinite : Prop :=
  let ell : ℝ → ℝ := fun x =>
    1 / (x + 1 / 2) + 1 / (x - 1 / 2) - 1 / 2 * Real.log Real.pi +
      1 / 2 * (Complex.digamma (((1 / 4 + x / 2 : ℝ) : ℂ))).re -
      ∑' n : ℕ, vonMangoldt n / ((n : ℝ) ^ (x + 1 / 2 : ℝ))
  let rates : Fin 2 → ℝ := ![3, 5]
  let Q : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
    if i = j then
      2 * (ell (rates i) / rates i - deriv ell (rates i))
    else
      4 * (rates j * ell (rates i) - rates i * ell (rates j)) /
        (rates j ^ 2 - rates i ^ 2)
  Q.PosDef

end MathlibPlus.Open.Analysis.TotalEvenLoewner
