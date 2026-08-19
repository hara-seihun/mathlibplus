import Mathlib

namespace MathlibPlus.Algebra.Claim12303

/--
The two-curve counterexample in Claim 12303.  The common Adams/K₀ matrix is
written explicitly, and the two named affine curves retain their point-count,
trace, and Frobenius-polynomial data.  The final quantified clause is the
curve-blind obstruction: one common matrix cannot have both displayed Weil
characteristic polynomials, without invoking the separate determinant-parity
obstruction.
-/
def sameFieldCurves_frobeniusPolynomial : Prop :=
  let psi5 : Matrix (Fin 2) (Fin 2) ℚ := !![(1 : ℚ), 0; 0, 5]
  let k0 : Matrix (Fin 2) (Fin 2) ℚ := !![(1 : ℚ), 0; 0, 5]
  let E₁ : Finset (ZMod 5 × ZMod 5) :=
    Finset.univ.filter (fun p : ZMod 5 × ZMod 5 =>
      p.2 ^ 2 = p.1 ^ 3 + p.1 + 1)
  let E₂ : Finset (ZMod 5 × ZMod 5) :=
    Finset.univ.filter (fun p : ZMod 5 × ZMod 5 =>
      p.2 ^ 2 = p.1 ^ 3 + 2 * p.1)
  let cardE₁ : ℤ := (E₁.card : ℤ) + 1
  let cardE₂ : ℤ := (E₂.card : ℤ) + 1
  let traceE₁ : ℤ := (5 : ℤ) + 1 - cardE₁
  let traceE₂ : ℤ := (5 : ℤ) + 1 - cardE₂
  let pAdams : Polynomial ℚ :=
    (Polynomial.X - Polynomial.C 1) *
      (Polynomial.X - Polynomial.C 5)
  let pE₁ : Polynomial ℚ :=
    Polynomial.X ^ 2 - Polynomial.C (traceE₁ : ℚ) * Polynomial.X +
      Polynomial.C 5
  let pE₂ : Polynomial ℚ :=
    Polynomial.X ^ 2 - Polynomial.C (traceE₂ : ℚ) * Polynomial.X +
      Polynomial.C 5
  psi5 = k0 ∧
    Matrix.charpoly psi5 = pAdams ∧
    pAdams = Polynomial.X ^ 2 - Polynomial.C 6 * Polynomial.X +
      Polynomial.C 5 ∧
    cardE₁ = 9 ∧
    cardE₂ = 2 ∧
    traceE₁ = -3 ∧
    traceE₂ = 4 ∧
    traceE₁ ≠ traceE₂ ∧
    pE₁ = Polynomial.X ^ 2 + Polynomial.C 3 * Polynomial.X +
      Polynomial.C 5 ∧
    pE₂ = Polynomial.X ^ 2 - Polynomial.C 4 * Polynomial.X +
      Polynomial.C 5 ∧
    pE₁ ≠ pE₂ ∧
    ¬ ∃ F₁ F₂ : Matrix (Fin 2) (Fin 2) ℚ,
      F₁ = psi5 ∧
      F₂ = psi5 ∧
      Matrix.charpoly F₁ = pE₁ ∧
      Matrix.charpoly F₂ = pE₂

end MathlibPlus.Algebra.Claim12303
