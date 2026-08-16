import Mathlib

namespace MathlibPlus.Open.NewResearch2.O0108

def nr2_claim_11016 : Prop :=
  ∀ p : ℝ, 1 < p →
    let lam : ℂ := (1 : ℂ) + 2 * Complex.I
    let U : Matrix (Fin 4) (Fin 4) ℂ :=
      Matrix.diagonal ![
        Complex.cpow (p : ℂ) lam,
        Complex.cpow (p : ℂ) (-star lam),
        Complex.cpow (p : ℂ) (star lam),
        Complex.cpow (p : ℂ) (-lam)]
    Matrix.charpoly U =
        (Polynomial.X - Polynomial.C (Complex.cpow (p : ℂ) lam)) *
        (Polynomial.X - Polynomial.C (Complex.cpow (p : ℂ) (-star lam))) *
        (Polynomial.X - Polynomial.C (Complex.cpow (p : ℂ) (star lam))) *
        (Polynomial.X - Polynomial.C (Complex.cpow (p : ℂ) (-lam))) ∧
      (‖Complex.cpow (p : ℂ) lam‖ = p ∧
        ‖Complex.cpow (p : ℂ) (-star lam)‖ = p⁻¹ ∧
        ‖Complex.cpow (p : ℂ) (star lam)‖ = p ∧
        ‖Complex.cpow (p : ℂ) (-lam)‖ = p⁻¹)

def nr2_claim_11017 : Prop :=
  ∀ p : ℝ, 1 < p →
    let lam : ℂ := (1 : ℂ) + 2 * Complex.I
    let U : Matrix (Fin 4) (Fin 4) ℂ :=
      Matrix.diagonal ![
        Complex.cpow (p : ℂ) lam,
        Complex.cpow (p : ℂ) (-star lam),
        Complex.cpow (p : ℂ) (star lam),
        Complex.cpow (p : ℂ) (-lam)]
    let B : Matrix (Fin 4) (Fin 4) ℂ :=
      !![ (0 : ℂ), 1, 0, 0;
          1, 0, 0, 0;
          0, 0, 0, 1;
          0, 0, 1, 0 ]
    Matrix.conjTranspose U * B * U = B ∧
      Matrix.IsHermitian B ∧
      ∃ Q : Matrix (Fin 4) (Fin 4) ℂ,
        IsUnit Q.det ∧
        Matrix.conjTranspose Q * B * Q =
          Matrix.diagonal ![(1 : ℂ), 1, -1, -1]

end MathlibPlus.Open.NewResearch2.O0108
