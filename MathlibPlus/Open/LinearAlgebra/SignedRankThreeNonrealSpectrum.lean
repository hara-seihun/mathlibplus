import Mathlib

namespace MathlibPlus.Open.LinearAlgebra

def signedRankThreeNonrealSpectrum : Prop :=
  let B : Matrix (Fin 3) (Fin 3) ℂ := !![
    (49.55905958 : ℂ), (4.74398758 : ℂ), (4.24613702 : ℂ);
    (602.78718028 : ℂ), (58.92247434 : ℂ), (90.61660513 : ℂ);
    (30.77594537 : ℂ), (3.01020645 : ℂ), (4.70377566 : ℂ)]
  let D : Matrix (Fin 3) (Fin 3) ℂ :=
    fun i j => if i = j then if i = 1 then (-1 : ℂ) else 1 else 0
  let S : Matrix (Fin 3) (Fin 3) ℂ := D * B
  let χ : Polynomial ℂ := Matrix.charpoly S
  let δ : ℝ :=
    -(22228276895038725417317370670406276969915998349347549 : ℝ) /
      125000000000000000000000000000000000000000000000000
  let realThreeFactor : Prop :=
    ∃ r₁ r₂ r₃ : ℝ,
      χ =
          (Polynomial.X - Polynomial.C (r₁ : ℂ)) *
            (Polynomial.X - Polynomial.C (r₂ : ℂ)) *
              (Polynomial.X - Polynomial.C (r₃ : ℂ)) ∧
        0 < r₁ ∧ 0 < r₂ ∧ r₃ < 0
  (Polynomial.discr χ = (δ : ℂ) ∧ δ < 0) ∧
    (∃ r : ℝ, ∃ z : ℂ,
      z.im ≠ 0 ∧
        χ =
          (Polynomial.X - Polynomial.C (r : ℂ)) *
            (Polynomial.X - Polynomial.C z) *
              (Polynomial.X - Polynomial.C (star z))) ∧
    ¬ realThreeFactor

end MathlibPlus.Open.LinearAlgebra
