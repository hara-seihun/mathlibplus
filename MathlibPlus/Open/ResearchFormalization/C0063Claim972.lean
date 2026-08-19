import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.C0063Claim972

/-- The order-seven derivative determinant of the two-scale degree-eight
family has the displayed polynomial factorization and the stated negative
specialization at `A = 13`. -/
def exactTwoScaleDegreeEightDeterminant_claim972 : Prop :=
  let P : ℝ → ℝ := fun A =>
    66600 * A ^ 14 - 740250 * A ^ 13 - 1212400 * A ^ 12 -
      2220750 * A ^ 11 - 8375850 * A ^ 10 - 10828965 * A ^ 9 -
      24058020 * A ^ 8 - 33329895 * A ^ 7 - 43557710 * A ^ 6 -
      48286665 * A ^ 5 - 28313208 * A ^ 4 - 42946995 * A ^ 3 -
      17417820 * A ^ 2 - 11301360 * A - 2842600
  ∀ A : ℝ,
    let G_A : Polynomial ℝ :=
      (1 + Polynomial.C A * Polynomial.X) ^ 5 *
        (1 + Polynomial.X) ^ 3
    let D₇ : ℝ :=
      Matrix.det (fun i j : Fin 7 =>
        (((Polynomial.derivative^[6 + j - i]) G_A).eval 0))
    D₇ = -3095868211200000 * A ^ 21 * P A ∧
      (A = 13 →
        D₇ = -3448050968558587609041640575830444915111828173042483200000 ∧
          D₇ < 0)

end MathlibPlus.Open.ResearchFormalization.C0063Claim972
