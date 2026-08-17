import MathlibPlus.Open.Analysis.BaezDuarte

namespace MathlibPlus.Open.Analysis.BaezDuarteErrorGeneratingFunction11867

noncomputable section

open MeasureTheory

/-- The real coefficient `E_k(x)=-h_k(x)-1`. -/
def errorCoefficient (x : ℝ) (k : ℕ+) : ℝ :=
  -baezDuarteHk k x - 1

/-- The divisor-polynomial generating function `L_x`. -/
def divisorGeneratingFunction (x : ℝ) (z : ℂ) : ℂ :=
  ∑' j : ℕ+,
    (baezDuarteR (j : ℕ) x : ℂ) * z ^ (j : ℕ)

/-- The complex error generating function `𝓔_x`. -/
def errorGeneratingFunction (x : ℝ) (z : ℂ) : ℂ :=
  ∑' k : ℕ+,
    (errorCoefficient x k : ℂ) * z ^ (k : ℕ)

/-- The common unit-disk convergence domain for the three series occurring
in the error identity. -/
def commonConvergenceDomain (u : ℝ) (z : ℂ) : Prop :=
  0 < u ∧
    ‖z‖ < 1 ∧
    Summable (fun k : ℕ+ =>
      (errorCoefficient (Real.exp (-u)) k : ℂ) * z ^ (k : ℕ)) ∧
    Summable (fun j : ℕ+ =>
      (baezDuarteR (j : ℕ) (Real.exp (-u)) : ℂ) * z ^ (j : ℕ)) ∧
    Summable (fun n : ℕ+ =>
      (ArithmeticFunction.moebius (n : ℕ) : ℝ) /
          (n : ℝ) * (Real.exp (-u)) ^ (n : ℕ))

/-- The exact error coefficient identification and generating-function
identity, on the common complex convergence domain. -/
def exactErrorGeneratingFunction : Prop :=
  ∀ (u : ℝ) (z : ℂ),
    commonConvergenceDomain u z →
      (∀ k : ℕ+,
        baezDuartePoint u (k : ℝ) - 1 = errorCoefficient (Real.exp (-u)) k ∧
          errorCoefficient (Real.exp (-u)) k =
            -baezDuarteHk k (Real.exp (-u)) - 1) ∧
      errorGeneratingFunction (Real.exp (-u)) z =
        divisorGeneratingFunction (Real.exp (-u)) z / (1 - z) -
          (baezDuarteG (Real.exp (-u)) : ℂ) * z / (1 - z) ^ 2 -
            z / (1 - z)

end

end MathlibPlus.Open.Analysis.BaezDuarteErrorGeneratingFunction11867
