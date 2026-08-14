import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.ResearchBatch.Arithmetic

def complexDivisorSigma (z : ℂ) (n : ℕ) : ℂ :=
  ∑ d ∈ n.divisors, Complex.cpow (d : ℂ) z

def signed_gcd_coefficient_cancellation : Prop :=
  ∀ (R : ℕ) (w : ℂ), 0 < R →
    (∑ h ∈ R.divisors,
        (ArithmeticFunction.moebius h : ℂ) * Complex.cpow (h : ℂ) (-w) *
          complexDivisorSigma (-1 - w) (R / h)) =
      ∏ p ∈ (R.divisors.filter Nat.Prime),
        (1 + Complex.cpow (p : ℂ) (-1 - w) -
          Complex.cpow (p : ℂ) (-w)) ∧
    (∑ h ∈ R.divisors,
        (ArithmeticFunction.moebius h : ℂ) * complexDivisorSigma (-1) (R / h)) =
      (1 / (R : ℂ))

def dirichletTerm (z : ℕ → ℂ) (s : ℂ) (n : ℕ) : ℂ :=
  if 0 < n then z n * Complex.cpow (n : ℂ) (-s) else 0

def dyadicDirichletCoefficient (z : ℕ → ℂ) (m : ℕ) : ℂ :=
  if 2 ∣ m then z (m / 2) else 0

def dyadic_multiplication_decimates_dirichlet_coefficients : Prop :=
  ∀ (z : ℕ → ℂ) (s : ℂ),
    Summable (fun n => dirichletTerm z s n) →
      (∀ m, 0 < m →
        dyadicDirichletCoefficient z m =
          if 2 ∣ m then z (m / 2) else 0) ∧
      Summable (fun m => dirichletTerm (dyadicDirichletCoefficient z) s m) ∧
      (∑' m, dirichletTerm (dyadicDirichletCoefficient z) s m) =
        Complex.cpow (2 : ℂ) (-s) * (∑' n, dirichletTerm z s n)

end MathlibPlus.Open.ResearchBatch.Arithmetic
