import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.O0035Claim10470

noncomputable section
open scoped BigOperators

/-- The positive-real-branch local weight `χ(p)p^(-s)`. -/
def finitePrimeWeight_10470 (N : ℕ) (χ : DirichletCharacter ℂ N)
    (s : ℂ) (p : ℕ) : ℂ :=
  χ (p : ZMod N) * Complex.exp (-s * (Real.log (p : ℝ) : ℂ))

/-- The finite diagonal carrier over the exact prime subtype. -/
def finitePrimeMatrix_10470 (S : Finset ℕ) (N : ℕ)
    (χ : DirichletCharacter ℂ N) (s : ℂ) :
    Matrix {p : ℕ // p ∈ S} {p : ℕ // p ∈ S} ℂ :=
  Matrix.diagonal (fun p => finitePrimeWeight_10470 N χ s p.1)

/-- The auxiliary formal-power-series diagonal carrier. -/
def finitePrimeFormalMatrix_10470 (S : Finset ℕ) (N : ℕ)
    (χ : DirichletCharacter ℂ N) (s : ℂ) (u : PowerSeries ℂ) :
    Matrix {p : ℕ // p ∈ S} {p : ℕ // p ∈ S} (PowerSeries ℂ) :=
  Matrix.diagonal (fun p =>
    PowerSeries.C (finitePrimeWeight_10470 N χ s p.1) * u)

/-- Its formal inverse determinant, whose constant coefficient is one. -/
def finitePrimeFormalEulerCarrier_10470 (S : Finset ℕ) (N : ℕ)
    (χ : DirichletCharacter ℂ N) (s : ℂ) : PowerSeries ℂ :=
  (Matrix.det
    (1 - finitePrimeFormalMatrix_10470 S N χ s PowerSeries.X))⁻¹

/-- Claim 10470: the finite diagonal carrier has the determinant, formal
logarithmic determinant, power-trace, and coefficientwise s-derivative
identities of the finite twisted Euler product.  The explicit auxiliary
variable is the formal power-series variable `u`; consequently no ordinary
complex-log branch or convergence hypothesis is selected. -/
def exactFinitePrimeLocalCarrierPowerSeries_claim10470_batch : Prop :=
  ∀ (S : Finset ℕ) (N : ℕ) (χ : DirichletCharacter ℂ N),
    (∀ p ∈ S, p.Prime) →
      (∀ s : ℂ,
        (Matrix.det (1 - finitePrimeMatrix_10470 S N χ s))⁻¹ =
          ∏ p ∈ S,
            (1 - finitePrimeWeight_10470 N χ s p)⁻¹) ∧
      (∀ s : ℂ, ∀ m : ℕ, 0 < m →
        Matrix.trace ((finitePrimeMatrix_10470 S N χ s) ^ m) =
          ∑ p ∈ S, (finitePrimeWeight_10470 N χ s p) ^ m) ∧
      (∀ s : ℂ,
        PowerSeries.constantCoeff
            (finitePrimeFormalEulerCarrier_10470 S N χ s) = 1) ∧
      (∀ s : ℂ,
        PowerSeries.logOf (finitePrimeFormalEulerCarrier_10470 S N χ s) =
          ∑ p ∈ S,
            PowerSeries.logOf
              ((1 - PowerSeries.C (finitePrimeWeight_10470 N χ s p) *
                  PowerSeries.X)⁻¹)) ∧
      (∀ s : ℂ, ∀ m : ℕ, 0 < m →
        PowerSeries.coeff m
            (PowerSeries.logOf
              (finitePrimeFormalEulerCarrier_10470 S N χ s)) =
          (∑ p ∈ S, (finitePrimeWeight_10470 N χ s p) ^ m) / (m : ℂ)) ∧
      (∀ s : ℂ, ∀ m : ℕ, 0 < m →
        HasDerivAt
          (fun z : ℂ =>
            PowerSeries.coeff m
              (PowerSeries.logOf
                (finitePrimeFormalEulerCarrier_10470 S N χ z)))
          (-∑ p ∈ S,
            (Real.log (p : ℝ) : ℂ) *
              (finitePrimeWeight_10470 N χ s p) ^ m) s) ∧
      (∀ s : ℂ, ∀ m : ℕ, 0 < m →
        HasDerivAt
          (fun z : ℂ => -PowerSeries.coeff m
              (PowerSeries.logOf
                (finitePrimeFormalEulerCarrier_10470 S N χ z)))
          (∑ p ∈ S,
            (Real.log (p : ℝ) : ℂ) *
              (finitePrimeWeight_10470 N χ s p) ^ m) s)

end
end MathlibPlus.Open.ResearchFormalization.O0035Claim10470
