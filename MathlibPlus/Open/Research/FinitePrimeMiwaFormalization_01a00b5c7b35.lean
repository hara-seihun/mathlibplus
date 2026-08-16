import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Research.FinitePrimeMiwa

noncomputable section

/-- The twisted prime-power coefficient used by the finite Miwa series. -/
def primePowerWeight (χ : ℕ → ℂ) (s : ℂ) (p : ℕ) : ℂ :=
  χ p * Complex.cpow (p : ℂ) (-s)

/-- The finite prime trace series, with the coefficient of `z^k` equal to `t_k`. -/
def finitePrimeTraceSeries (P : Finset ℕ) (χ : ℕ → ℂ) (s : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun k =>
    if 0 < k then
      (1 / (k : ℂ)) * ∑ p ∈ P, (primePowerWeight χ s p) ^ k
    else 0)

/-- The formal geometric series representing `(1 - a z)⁻¹`. -/
def inverseLinearPrimeFactor (a : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun k => a ^ k)

/-- Formal exponential of a series with its coefficients written explicitly. -/
noncomputable def formalExpSeries (F : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun n =>
    ∑' m : ℕ, (PowerSeries.coeff n (F ^ m)) / (m.factorial : ℂ))

/-- Formal logarithm of a unit, written as the logarithm series in `U - 1`. -/
noncomputable def formalLogUnitSeries (U : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun n =>
    ∑' m : ℕ,
      if 0 < m then
        ((-1 : ℂ) ^ (m + 1)) *
            (PowerSeries.coeff n ((U - 1) ^ m)) / (m : ℂ)
      else 0)

/-- The finite Euler product in the formal power-series carrier. -/
def finiteEulerProductSeries (P : Finset ℕ) (χ : ℕ → ℂ) (s : ℂ) : PowerSeries ℂ :=
  ∏ p ∈ P, inverseLinearPrimeFactor (primePowerWeight χ s p)

/-- Finite arithmetic Miwa identity, including the assertion that the logarithm
contains only the twisted single-prime powers and no mixed-prime primitive. -/
def finiteArithmeticMiwaIdentity : Prop :=
  ∀ (P : Finset ℕ),
    (∀ p ∈ P, Nat.Prime p) →
    ∀ (χ : ℕ → ℂ) (s : ℂ),
      formalExpSeries (finitePrimeTraceSeries P χ s) =
          finiteEulerProductSeries P χ s ∧
        formalLogUnitSeries (finiteEulerProductSeries P χ s) =
          finitePrimeTraceSeries P χ s

end
end MathlibPlus.Open.Research.FinitePrimeMiwa
