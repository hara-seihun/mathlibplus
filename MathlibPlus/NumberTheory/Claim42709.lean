import Mathlib

namespace MathlibPlus.NumberTheory.Claim42709

open scoped BigOperators ArithmeticFunction.Moebius

/-- The Mertens sum used in the Farey Fourier calculation. -/
def mertens (N : ℕ) : ℤ :=
  ∑ r ∈ Finset.Icc 1 N, (μ r : ℤ)

/-- The divisor-transform form of the `k`th Farey Fourier coefficient. -/
def fourierCoefficient (N k : ℕ) : ℤ :=
  ∑ d ∈ k.divisors.filter (fun d => d ≤ N),
    (d : ℤ) * mertens (N / d)

/-- Claim 42709: the first Fourier coefficient is the Mertens function. -/
theorem firstFourierMode_eq_mertens (N : ℕ) (hN : 1 ≤ N) :
    fourierCoefficient N 1 = mertens N := by
  simp [fourierCoefficient, Finset.filter_singleton, hN]

