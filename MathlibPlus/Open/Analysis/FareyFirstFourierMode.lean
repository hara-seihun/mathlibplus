import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

noncomputable def mertens (N : ℕ) : ℤ :=
  ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.moebius n

noncomputable def fareyLayerFourierCoeff (q k : ℕ) : ℂ :=
  ∑ a ∈ (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q),
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((a * k : ℕ) : ℂ) / (q : ℂ))

noncomputable def fareyDivisorTransform (N k : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 N, fareyLayerFourierCoeff q k

noncomputable def fareyH (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
    ((mertens (N / d) : ℤ) : ℝ) * ((mertens (N / e) : ℤ) : ℝ) *
      (((Nat.gcd d e : ℕ) : ℝ) ^ 2) / ((d : ℝ) * (e : ℝ))

noncomputable def zetaTwo : ℝ :=
  ∑' n : ℕ, (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹

def firstFourierModeLowerBound : Prop :=
  ∀ N : ℕ,
    fareyDivisorTransform N 1 = (mertens N : ℂ) ∧
      fareyH N ≥ zetaTwo⁻¹ * (((mertens N : ℤ) : ℝ) ^ 2)

end MathlibPlus.Open.Analysis
