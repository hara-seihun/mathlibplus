import Mathlib

namespace MathlibPlus.Open.NumberTheory.Claim9759

open scoped BigOperators

noncomputable def fareyLevel {V : Type*} [SeminormedAddCommGroup V]
    [InnerProductSpace ℝ V] (e : ℕ → V) (n : ℕ) : V :=
  ∑ d ∈ n.divisors,
    (((ArithmeticFunction.moebius (n / d) : ℤ) : ℝ) • e d)

noncomputable def fareyWhitened {V : Type*} [SeminormedAddCommGroup V]
    [InnerProductSpace ℝ V] (e : ℕ → V) (q : ℕ) : V :=
  ∑ d ∈ q.divisors,
    (((d : ℝ) / (q : ℝ)) *
      ((ArithmeticFunction.moebius (q / d) : ℤ) : ℝ)) • e d

noncomputable def fareyConvolutionCoeff (n : ℕ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ d ∈ n.divisors,
    (d : ℝ) * ((ArithmeticFunction.moebius d : ℤ) : ℝ)

def orthogonalExpansion {V : Type*} [SeminormedAddCommGroup V]
    [InnerProductSpace ℝ V] (e : ℕ → V) : Prop :=
  (∀ d u : ℕ, 0 < d → 0 < u →
      inner ℝ (e d) (e u) =
        ((Nat.gcd d u : ℝ) ^ 2) / ((d : ℝ) * (u : ℝ))) →
    ∀ n : ℕ, 0 < n →
      fareyLevel e n =
        ∑ q ∈ n.divisors,
          fareyConvolutionCoeff (n / q) • fareyWhitened e q

end MathlibPlus.Open.NumberTheory.Claim9759
