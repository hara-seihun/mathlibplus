import Mathlib

namespace MathlibPlus.Open.NumberTheory.K0164Claim9735

open scoped BigOperators

noncomputable section

private def ramanujanSum9735 (q k : ℕ) : ℤ :=
  ∑ d ∈ (Nat.divisors q).filter (fun d => d ∣ k),
    (d : ℤ) * (ArithmeticFunction.moebius (q / d) : ℤ)

private def mertens9735 (n : ℕ) : ℤ :=
  ∑ m ∈ Finset.Icc 1 n, (ArithmeticFunction.moebius m : ℤ)

/-- Claim 9735: the exact finite Ramanujan divisor transform equals its
Möbius/Mertens divisor expansion, with the positive Fourier mode retained. -/
def claim9735_summedRamanujanDivisorTransform : Prop :=
  ∀ (N k : ℕ),
    0 < k →
      (∑ q ∈ Finset.Icc 1 N, ramanujanSum9735 q k) =
        ∑ d ∈ Nat.divisors k,
          (d : ℤ) * mertens9735 (N / d)

end

end MathlibPlus.Open.NumberTheory.K0164Claim9735
