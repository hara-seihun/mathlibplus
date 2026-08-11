import MathlibPlus.Basic

namespace MathlibPlus.Open.NumberTheory

open scoped BigOperators

/--
The exact gcd-kernel reconstruction from claim 9755.  The source's
`K(m,n)=(gcd(m,n))^2/(mn)` and `R(d)=∏_{p∣d}(1-p⁻²)` are inlined; division is
rational division, and the displayed sum is over the positive divisors of the
(nonzero, by the hypotheses) gcd.
-/
def exactGcdKernelReconstruction_claim9755 : Prop :=
  ∀ (m n : ℕ),
    0 < m → 0 < n →
      (Nat.gcd m n : ℚ) ^ 2 / ((m : ℚ) * (n : ℚ)) =
        ∑ d ∈ (Nat.gcd m n).divisors,
          ((d : ℚ) / (m : ℚ)) * ((d : ℚ) / (n : ℚ)) *
            (∏ p ∈ d.primeFactors, (1 - (p : ℚ) ^ (-(2 : ℤ))))

end MathlibPlus.Open.NumberTheory
