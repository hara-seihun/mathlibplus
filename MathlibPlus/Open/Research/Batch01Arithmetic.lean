import Mathlib

namespace MathlibPlus.Open.Research

noncomputable section

open scoped BigOperators

/-- The exponent of a prime in a natural number, represented by factorization. -/
def primeExponent (p n : ℕ) : ℕ := n.factorization p

/-- The prime-power component `p^(v_p(n))`. -/
def primePowerComponent (n p : ℕ) : ℕ :=
  p ^ primeExponent p n

/-- The common block assembled from a finite set of prime divisors. -/
def commonBlock (n : ℕ) (S : Finset ℕ) : ℕ :=
  S.prod (fun p => primePowerComponent n p)

/-- The natural index represented by an integer multiple of a common block. -/
def commonBlockIndex (n : ℕ) (S : Finset ℕ) (t : ℤ) : ℕ :=
  (((commonBlock n S : ℤ) * t).toNat)

/-- The compressed binomial index belonging to a prime component. -/
def compressedBinomialIndex
    (n : ℕ) (S : Finset ℕ) (t : ℤ) (p : ℕ) : ℕ :=
  ((((commonBlock n S / primePowerComponent n p : ℕ) : ℤ) * t).toNat)

/-- The common-block divisor from the selected prime components. -/
def commonBlockDivisor
    (n : ℕ) (S : Finset ℕ) (t : ℤ) : ℕ :=
  S.prod (fun p =>
    p ^ max 0
      (primeExponent p n -
        primeExponent p
          (Nat.choose (n / primePowerComponent n p)
            (compressedBinomialIndex n S t p))))

/-- The height factor `H_n(k) = n / gcd(n, binomial(n,k))`. -/
def binomialHeight (n k : ℕ) : ℕ :=
  n / Nat.gcd n (Nat.choose n k)

/-- The simultaneous common-block divisibility assertion. -/
def simultaneousCommonBlockDivisibility : Prop :=
  ∀ (n : ℕ) (S : Finset ℕ),
    S.Nonempty →
    (∀ p ∈ S, Nat.Prime p ∧ p ∣ n) →
    ∀ t : ℤ,
      2 ≤ (commonBlock n S : ℤ) * t →
      (commonBlock n S : ℤ) * t ≤ (n / 2 : ℕ) →
      commonBlockDivisor n S t ∣
        binomialHeight n (commonBlockIndex n S t)

end

end MathlibPlus.Open.Research
