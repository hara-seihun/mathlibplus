import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchQ0135

/-- Composite natural numbers, used as the domain restriction in the packet. -/
def composite (n : ℕ) : Prop :=
  ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ n = a * b

/-- The set of gcd values occurring in the specified row range. -/
def rowGcdValues (n : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (n / 2)).image (fun k => Nat.gcd n (Nat.choose n k))

/-- The minimum row binomial gcd, with an irrelevant total-value convention below the
range where the displayed minimum is nonempty. -/
def rowBinomialGcd (n : ℕ) : ℕ :=
  if h : (rowGcdValues n).Nonempty then
    (rowGcdValues n).min' h
  else 0

/-- The least-prime-factor notation used in the admitted statements. -/
def leastPrimeFactor (n : ℕ) : ℕ := n.minFac

/-- Prime-power components indexed by the prime support of the factorization. -/
def primePowerComponents (n : ℕ) : Finset ℕ :=
  ((Nat.factorization n).support.filter Nat.Prime).image
    (fun p => p ^ (Nat.factorization n p))

/-- The largest exact prime-power component. -/
def largestPrimePowerComponent (n : ℕ) : ℕ :=
  if h : (primePowerComponents n).Nonempty then
    (primePowerComponents n).max' h
  else 1

/-- The explicit equality-family condition `n = p q^a` with distinct primes `p < q`. -/
def pqPowerFamily (n : ℕ) : Prop :=
  ∃ p q a : ℕ,
    Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ 1 ≤ a ∧ n = p * q ^ a

/-- Claim 16897: the row minimum, least-prime-factor notation, and largest
exact prime-power notation used by the packet. -/
def claim16897 : Prop :=
  ∀ n : ℕ, composite n →
    (∃ h : (rowGcdValues n).Nonempty,
      rowBinomialGcd n = (rowGcdValues n).min' h) ∧
    leastPrimeFactor n = n.minFac ∧
    (∃ h : (primePowerComponents n).Nonempty,
      largestPrimePowerComponent n = (primePowerComponents n).max' h)

/-- Claim 16903: the baseline equality examples and the prime-square lower
boundary. -/
def claim16903 : Prop :=
  (∀ p q : ℕ, Nat.Prime p → Nat.Prime q → p ≠ q →
    rowBinomialGcd (p * q) = (p * q) / largestPrimePowerComponent (p * q)) ∧
  rowBinomialGcd 30 = 30 / largestPrimePowerComponent 30 ∧
  (∀ n : ℕ, composite n → leastPrimeFactor n ≤ rowBinomialGcd n) ∧
  (∀ p : ℕ, Nat.Prime p → rowBinomialGcd (p ^ 2) ≥ p ∧ p = Nat.sqrt (p ^ 2))

/-- Base-p digit sum. -/
def digitSum (p n : ℕ) : ℕ := (Nat.digits p n).sum

/-- The number of base-p carries, expressed by the standard digit-sum
identity for the sum of two naturals. -/
def carryCount (p x y : ℕ) : ℕ :=
  (digitSum p x + digitSum p y - digitSum p (x + y)) / (p - 1)

/-- The p-adic valuation represented by the exponent in the prime factorization. -/
def primeValuation (p n : ℕ) : ℕ := Nat.factorization n p

/-- Digitwise comparison in base p. -/
def digitwiseLE (p k n : ℕ) : Prop :=
  ∀ i : ℕ, (k / p ^ i) % p ≤ (n / p ^ i) % p

/-- Claim 16904: Kummer's carry formula and the corresponding Lucas
criterion for absence from the row gcd. -/
def claim16904 : Prop :=
  (∀ p n k : ℕ, Nat.Prime p → p ∣ n → k ≤ n →
    primeValuation p (Nat.choose n k) = carryCount p k (n - k)) ∧
  (∀ p n k : ℕ, Nat.Prime p → p ∣ n → k ≤ n →
    (¬ p ∣ Nat.gcd n (Nat.choose n k)) ↔ digitwiseLE p k n)

/-- Claim 16905: the close-prime triple dichotomy. -/
def claim16905 : Prop :=
  ∀ p q r : ℕ,
    Nat.Prime p → Nat.Prime q → Nat.Prime r →
    p < q → q < r →
    p > 10 * (r - p) ^ 2 →
    rowBinomialGcd (p * q * r) =
      if r - q > q - p then p * q else p

/-- Claim 16909: the equality slice where the upper cofactor is the least
prime. -/
def claim16909 : Prop :=
  ∀ n : ℕ, composite n →
    (n / largestPrimePowerComponent n = leastPrimeFactor n ↔ pqPowerFamily n)

/-- Claim 16910: the exact `p q^a` equality family and its displayed
minimizing row. -/
def claim16910 : Prop :=
  ∀ p q a : ℕ,
    Nat.Prime p → Nat.Prime q → p < q → 1 ≤ a →
    largestPrimePowerComponent (p * q ^ a) = q ^ a ∧
    rowBinomialGcd (p * q ^ a) = p ∧
    Nat.gcd (p * q ^ a) (Nat.choose (p * q ^ a) (q ^ a)) = p

/-- Claim 16911: the stated `n = 12` equality example lies outside the
previously asserted `p q^a`, `p < q` family. -/
def claim16911 : Prop :=
  rowBinomialGcd 12 = 12 / largestPrimePowerComponent 12 ∧
  ¬ pqPowerFamily 12

/-- Claim 16912: the infinite `3 * 2^a` equality family and its exact
minimizing index. -/
def claim16912 : Prop :=
  ∀ a : ℕ, 2 ≤ a →
    largestPrimePowerComponent (3 * 2 ^ a) = 2 ^ a ∧
    rowBinomialGcd (3 * 2 ^ a) = 3 ∧
    Nat.gcd (3 * 2 ^ a) (Nat.choose (3 * 2 ^ a) (2 ^ a)) = 3

/-- Varying-top-row gcd in Claim 16914. -/
def varyingRowGcd (k : ℕ) : ℕ :=
  ((Finset.Icc 2 (k + 1)).image (fun q => Nat.choose (q * k) k)).gcd id

/-- Claim 16914: the varying-row criterion, with the largest exact
prime-power component as `P`. -/
def claim16914 : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    (varyingRowGcd k = 1 ↔
      (k + 1) / largestPrimePowerComponent (k + 1) >
        largestPrimePowerComponent (k + 1))

end MathlibPlus.Open.ResearchFormalization.BatchQ0135
