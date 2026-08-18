import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R2017HighPrime

noncomputable section
open Classical
open scoped BigOperators

/-- The finite set of primes satisfying the literal interval condition
`x < p ≤ 2*x`. -/
def primeCarrier (x : ℕ) : Finset ℕ :=
  (Finset.Icc 0 (2 * x)).filter
    (fun p => Nat.Prime p ∧ x < p ∧ p ≤ 2 * x)

/-- The nonzero block belonging to one prime. -/
def multipleBlock (p M : ℕ) : Finset ℕ :=
  (Finset.Icc 1 M).image (fun m => m * p)

/-- The construction `R = {0} ∪ {m p : p ∈ 𝒫, 1 ≤ m ≤ M}`. -/
def highPrimeSet (x M : ℕ) : Finset ℕ :=
  insert 0 ((primeCarrier x).biUnion (fun p => multipleBlock p M))

/-- The exact parameter range in the admitted high-prime construction. -/
def highPrimeParameters (x N M : ℕ) : Prop :=
  x ≥ 2 ∧
    N = x ^ 2 ∧
      1 ≤ M ∧
        M < x ∧
          2 * x * M < N ∧
            M + 1 ≥ (primeCarrier x).card - 1

/-- The literal residue fiber in `R` at a natural residue representative. -/
def residueFiber (x M p a : ℕ) : Finset ℕ :=
  (highPrimeSet x M).filter (fun r => Nat.ModEq p r a)

/-- The zero fiber at `p`. -/
def zeroFiber (x M p : ℕ) : Finset ℕ :=
  residueFiber x M p 0

/-- The part of another prime block lying in a specified `p`-fiber. -/
def blockResidueFiber (M p q a : ℕ) : Finset ℕ :=
  (multipleBlock q M).filter (fun r => Nat.ModEq p r a)

/-- The union of all zero fibers. -/
def zeroFiberUnion (x M : ℕ) : Finset ℕ :=
  (primeCarrier x).biUnion (fun p => zeroFiber x M p)

/-- Injectivity of the pair of residue maps on the actual finite carrier `R`. -/
def pairResidueInjective (x M p q : ℕ) : Prop :=
  ∀ a b : ℕ,
    a ∈ highPrimeSet x M →
      b ∈ highPrimeSet x M →
        Nat.ModEq p a b → Nat.ModEq q a b → a = b

/-- The uniform zero-fiber objective from the construction. -/
def uniformObjective (x M : ℕ) : ℚ :=
  ∑ p ∈ primeCarrier x,
    (zeroFiber x M p).card / (highPrimeSet x M).card

/-- The divisibility contradiction used for two distinct prime blocks. -/
def impossibleBlockCollision (x M p q : ℕ) : Prop :=
  p ∈ primeCarrier x →
    q ∈ primeCarrier x →
      p ≠ q →
        ∀ m n : ℕ,
          m ∈ Finset.Icc 1 M →
            n ∈ Finset.Icc 1 M →
              m * p = n * q → p ∣ n ∧ ¬ p ∣ n

/-- Claim 35299: distinct nonzero prime-multiple blocks are disjoint and the
explicit construction has cardinality `1 + k*M`, with `k = |𝒫|`. -/
def claim35299 : Prop :=
  ∀ x N M : ℕ,
    highPrimeParameters x N M →
      let P := primeCarrier x
      (∀ p ∈ P, ∀ q ∈ P, p ≠ q →
        impossibleBlockCollision x M p q ∧
          Disjoint (multipleBlock p M) (multipleBlock q M)) ∧
        (highPrimeSet x M).card = 1 + P.card * M

/-- Claim 35301: the zero fibers are the explicit prime blocks, other blocks
are injective in every nonzero residue, the zero fiber is largest, and the
zero fibers cover the whole construction. -/
def claim35301 : Prop :=
  ∀ x N M : ℕ,
    highPrimeParameters x N M →
      let P := primeCarrier x
      (∀ p ∈ P,
        zeroFiber x M p = insert 0 (multipleBlock p M) ∧
          (zeroFiber x M p).card = M + 1 ∧
            M < p ∧
              (∀ q ∈ P, q ≠ p →
                ∀ m n : ℕ,
                  m ∈ Finset.Icc 1 M →
                    n ∈ Finset.Icc 1 M →
                      Nat.ModEq p (m * q) (n * q) → m = n) ∧
              (∀ q ∈ P, q ≠ p → ∀ a : ℕ,
                ¬ Nat.ModEq p a 0 →
                  (blockResidueFiber M p q a).card ≤ 1) ∧
              (∀ a : ℕ,
                (residueFiber x M p a).card ≤ (zeroFiber x M p).card)) ∧
        highPrimeSet x M = zeroFiberUnion x M

/-- Claim 35305: the concrete `x=100`, `N=10000`, `M=48` witness uses exactly
all 21 primes in `101,...,199`, lies in the ambient interval, has cardinality
1009, has pairwise-injective prime residues, has largest zero fibers of size
49 covering the witness, and has objective `1029/1009`. -/
def claim35305 : Prop :=
  let x := 100
  let N := 10000
  let M := 48
  let P := primeCarrier x
  let R := highPrimeSet x M
  P = (Finset.Icc 101 199).filter Nat.Prime ∧
    P.card = 21 ∧
      highPrimeParameters x N M ∧
        (∀ r ∈ R, r ∈ Finset.Ico 0 N) ∧
          R.card = 1009 ∧
            (∀ p ∈ P, ∀ q ∈ P, p ≠ q →
              pairResidueInjective x M p q) ∧
              (∀ p ∈ P,
                (zeroFiber x M p).card = 49 ∧
                  (∀ a : ℕ,
                    (residueFiber x M p a).card ≤ (zeroFiber x M p).card)) ∧
                R = zeroFiberUnion x M ∧
                  uniformObjective x M = (1029 : ℚ) / 1009

end

end MathlibPlus.Open.ResearchFormalization.R2017HighPrime
