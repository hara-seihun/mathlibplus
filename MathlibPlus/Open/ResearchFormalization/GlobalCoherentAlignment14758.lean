import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch14758

open scoped BigOperators

noncomputable section

/-- The character polynomial used for a prime-power coefficient. -/
private def character (k : ℕ) (z : ℂ) : ℂ :=
  ∑ r ∈ Finset.range (k + 1),
    z ^ ((k : ℤ) - 2 * (r : ℤ))

/-- The order-eleven-and-a-half prime scale from the normalized coefficients. -/
private def primeScale (p : ℕ) : ℂ :=
  Complex.ofReal ((p : ℝ) ^ (11 / 2 : ℝ))

/-- A Satake phase, with the half-angle convention of the local square. -/
private def satakePhase (φ : ℕ → ℝ) (p : ℕ) : ℂ :=
  Complex.exp (Complex.I * (φ p / 2))

/-- The finite subtype of primes occurring in the factorization of `n`. -/
private abbrev PrimeIndex (n : ℕ) :=
  {p : ℕ // p ∈ Nat.primeFactors n}

/-- Exact harmonic multiweights: one coordinate in `[-k_p,k_p]` for every
prime in the factorization of `n`.  `Lex` supplies a fixed finite order for
choosing representatives below. -/
private abbrev HarmonicIndex (n : ℕ) :=
  Lex (∀ p : PrimeIndex n,
    Fin (2 * Nat.factorization n p.1 + 1))

private def zeroIndex (n : ℕ) : HarmonicIndex n :=
  toLex (fun p =>
    ⟨Nat.factorization n p.1, by omega⟩)

/-- Simultaneous negation of all harmonic weights. -/
private def negIndex (n : ℕ) (m : HarmonicIndex n) : HarmonicIndex n :=
  toLex (fun p => Fin.rev ((ofLex m) p))

private def harmonicWeight (n : ℕ) (p : PrimeIndex n)
    (m : HarmonicIndex n) : ℤ :=
  (((ofLex m) p).val : ℤ) - (Nat.factorization n p.1 : ℤ)

private def harmonicMultiplicity (n : ℕ) (m : HarmonicIndex n) : ℕ :=
  ∏ p : PrimeIndex n,
    (Nat.factorization n p.1 - Int.natAbs (harmonicWeight n p m) + 1)

private def harmonicU (n : ℕ) (m : HarmonicIndex n) : ℝ :=
  11 * ∑ p : PrimeIndex n,
    (harmonicWeight n p m : ℝ) * Real.log (p.1 : ℝ)

private def harmonicPhi (n : ℕ) (φ : ℕ → ℝ) (m : HarmonicIndex n) : ℝ :=
  ∑ p : PrimeIndex n,
    (harmonicWeight n p m : ℝ) * φ p.1

/-- The summand attached to one harmonic multiweight. -/
private def harmonicCurrent (n : ℕ) (φ : ℕ → ℝ)
    (m : HarmonicIndex n) : ℂ :=
  (harmonicMultiplicity n m : ℂ) *
    Complex.ofReal (Real.sinh (harmonicU n m)) *
    Complex.ofReal (Real.sin (harmonicPhi n φ m))

/-- The canonical finite set for `m/{±1}`, with no elements outside the
exact signed-orbit domain.  Each nonzero orbit contributes its lexicographically
smaller member exactly once. -/
private def signedOrbitRepresentatives (n : ℕ) : Finset (HarmonicIndex n) := by
  classical
  exact (Finset.univ : Finset (HarmonicIndex n)).filter (fun m =>
    m ≠ zeroIndex n ∧ m < negIndex n m)

private def coherentPlus (n : ℕ) (φ : ℕ → ℝ) : ℂ :=
  ∏ p ∈ Nat.primeFactors n,
    character (Nat.factorization n p)
      (primeScale p * satakePhase φ p)

private def coherentMinus (n : ℕ) (φ : ℕ → ℝ) : ℂ :=
  ∏ p ∈ Nat.primeFactors n,
    character (Nat.factorization n p)
      (primeScale p * (satakePhase φ p)⁻¹)

/-- The global coherent-alignment current.  The finite index and its
canonical signed-orbit representatives are the exact multiweight carriers
for the notation `m/{±1}, m ≠ 0`. -/
def claim14758 : Prop :=
  ∀ (n : ℕ) (φ : ℕ → ℝ), n ≠ 0 →
    (coherentPlus n φ ^ 2 - coherentMinus n φ ^ 2) /
        (4 * Complex.I) =
      ∑ m ∈ signedOrbitRepresentatives n, harmonicCurrent n φ m

end

end MathlibPlus.Open.ResearchFormalizationBatch14758
