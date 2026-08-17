import MathlibPlus.NumberTheory.Claim35955

open scoped BigOperators
open Classical

namespace MathlibPlus.Open.NumberTheory.Claim35956

/-- The critical scale `z = sqrt (N / log N)`. -/
noncomputable def criticalScale (N : ℕ) : ℝ :=
  Real.sqrt ((N : ℝ) / Real.log (N : ℝ))

/-- The finite set of primes at most a real cutoff. -/
noncomputable def primesUpTo (z : ℝ) : Finset ℕ :=
  (Finset.range (Nat.floor z + 1)).filter
    (fun p => Nat.Prime p ∧ (p : ℝ) ≤ z)

/-- The primorial `P(z)`. -/
noncomputable def primorial (z : ℝ) : ℕ :=
  ∏ p ∈ primesUpTo z, p

/-- The local number of maximizing residue classes. -/
def localMultiplicity (N p : ℕ) : ℕ :=
  if p ∣ N then p else N % p

/-- The exact prime interval remainder on a natural representative of a shift. -/
def primeRemainder (p N t : ℕ) : ℚ :=
  MathlibPlus.NumberTheory.Claim35955.intervalRemainder p N t

/-- A representative modulo `P` at which one prime remainder is maximal. -/
def primeRemainderMaximizer (p N P t : ℕ) : Prop :=
  t < P ∧
    ∀ u : ℕ, u < P → primeRemainder p N t ≤ primeRemainder p N u

/-- Simultaneous attainment of every local prime maximum at the primorial
period. -/
def simultaneousPrimeMaximizer (N : ℕ) (z : ℝ) (t : ℕ) : Prop :=
  let P := primorial z
  t < P ∧
    ∀ p ∈ primesUpTo z, primeRemainderMaximizer p N P t

/-- `M(N,z)`, the number of shifts modulo `P(z)` with all local maxima. -/
noncomputable def simultaneousPrimeMaximizerCount (N : ℕ) (z : ℝ) : ℕ :=
  (Finset.range (primorial z)).filter (simultaneousPrimeMaximizer N z) |>.card

/-- The lower-Rosser prime layer with its common prime coefficient explicit.
The source supplies only that this coefficient is negative. -/
noncomputable def lowerRosserPrimeLayer (c : ℚ) (N : ℕ) (z : ℝ) (t : ℕ) : ℚ :=
  ∑ p ∈ primesUpTo z, c * primeRemainder p N t

/-- A minimum of the lower prime layer on the primorial period. -/
def lowerRosserPrimeLayerMinimizer
    (c : ℚ) (N : ℕ) (z : ℝ) (t : ℕ) : Prop :=
  let P := primorial z
  t < P ∧
    ∀ u : ℕ, u < P →
      lowerRosserPrimeLayer c N z t ≤ lowerRosserPrimeLayer c N z u

/-- Claim 35956: the CRT product count and the exact adverse-shift
interpretation for every negative lower-Rosser prime coefficient. -/
def claim35956_crtProductFormula : Prop :=
  ∀ N : ℕ,
    let z := criticalScale N
    let P := primorial z
    simultaneousPrimeMaximizerCount N z =
        ∏ p ∈ primesUpTo z, localMultiplicity N p ∧
      ∀ c : ℚ, c < 0 →
        ∀ t : ℕ, t < P →
          (simultaneousPrimeMaximizer N z t ↔
            lowerRosserPrimeLayerMinimizer c N z t)

end MathlibPlus.Open.NumberTheory.Claim35956
