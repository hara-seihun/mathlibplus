import MathlibPlus.Open.NumberTheory.CRTPrimeAdversityClaim

namespace MathlibPlus.Open.ResearchFormalization.R2063Claim35959

open scoped BigOperators
open Filter
open MathlibPlus.Open.NumberTheory.Claim35956

noncomputable section

/-- Chebyshev's theta function on the exact real-cutoff prime carrier. -/
def thetaPrime (z : ℝ) : ℝ :=
  ∑ p ∈ primesUpTo z, Real.log (p : ℝ)

/-- The critical small-remainder cutoff `K=floor(z/log(N)^2)`. -/
def smallRemainderCutoff (N : ℕ) : ℕ :=
  Nat.floor (criticalScale N / Real.log (N : ℝ) ^ 2)

def smallRemainderPrimes (N : ℕ) : Finset ℕ :=
  (primesUpTo (criticalScale N)).filter (fun p =>
    1 ≤ N % p ∧ N % p ≤ smallRemainderCutoff N)

def goodPrimes (N : ℕ) : Finset ℕ :=
  (primesUpTo (criticalScale N)).filter (fun p =>
    smallRemainderCutoff N < p ∧ p ∉ smallRemainderPrimes N)

def goodPrimeLogContribution (N : ℕ) : ℝ :=
  ∑ p ∈ goodPrimes N,
    Real.log (localMultiplicity N p : ℝ)

def goodPrimeLowerBound (N : ℕ) : ℝ :=
  (thetaPrime (criticalScale N) -
      thetaPrime (smallRemainderCutoff N : ℝ) -
      ∑ p ∈ smallRemainderPrimes N, Real.log (p : ℝ)) /
    Real.log (criticalScale N)

/-- Claim 35959: every good prime contributes a maximizing residue count above
    `K`, and the exact prime-layer count and logarithmic contribution have the
    displayed critical-scale asymptotics. -/
def manyGoodPrimesLargeMaximizingResidueCount_claim35959 : Prop :=
  (∀ N : ℕ, ∀ p ∈ goodPrimes N,
    (p ∣ N ∧ localMultiplicity N p = p ∧
        smallRemainderCutoff N < localMultiplicity N p) ∨
      (¬ p ∣ N ∧ N % p > smallRemainderCutoff N ∧
        localMultiplicity N p = N % p)) ∧
  (∀ᶠ N : ℕ in atTop,
    goodPrimeLowerBound N ≤ (goodPrimes N).card) ∧
  Asymptotics.IsEquivalent atTop
    (fun N : ℕ => Real.log (smallRemainderCutoff N : ℝ))
    (fun N : ℕ => Real.log (criticalScale N)) ∧
  Asymptotics.IsEquivalent atTop
    (fun N : ℕ => ((goodPrimes N).card : ℝ))
    (fun N : ℕ => criticalScale N / Real.log (criticalScale N)) ∧
  Asymptotics.IsEquivalent atTop goodPrimeLogContribution
    (fun N : ℕ => criticalScale N)

end

end MathlibPlus.Open.ResearchFormalization.R2063Claim35959
