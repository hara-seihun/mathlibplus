import MathlibPlus.Open.NewResearch2.ThetaKernel

open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2.PrimeRenewal15232

noncomputable section

open MathlibPlus.Open.NewResearch2.ThetaKernel

/-- The theta field with exactly the positive-indexed shells whose indices avoid
all primes in the finite deletion set. -/
def primeDeletedField (P : Finset ℕ) (u : ℝ) : ℝ :=
  ∑' n : ℕ,
    if 1 ≤ n ∧ ∀ p ∈ P, ¬ p ∣ n then thetaShell n u else 0

/-- The positive-index finite theta field at cutoff `M`. -/
def thetaFieldCutoff (M : ℕ) (u : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 M, thetaShell n u

/-- The positive-index finite field after deleting indices divisible by a
prime in `P`. -/
def primeDeletedFieldCutoff (P : Finset ℕ) (M : ℕ) (u : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 M,
    if ∀ p ∈ P, ¬ p ∣ n then thetaShell n u else 0

/-- Finite prime deletion is the exact Möbius renewal identity, with the
translated finite cutoff replaced by `⌊M/d⌋`. -/
def claim_15232 : Prop :=
  ∀ (P : Finset ℕ) (u : ℝ) (M : ℕ),
    (∀ p ∈ P, Nat.Prime p) →
    let R_P : ℕ := ∏ p ∈ P, p
    primeDeletedField P u =
        ∑ d ∈ Nat.divisors R_P,
          (ArithmeticFunction.moebius d : ℝ) *
              Real.rpow (d : ℝ) (- (1 : ℝ) / 2) *
              thetaKernelPhi (u + Real.log (d : ℝ)) ∧
      primeDeletedFieldCutoff P M u =
        ∑ d ∈ Nat.divisors R_P,
          (ArithmeticFunction.moebius d : ℝ) *
              Real.rpow (d : ℝ) (- (1 : ℝ) / 2) *
              thetaFieldCutoff (M / d) (u + Real.log (d : ℝ))

end
end MathlibPlus.Open.NewResearch2.PrimeRenewal15232
