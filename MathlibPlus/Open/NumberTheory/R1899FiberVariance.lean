import MathlibPlus.Open.NumberTheory.R1899RoughSieveAndEntropy

open scoped BigOperators
open Classical
noncomputable section

namespace MathlibPlus.Open.NumberTheory.R1899FiberVariance

open MathlibPlus.Open.NumberTheory.R1899

def varianceAtPrime {Q N p : ℕ} (t : Fin Q) : ℝ :=
  ∑ a : Fin p,
    ((residueCount (N := N) t a : ℝ) -
      (roughCount (N := N) t : ℝ) / (p : ℝ)) ^ 2

/-- The maximum residue fiber used by the Cauchy reduction. -/
def maximumResidueFiber {Q N p : ℕ}
    (t : Fin Q) (a : Fin p) : ℕ :=
  residueCount (N := N) t a

def maximumResidueCount {Q N p : ℕ}
    (t : Fin Q) : ℕ :=
  Finset.univ.sup
    (fun a : Fin p => maximumResidueFiber (N := N) t a)

def selectedResidueSurvivor {Q N : ℕ}
    (P : Finset ℕ) (t : Fin Q)
    (selected : ∀ p, p ∈ P → Fin p) : Prop :=
  ∃ n ∈ roughSurvivors (N := N) t,
    ∀ p hp, n % p ≠ (selected p hp).val

/-- Claim 34775: exact maximum-fiber, Cauchy, and survivor consequences on
R-1899's primorial rough-survivor and tail-prime carrier. -/
def fiberVarianceMaximumReduction_claim34775 : Prop :=
  ∀ (N z : ℕ) (P : Finset ℕ),
    let Q := primorialUpTo z
    (∀ p ∈ P, Nat.Prime p ∧ ¬ p ∣ Q) →
      ∀ t : Fin Q,
        (∀ p ∈ P,
          (maximumResidueCount (N := N) (p := p) t : ℝ) ≤
            (roughCount (N := N) t : ℝ) / (p : ℝ) +
              Real.sqrt (varianceAtPrime (N := N) (p := p) t)) ∧
        ((∑ p ∈ P, (maximumResidueCount (N := N) (p := p) t : ℝ)) ≤
          (roughCount (N := N) t : ℝ) * tailPrimeSum P +
            Real.sqrt ((P.card : ℝ) * fiberVariance (N := N) P t)) ∧
        ((0 < roughCount (N := N) t ∧
            tailPrimeSum P +
                Real.sqrt ((P.card : ℝ) * fiberVariance (N := N) P t) /
                  (roughCount (N := N) t : ℝ) < 1) →
          ∀ selected : ∀ p, p ∈ P → Fin p,
            selectedResidueSurvivor (N := N) P t selected)

end MathlibPlus.Open.NumberTheory.R1899FiberVariance
