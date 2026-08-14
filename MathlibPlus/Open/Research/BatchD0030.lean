import Mathlib

namespace MathlibPlus.Open.ResearchBatch.D0030

open scoped BigOperators

noncomputable def finiteAtomicShiftIntegral
    (μ : ℝ →₀ ℝ) (f : ℝ → ℝ) : ℝ :=
  μ.sum (fun α w => w * f α)

def finiteAtomicShiftIntegral_claim : Prop :=
  ∀ (μ : ℝ →₀ ℝ) (f : ℝ → ℝ),
    finiteAtomicShiftIntegral μ f =
      ∑ α ∈ μ.support, μ α * f α

noncomputable def shiftPacket (a : ℝ) (p : ℝ →₀ ℤ) : ℝ →₀ ℤ :=
  Finsupp.mapDomain (fun α => α + a) p

noncomputable def packetPrimeCoeff (prime : ℕ) (p : ℝ →₀ ℤ) : ℝ :=
  ∑ α ∈ p.support, (p α : ℝ) * Real.rpow (prime : ℝ) (-α)

def primeCoefficientCovariance_claim : Prop :=
  (∀ (prime : ℕ) (a : ℝ) (p : ℝ →₀ ℤ),
      0 < prime →
        packetPrimeCoeff prime (shiftPacket a p) =
          Real.rpow (prime : ℝ) (-a) * packetPrimeCoeff prime p) ∧
    (∀ (prime : ℕ), packetPrimeCoeff prime 0 = 0)

noncomputable def packetTotalExponent (p : ℝ →₀ ℤ) : ℤ :=
  ∑ α ∈ p.support, p α

noncomputable def packetShiftMoment (p : ℝ →₀ ℤ) (degree : ℕ) : ℝ :=
  ∑ α ∈ p.support, (p α : ℝ) * α ^ degree

def reflectionInvariant (p : ℝ →₀ ℤ) : Prop :=
  ∀ α : ℝ, p (-α) = p α

def balancedCompletedPacket (p : ℝ →₀ ℤ) : Prop :=
  packetTotalExponent p = 0 ∧ packetShiftMoment p 1 = 0

def reflectionInvarianceForcesFirstMomentCancellation_claim : Prop :=
  ∀ p : ℝ →₀ ℤ,
    reflectionInvariant p →
      packetShiftMoment p 1 = 0 ∧
        (packetTotalExponent p = 0 → balancedCompletedPacket p)

end MathlibPlus.Open.ResearchBatch.D0030
