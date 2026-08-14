import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch.Combinatorics

open scoped BigOperators
open BigOperators

noncomputable section

/-- An explicit series definition of the Euler--Mascheroni constant. -/
def eulerGamma : ℝ :=
  ∑' n : ℕ, ((1 / ((n + 1 : ℕ) : ℝ)) -
    Real.log (1 + 1 / ((n + 1 : ℕ) : ℝ)))

def primeProduct (y : ℕ) (f : ℕ → ℝ) : ℝ :=
  Finset.prod (Finset.filter Nat.Prime (Finset.Icc 2 y)) f

def correctionFactor (k y : ℕ) : ℝ :=
  primeProduct y (fun p =>
    (1 - (p : ℝ)⁻¹) ^ (1 - (k : ℤ)))

/-- The fixed-k Mertens asymptotic for the small-prime correction factor. -/
def correctionFactorAsymptotic : Prop :=
  ∀ (k : ℕ), 2 ≤ k →
    Filter.Tendsto
      (fun y : ℕ =>
        correctionFactor k y /
          (Real.exp eulerGamma * Real.log (y : ℝ)) ^ (k - 1))
      Filter.atTop (nhds 1)

/-- The divisor-count function and the finite replay maximum. -/
def divisorCount (m : ℕ) : ℕ :=
  (Finset.filter (fun d : ℕ => d ∣ m) (Finset.Icc 1 m)).card

def replayMaximum (n : ℕ) : ℕ :=
  (Finset.image (fun m : ℕ => m + divisorCount m) (Finset.Icc 1 (n - 1))).sup id

/-- The stated finite range lower bound and the reported equality at `35`. -/
def divisorReplayBound : Prop :=
  (∀ n : ℕ, 25 ≤ n → n ≤ 10000000 → replayMaximum n ≥ n + 3) ∧
    replayMaximum 35 - 35 = 3


end
end MathlibPlus.Open.ResearchFormalizationBatch.Combinatorics
