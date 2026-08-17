import Mathlib
import MathlibPlus.Analysis.DyadicTail

namespace MathlibPlus.Open.ResearchFormalization.R2833R3678

noncomputable section
open scoped BigOperators

/-- The exact dyadic weights and tail sums. -/
def dyadicWeight (j : ℕ) : ℝ :=
  (j : ℝ) / (2 : ℝ) ^ j

def dyadicTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, dyadicWeight (j + (N + 1))

def binaryTailSubsetSum (N : ℕ) (e : ℕ → Bool) : ℝ :=
  ∑' j : ℕ,
    if N < j ∧ e j = true then dyadicWeight j else 0

/-- Claim 47277: every point in every dyadic tail interval has a binary
expansion using precisely later weights, and the full subset-sum set is [0,2]. -/
def claim47277_infiniteDyadicSubsetExpansion : Prop :=
  (∀ N : ℕ, ∀ y : ℝ, 0 ≤ y → y ≤ dyadicTail N →
    ∃ e : ℕ → Bool, binaryTailSubsetSum N e = y) ∧
  (∀ y : ℝ, 0 ≤ y → y ≤ 2 →
    ∃ e : ℕ → Bool, binaryTailSubsetSum 0 e = y) ∧
  (∀ e : ℕ → Bool,
    0 ≤ binaryTailSubsetSum 0 e ∧ binaryTailSubsetSum 0 e ≤ 2)

/-- Claim 47278: after clearing the exact dyadic denominator, a positive
finite later-term representation is precisely the displayed offset equation. -/
def claim47278_finiteOffsetTiling : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    (∀ j : ℕ, 2 ≤ j → dyadicWeight (j + 1) < dyadicWeight j) ∧
    ∀ D : Finset ℕ,
      (∀ d ∈ D, 0 < d) →
        (dyadicWeight n =
            Finset.sum D (fun d => dyadicWeight (n + d))) ↔
          (n : ℝ) =
            Finset.sum D (fun d => ((n + d : ℕ) : ℝ) / (2 : ℝ) ^ d)

/-- The selected finite offsets before a residual path reaches zero. -/
def selectedOffsets (n : ℕ) (r : ℕ → ℕ) (k : ℕ) : Finset ℕ :=
  (Finset.range (k + 1)).filter (fun d => 0 < d ∧ r d ≥ n + d)

/-- Claim 47279: the greedy residual recurrence and its conditional tiling
conclusion; no termination assertion is added. -/
def claim47279_greedyResidualRecurrence : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    ∀ r : ℕ → ℕ, r 1 = 2 * n →
      (∀ d : ℕ, 1 ≤ d →
        r d < 2 * (n + d) →
          r (d + 1) = 2 * (r d % (n + d))) →
      (∃ e : ℕ → Bool,
        (∀ d : ℕ, 1 ≤ d →
          (e d = true ↔ r d ≥ n + d)) ∧
        (∀ k : ℕ, 1 ≤ k → r (k + 1) = 0 →
          (n : ℝ) =
            Finset.sum (selectedOffsets n r k)
              (fun d => ((n + d : ℕ) : ℝ) / (2 : ℝ) ^ d)))

/-- Wall atoms and their exponent moments. -/
def wallLowAtom (t : ℝ) : ℝ :=
  Real.exp (-Real.pi * Real.exp (-t))

def wallHighAtom (t : ℝ) : ℝ :=
  Real.exp (-Real.pi * Real.exp t)

def wallLowWeight (t : ℝ) : ℝ :=
  Real.rpow (Real.exp (-t)) (5 / 4 : ℝ)

def wallHighWeight (t : ℝ) : ℝ :=
  Real.rpow (Real.exp (-t)) (-5 / 4 : ℝ)

def wallMomentTerm (t : ℝ) (n : ℕ) : ℝ :=
  wallLowWeight t * wallLowAtom t ^ n +
    wallHighWeight t * wallHighAtom t ^ n

def wallMomentGenerating (t z : ℝ) : ℝ :=
  ∑' n : ℕ, wallMomentTerm t n * z ^ n

def wallMoment (t : ℝ) (n : ℕ) : ℝ :=
  wallMomentTerm t n

def wallJacobiAlpha0 (t : ℝ) : ℝ :=
  wallMoment t 1 / wallMoment t 0

def wallJacobiBeta1 (t : ℝ) : ℝ :=
  (wallMoment t 0 * wallMoment t 2 - (wallMoment t 1) ^ 2) /
    (wallMoment t 0) ^ 2

def wallJacobiAlpha1 (t : ℝ) : ℝ :=
  let α := wallJacobiAlpha0 t
  (wallMoment t 3 - 2 * α * wallMoment t 2 + α ^ 2 * wallMoment t 1) /
    (wallMoment t 2 - 2 * α * wallMoment t 1 + α ^ 2 * wallMoment t 0)

/-- Claim 47671: the pre-square-lattice wall moment series is the positive
 two-atom rational Stieltjes function with the displayed Jacobi data. -/
def claim47671_twoAtomWallMoments : Prop :=
  ∀ t : ℝ, 0 < t →
    0 < wallHighAtom t ∧ wallHighAtom t < wallLowAtom t ∧
      wallLowAtom t < 1 ∧
      0 < wallLowWeight t ∧ 0 < wallHighWeight t ∧
      (∀ z : ℝ, |z| < 1 →
        wallMomentGenerating t z =
          wallLowWeight t / (1 - z * wallLowAtom t) +
            wallHighWeight t / (1 - z * wallHighAtom t)) ∧
      wallJacobiAlpha0 t =
        (wallLowWeight t * wallLowAtom t +
          wallHighWeight t * wallHighAtom t) /
          (wallLowWeight t + wallHighWeight t) ∧
      wallJacobiBeta1 t =
        wallLowWeight t * wallHighWeight t *
          (wallLowAtom t - wallHighAtom t) ^ 2 /
          (wallLowWeight t + wallHighWeight t) ^ 2 ∧
      wallJacobiAlpha1 t =
        (wallLowWeight t * wallHighAtom t +
          wallHighWeight t * wallLowAtom t) /
          (wallLowWeight t + wallHighWeight t)

end
end MathlibPlus.Open.ResearchFormalization.R2833R3678
