import Mathlib
import MathlibPlus.Open.Research.FormalizationBatch0306
import MathlibPlus.Analysis.Claim18067_22419

open scoped BigOperators
open ArithmeticFunction
open MeasureTheory

namespace MathlibPlus.Open.ResearchFormalization.R0474R0538

noncomputable section

/-- The flat partition profile used by the cubic-root windows. -/
def FlatGevreyPartitionProfile (χ : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ χ t) ∧
    (∀ t : ℝ, χ t ≠ 0 → -1 < t ∧ t < 1) ∧
    (∀ y : ℝ,
      HasSum (fun j : ℤ => χ (y - (j : ℝ))) 1) ∧
    ContDiff ℝ ⊤ χ ∧
    (∀ n : ℕ, iteratedDeriv n χ (-1) = 0 ∧
      iteratedDeriv n χ 1 = 0) ∧
    ∃ C A s : ℝ, 0 < C ∧ 0 < A ∧ 1 ≤ s ∧
      ∀ n : ℕ, ∀ t : ℝ,
        ‖iteratedDeriv n χ t‖ ≤
          C * A ^ n * Real.rpow (Nat.factorial n : ℝ) s

/-- The centered weighted prime discrepancy from Claim 21844. -/
noncomputable def centeredWeightedPrimeDiscrepancy (t : ℝ) : ℝ :=
  (∑ m ∈ Finset.Icc 1 (Nat.floor (Real.exp t)),
      (if (m : ℝ) = Real.exp t then (1 / 2 : ℝ) else 1) *
        (vonMangoldt m : ℝ) / (m : ℝ)) - t +
    Real.eulerMascheroniConstant

/-- The first-shift parameter-two Laguerre feature on the real axis. -/
noncomputable def phiX (x t : ℝ) (n : ℕ) : ℝ × ℝ :=
  let p : ℝ := MathlibPlus.Open.Research.poissonWeight x n
  (Real.sqrt p * MathlibPlus.Open.Research.laguerreAtom n t,
    Real.sqrt p * MathlibPlus.Open.Research.laguerreAtom (n + 1) t)

/-- Membership in the first-shift graph carrier, written in coordinates. -/
def IsFeatureVector (u : ℕ → ℝ × ℝ) : Prop :=
  Summable (fun n : ℕ =>
    (‖(u n).1‖ ^ 2 + ‖(u n).2‖ ^ 2))

/-- The feature norm in the first-shift graph carrier, written in coordinates. -/
noncomputable def featureNorm (u : ℕ → ℝ × ℝ) : ℝ :=
  Real.sqrt (∑' n : ℕ,
    (‖(u n).1‖ ^ 2 + ‖(u n).2‖ ^ 2))

/-- The cubic-root center and its pulled-back window. -/
noncomputable def cubicCenter (j : ℕ) : ℝ :=
  ((j : ℝ) / 3) ^ 3

noncomputable def cubicWindow (χ : ℝ → ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  χ (3 * Real.rpow t (1 / 3 : ℝ) - (j : ℝ))

/-- Coordinatewise representation of the Hilbert-valued local graph vector. -/
noncomputable def localGraphVector (χ : ℝ → ℝ) (x : ℝ) (j : ℕ) : ℕ → ℝ × ℝ :=
  fun n =>
    (∫ t in Set.Ici (0 : ℝ),
        cubicWindow χ j t * centeredWeightedPrimeDiscrepancy t * (phiX x t n).1,
      ∫ t in Set.Ici (0 : ℝ),
        cubicWindow χ j t * centeredWeightedPrimeDiscrepancy t * (phiX x t n).2)

/-- Claim 21854: fixed-parameter local graph vectors have cubic-root Gaussian decay. -/
def claim21854_localGraphVectorGaussianBound : Prop :=
  ∀ χ : ℝ → ℝ, FlatGevreyPartitionProfile χ →
    ∀ x : ℝ, 0 < x →
      ∃ C η : ℝ, 0 < C ∧ 0 < η ∧
        ∀ j : ℕ,
          IsFeatureVector (localGraphVector χ x j) ∧
            featureNorm (localGraphVector χ x j) ≤
              C * Real.exp (-η * Real.rpow (cubicCenter j) (2 / 3 : ℝ)) ∧
            C * Real.exp (-η * Real.rpow (cubicCenter j) (2 / 3 : ℝ)) =
              C * Real.exp (-η * (j : ℝ) ^ 2 / 9)

/-- Claim 21855: the indexed local graph vectors are absolutely summable. -/
def claim21855_absoluteSummabilityOfLocalGraphVectors : Prop :=
  ∀ χ : ℝ → ℝ, FlatGevreyPartitionProfile χ →
    ∀ x : ℝ, 0 < x →
      (∀ j : ℕ, IsFeatureVector (localGraphVector χ x j)) ∧
        Summable (fun j : ℕ => featureNorm (localGraphVector χ x j))

/-- Claim 21864: the two radial saddle inequalities used by the joint bound. -/
def claim21864_radialSaddleInequality : Prop :=
  (∀ (r x : ℝ) (z : ℂ), 0 ≤ r → 0 ≤ x →
    -r ^ 2 / 2 + 4 * Real.rpow x (1 / 4 : ℝ) *
        Real.sqrt (r * ‖z‖) ≤
      -r ^ 2 / 4 + 3 * Real.rpow 4 (1 / 3 : ℝ) *
        Real.rpow x (1 / 3 : ℝ) * Real.rpow ‖z‖ (2 / 3 : ℝ)) ∧
  (∀ (r x θ : ℝ), 0 ≤ r → 0 ≤ x →
    -r ^ 2 - x + 2 * Real.sqrt x * r * Real.cos θ ≤
      -r ^ 2 / 2 + x)

abbrev PositiveReal := {u : ℝ // 0 < u}

/-- Claim 22420: the exact ratio of the two adjacent moving anchors. -/
def claim22420_adjacentAnchorRatioIdentity : Prop :=
  let t : ℝ := 551 / 5000
  let y : ℝ := 7 / 50
  let u0 : ℝ := 690988 ^ 2 - t / 16
  let u1 : ℝ := 690989 ^ 2 - t / 16
  ∀ c₂ : ℂ, c₂ ≠ 0 →
    ∃ U₀ U₁ : PositiveReal,
      (U₀ : ℝ) = u0 ∧ (U₁ : ℝ) = u1 ∧
        MathlibPlus.Analysis.Claim22419.T₂ t y U₁ c₂ /
            MathlibPlus.Analysis.Claim22419.T₂ t y U₀ c₂ =
          Complex.exp
            (((-(t / 4) * Real.log (u1 / u0) * Real.log 2 : ℝ) : ℂ) +
              2 * Real.pi * Complex.I * ((u1 - u0 : ℝ) : ℂ) *
                (Real.log 2 : ℂ))

end

end MathlibPlus.Open.ResearchFormalization.R0474R0538
