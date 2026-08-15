import Mathlib

noncomputable section

open scoped BigOperators
open Set MeasureTheory

namespace MathlibPlus.Open.Analysis.LogKernel

/-- The multiplicative lift on the positive half-line, extended by zero off it. -/
def logarithmicKernelLift (k : ℝ → ℝ) (u : ℝ) : ℝ :=
  if 0 < u then u ^ ((-1 : ℝ) / 2) * k (Real.log u) else 0

/-- The L² norm of a real-valued function on a specified measurable set. -/
def l2NormOn (s : Set ℝ) (f : ℝ → ℝ) : ℝ :=
  (MeasureTheory.eLpNorm f 2 (volume.restrict s)).toReal

/-- The finite weight appearing in the half-line Möbius bound. -/
def halfLineWeightSum (B : ℝ) : ℝ :=
  ∑ n ∈ Finset.filter (fun n => 1 ≤ n) (Finset.range (Nat.floor B + 1)),
    (n : ℝ) ^ ((-1 : ℝ) / 2)

/-- The sampled half-line Möbius inverse. -/
def sampledHalfLineMobius (g : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∑' n : ℕ,
    if 0 < n then
      ((ArithmeticFunction.moebius n : ℤ) : ℝ) * g ((n : ℝ) * u)
    else 0

/-- Claim 2472: logarithmic kernel lift. -/
def logarithmicKernelLiftClaim : Prop :=
  ∀ (A : ℝ) (k : ℝ → ℝ),
    ContDiff ℝ ⊤ k →
    Function.support k ⊆ Ico 0 A →
    let g := logarithmicKernelLift k
    (∀ u, 0 < u → g u = u ^ ((-1 : ℝ) / 2) * k (Real.log u)) ∧
      ContDiffOn ℝ ⊤ g (Ici 1) ∧
      Function.support g ⊆ Ico 1 (Real.exp A)

/-- Claim 2659: endpoint-kernel lift with zero extension. -/
def endpointKernelLiftClaim : Prop :=
  ∀ (A B : ℝ) (k g : ℝ → ℝ),
    1 ≤ A →
    B = Real.exp A →
    ContDiff ℝ ⊤ k →
    HasCompactSupport k →
    Function.support k ⊆ Ico 0 A →
    ∀ u,
      g u = if 1 ≤ u ∧ u < B then
        u ^ ((-1 : ℝ) / 2) * k (Real.log u)
      else 0

/-- Claim 2660: sampled-half-line Möbius inverse and finite support of each sum. -/
def sampledHalfLineMobiusInverseClaim : Prop :=
  ∀ (B : ℝ) (g φ : ℝ → ℝ),
    1 ≤ B →
    (∀ v, B ≤ v → g v = 0) →
    ∀ u, 1 ≤ u →
      φ u = sampledHalfLineMobius g u ∧
        Set.Finite {n : ℕ | 0 < n ∧ g ((n : ℝ) * u) ≠ 0}

/-- The common endpoint-lift hypotheses used by the two quantitative claims. -/
def endpointLiftData (A B : ℝ) (k g φ : ℝ → ℝ) : Prop :=
  1 ≤ A ∧
    B = Real.exp A ∧
    ContDiff ℝ ⊤ k ∧
    HasCompactSupport k ∧
    Function.support k ⊆ Ico 0 A ∧
    (∀ u, g u = if 1 ≤ u ∧ u < B then
      u ^ ((-1 : ℝ) / 2) * k (Real.log u) else 0) ∧
    (∀ u, 1 ≤ u → φ u = sampledHalfLineMobius g u)

/-- Claim 2662: Möbius inverse L² bound. -/
def mobiusInverseL2BoundClaim : Prop :=
  ∀ (A B : ℝ) (k g φ : ℝ → ℝ),
    endpointLiftData A B k g φ →
    l2NormOn (Ici 1) φ ≤
        halfLineWeightSum B * l2NormOn (Ici 1) g ∧
      halfLineWeightSum B * l2NormOn (Ici 1) g ≤
        2 * Real.exp (A / 2) * l2NormOn (Ici 0) k

/-- The finite-in-v integral in the sampled-half-line identity. -/
def mobiusPartialSum (v : ℝ) : ℝ :=
  ∑' n : ℕ,
    if 0 < n ∧ (n : ℝ) ≤ v then
      ((ArithmeticFunction.moebius n : ℤ) : ℝ) / (n : ℝ)
    else 0

/-- Claim 2663: sampled-half-line integral identity and its absolute bound. -/
def sampledHalfLineIntegralIdentityClaim : Prop :=
  ∀ (A B : ℝ) (k g φ : ℝ → ℝ),
    endpointLiftData A B k g φ →
    (∫ u in Ici 1, φ u) =
        ∫ v in Icc 1 B, g v * mobiusPartialSum v ∧
      |∫ u in Ici 1, φ u| ≤
        (1 + A) * Real.exp (A / 2) * l2NormOn (Ici 0) k

end MathlibPlus.Open.Analysis.LogKernel
