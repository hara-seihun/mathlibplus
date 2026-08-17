import Mathlib


open scoped BigOperators Topology
open Filter Set Topology

namespace MathlibPlus.Open.ResearchFormalization.O0356.Claim15673

noncomputable section

open Classical

abbrev PositiveNat := {n : ℕ // 1 ≤ n}

/-- The pole-removed carrier `P(s)=(s-1)ζ(s)`, with its removable value at
`s=1` filled by `1`. -/
noncomputable def poleRemovedZeta (s : ℂ) : ℂ :=
  if s = 1 then 1 else (s - 1) * riemannZeta s

/-- The exact entire-carrier facts used for the Hadamard construction. -/
def HadamardCarrierSpec : Prop :=
  AnalyticOnNhd ℂ poleRemovedZeta Set.univ ∧
    poleRemovedZeta 1 = 1 ∧
      ∀ s : ℂ, s ≠ 1 →
        poleRemovedZeta s = (s - 1) * riemannZeta s

/-- All zeros of the entire carrier, without a critical-strip restriction; in
particular this index includes the trivial zeros. -/
abbrev HadamardZero := {ρ : ℂ // poleRemovedZeta ρ = 0}

/-- The analytic order predicate for a zero of `P`. -/
def IsAnalyticZeroMultiplicity
    (ρ : HadamardZero) (m : ℕ) : Prop :=
  (∀ j : ℕ, j < m → iteratedDeriv j poleRemovedZeta ρ.1 = 0) ∧
    iteratedDeriv m poleRemovedZeta ρ.1 ≠ 0

/-- Analytic zero multiplicity, defined from the first nonzero derivative. -/
noncomputable def hadamardZeroMultiplicity (ρ : HadamardZero) : ℕ := by
  classical
  exact if h : ∃ m : ℕ, iteratedDeriv m poleRemovedZeta ρ.1 ≠ 0 then
    Nat.find h
  else 0

/-- The analytic multiplicity used in the zero-mode sum is the exact order
of every zero. -/
def HadamardMultiplicitySpec : Prop :=
  ∀ ρ : HadamardZero,
    IsAnalyticZeroMultiplicity ρ (hadamardZeroMultiplicity ρ)

/-- The Cayley coordinate used in the Li-coefficient germ. -/
noncomputable def cayleyCoordinate (w : ℂ) : ℂ :=
  1 / (1 - w)

/-- The zero mode attached to a zero of `P`. -/
noncomputable def cayleyMode (ρ : HadamardZero) : ℂ :=
  1 / (ρ.1 - 1)

/-- A coefficient sequence tied to the local logarithm germ of the exact
pole-removed carrier, rather than an unconstrained sequence. -/
def IsHadamardLiCoefficientSequence (S_f : ℕ → ℂ) : Prop :=
  HadamardCarrierSpec ∧
    HadamardMultiplicitySpec ∧
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        ∃ L : ℂ → ℂ,
          AnalyticOnNhd ℂ L (Metric.ball (0 : ℂ) r) ∧
            L 0 = 0 ∧
              (∀ w : ℂ, w ∈ Metric.ball (0 : ℂ) r →
                Complex.exp (L w) =
                  poleRemovedZeta (cayleyCoordinate w)) ∧
                (∀ w : ℂ, w ∈ Metric.ball (0 : ℂ) r →
                  L w =
                    -∑' n : PositiveNat,
                      S_f n.1 * w ^ n.1 / (n.1 : ℂ))

/-- The exponential Poisson transform of the exact Li coefficient sequence. -/
noncomputable def poissonTransform (S_f : ℕ → ℂ) (z : ℂ) : ℂ :=
  Complex.exp (-z) *
    ∑' n : PositiveNat,
      S_f n.1 * z ^ n.1 / (Nat.factorial n.1 : ℂ)

/-- Local normal convergence of one differentiated zero-mode family. -/
def LocallyNormallyConvergentZeroModes (r : ℕ) : Prop :=
  ∀ K : Set ℂ, IsCompact K →
    Summable (fun ρ : HadamardZero =>
      sSup ((fun z : ℂ =>
        ‖(hadamardZeroMultiplicity ρ : ℂ) *
          cayleyMode ρ ^ r * Complex.exp (cayleyMode ρ * z)‖) '' K))

/-- The standard zero-mode estimates used to justify the differentiated sum. -/
def ZeroModeGrowthSpec : Prop :=
  (∃ C R : ℝ,
      0 < C ∧ 0 < R ∧
        ∀ ρ : HadamardZero, R ≤ ‖ρ.1‖ →
          ‖cayleyMode ρ‖ ≤ C / ‖ρ.1‖) ∧
    Summable (fun ρ : HadamardZero =>
      (hadamardZeroMultiplicity ρ : ℝ) *
        (‖ρ.1‖⁻¹ * ‖ρ.1‖⁻¹))

/-- The Riemann-hypothesis branch for nontrivial zeta zeros. -/
def RiemannHypothesis : Prop :=
  ∀ ρ : ℂ,
    riemannZeta ρ = 0 →
      0 < ρ.re → ρ.re < 1 → ρ.re = (1 : ℝ) / 2

/-- Location, simplicity, and lowest-positive-height certification for the
first nontrivial zero. -/
def FirstPositiveNontrivialZero (ρ₁ : ℂ) (γ₁ : ℝ) : Prop :=
  0 < γ₁ ∧
    ρ₁ = ((1 / 2 : ℝ) : ℂ) + (γ₁ : ℂ) * Complex.I ∧
      riemannZeta ρ₁ = 0 ∧
        deriv riemannZeta ρ₁ ≠ 0 ∧
          poleRemovedZeta ρ₁ = 0 ∧
            ∀ ρ : ℂ,
              riemannZeta ρ = 0 →
                0 < ρ.re →
                  ρ.re < 1 →
                    0 < ρ.im → γ₁ ≤ ρ.im

noncomputable def FirstMode (ρ₁ : ℂ) : ℂ :=
  1 / (ρ₁ - 1)

noncomputable def FirstSlope (ρ₁ : ℂ) : ℝ :=
  Complex.normSq (FirstMode ρ₁)

noncomputable def FirstShellIndex (ρ₁ : ℂ) (x : ℝ) : ℕ :=
  Nat.floor (FirstSlope ρ₁ * x)

/-- The Turán/exterior-square quantity formed from the three consecutive
Poisson derivatives. -/
noncomputable def PoissonTuránSquare
    (S_f : ℕ → ℂ) (r : ℕ) (x : ℝ) : ℂ :=
  iteratedDeriv r (fun z : ℂ => poissonTransform S_f z) (x : ℂ) *
      iteratedDeriv (r + 2) (fun z : ℂ => poissonTransform S_f z) (x : ℂ) -
    (iteratedDeriv (r + 1)
      (fun z : ℂ => poissonTransform S_f z) (x : ℂ)) ^ 2

/-- The leading first-conjugate-pair term in the raw exterior square. -/
noncomputable def FirstPairLeading
    (ρ₁ : ℂ) (x : ℝ) : ℂ :=
  let b := FirstMode ρ₁
  let d := FirstSlope ρ₁
  let r := FirstShellIndex ρ₁ x
  (b - starRingEnd ℂ b) ^ 2 * (d : ℂ) ^ r *
    Complex.exp (-(d : ℂ) * (x : ℂ))

/-- Multiplicative `O(exp(-ηx))`, with one global rate and one global
constant. -/
def RelativeExponentialAsymptotic
    (f g : ℝ → ℂ) : Prop :=
  ∃ η C X : ℝ, 0 < η ∧ 0 ≤ C ∧
    ∃ ε : ℝ → ℂ,
      (∀ x : ℝ, X ≤ x →
        f x = g x * (1 + ε x) ∧
          ‖ε x‖ ≤ C * Real.exp (-η * x))

/-- Multiplicative `o(1)` at positive infinity. -/
def MultiplicativeLittleO
    (f g : ℝ → ℂ) : Prop :=
  ∃ ε : ℝ → ℂ,
    Tendsto ε atTop (𝓝 0) ∧
      ∀ x : ℝ, f x = g x * (1 + ε x)

/-- Eventual strict negativity for a complex-valued quantity means that it is
real and has negative real part. -/
def EventuallyStrictlyNegative (f : ℝ → ℂ) : Prop :=
  ∃ X : ℝ, ∀ x : ℝ, X ≤ x → (f x).im = 0 ∧ (f x).re < 0

/-- The factorial-normalized shell used by Claim 15678. -/
noncomputable def NormalizedFirstPair
    (S_f : ℕ → ℂ) (ρ₁ : ℂ) (x : ℝ) : ℂ :=
  let r := FirstShellIndex ρ₁ x
  ((x : ℂ) ^ r / (Nat.factorial r : ℂ)) *
    PoissonTuránSquare S_f r x

/-- The leading normalized conjugate-pair term. -/
noncomputable def NormalizedFirstPairLeading
    (ρ₁ : ℂ) (x : ℝ) : ℂ :=
  (FirstMode ρ₁ - starRingEnd ℂ (FirstMode ρ₁)) ^ 2 /
    (Real.sqrt (2 * Real.pi * FirstSlope ρ₁ * x) : ℂ)

/-- The nonzero constant in the asymptotic magnitude of the normalized
first-pair term. -/
noncomputable def NormalizedFirstPairMagnitudeConstant
    (ρ₁ : ℂ) : ℝ :=
  4 * (FirstMode ρ₁).im ^ 2 /
    Real.sqrt (2 * Real.pi * FirstSlope ρ₁)

end
end MathlibPlus.Open.ResearchFormalization.O0356.Claim15673


open scoped BigOperators Topology

namespace MathlibPlus.Open.ResearchFormalization.O0356.Claim15673

noncomputable section

/-- Claim 15673: the exact exponential Poisson transform has, from derivative
order two onward, the zero-mode formula indexed by every zero of the entire
pole-removed carrier, including the trivial zeros; the sum is locally normally
convergent under the standard genus-one zero estimates. -/
def claim15673_exactPoissonDerivativeZeroMode : Prop :=
  ∀ S_f : ℕ → ℂ,
    IsHadamardLiCoefficientSequence S_f →
      (∀ r : ℕ, 2 ≤ r →
        ∀ x : ℝ,
          iteratedDeriv r
              (fun z : ℂ => poissonTransform S_f z) (x : ℂ) =
            ∑' ρ : HadamardZero,
              (hadamardZeroMultiplicity ρ : ℂ) *
                cayleyMode ρ ^ r *
                Complex.exp (cayleyMode ρ * (x : ℂ))) ∧
        (∀ r : ℕ, 2 ≤ r →
          LocallyNormallyConvergentZeroModes r) ∧
        ZeroModeGrowthSpec

end
end MathlibPlus.Open.ResearchFormalization.O0356.Claim15673
