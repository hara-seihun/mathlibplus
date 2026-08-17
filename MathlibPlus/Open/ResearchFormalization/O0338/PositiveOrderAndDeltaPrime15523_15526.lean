import Mathlib
import MathlibPlus.Open.Analysis.O0338DistributionalEdge

open Asymptotics Filter Set TopologicalSpace Distribution
open scoped BigOperators Distributions Topology

namespace MathlibPlus.Open.ResearchFormalization.O0338

noncomputable section

open MathlibPlus.Open.Analysis.O0338

abbrev RealDistribution :=
  𝓓'((⊤ : TopologicalSpace.Opens ℝ), ℝ)

/-- The actual `k`-th distributional derivative of the Dirac mass at `t`,
with `δ_t'` acting by `-φ'(t)`. -/
noncomputable def deltaDerivative (t : ℝ) : ℕ → RealDistribution
  | 0 => Distribution.delta (Ω := (⊤ : TopologicalSpace.Opens ℝ))
      (n := ⊤) t
  | k + 1 =>
      Distribution.lineDerivCLM (Ω := (⊤ : TopologicalSpace.Opens ℝ))
        (k := ⊤) (n := ⊤) (1 : ℝ) (deltaDerivative t k)

/-- The exact principal Cauchy term of a delta derivative after translating
an active support edge to zero. -/
noncomputable def edgePrincipalPart
    (c : ℝ) (k : ℕ) (lower : Fin k → ℝ) (z : ℂ) : ℂ :=
  (c : ℂ) * (Nat.factorial k : ℂ) / z ^ (k + 1) +
    ∑ j : Fin k,
      (lower j : ℂ) * (Nat.factorial j.1 : ℂ) / z ^ (j.1 + 1)

/-- A genuine local jet of the actual compact distribution at its lower
support endpoint.  The residual distribution is separated by a positive
support gap, so the displayed positive-order term cannot be an arbitrary
callback or a pointwise surrogate. -/
def HasActivePositiveOrderEdgeJet
    (T : RealDistribution) (a c : ℝ) (k : ℕ) (lower : Fin k → ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧
    ∃ R : RealDistribution,
      IsCompact (Distribution.dsupport R) ∧
        Distribution.dsupport R ⊆ Set.Ici (a + δ) ∧
          T = c • deltaDerivative a k +
            (∑ j : Fin k, (lower j) • deltaDerivative a j.1) + R

/-- The actual shifted-zeta logarithm on the right half-plane, paired with
compactly supported test functions and required to be holomorphic there. -/
def IsActualShiftedZetaLog
    (T : RealDistribution) (a : ℝ) (logZeta L : ℂ → ℂ) : Prop :=
  ZetaLogBranch logZeta ∧
    AnalyticOnNhd ℂ L {s : ℂ | 1 - a < s.re} ∧
      (∀ s : ℂ, 1 - a < s.re →
        DistributionalPairing T
          (fun α : ℝ => logZeta (s + (α : ℂ))) (L s))

/-- The actual exponential of the shifted-zeta logarithm on its germ domain. -/
noncomputable def shiftedZetaExponential (L : ℂ → ℂ) (s : ℂ) : ℂ :=
  Complex.exp (L s)

/-- The logarithmic derivative of that actual exponential in the translated
edge coordinate. -/
noncomputable def shiftedEdgeLogDerivative
    (a : ℝ) (L : ℂ → ℂ) (z : ℂ) : ℂ :=
  -deriv (fun w : ℂ =>
      shiftedZetaExponential L ((1 - a : ℝ) + w)) z /
    shiftedZetaExponential L ((1 - a : ℝ) + z)

/-- A single-valued nonzero meromorphic continuation of the actual
right-half-plane shifted-zeta germ. -/
def HasNonzeroMeromorphicContinuation
    (a : ℝ) (L : ℂ → ℂ) : Prop :=
  ∃ r : ℝ, 0 < r ∧
    ∃ M : ℂ → ℂ,
      MeromorphicOn M (Metric.ball ((1 - a : ℝ) : ℂ) r) ∧
        (∃ w : ℂ,
          w ∈ Metric.ball ((1 - a : ℝ) : ℂ) r ∧ M w ≠ 0) ∧
          (∀ s : ℂ,
            s ∈ Metric.ball ((1 - a : ℝ) : ℂ) r →
              1 - a < s.re → M s = shiftedZetaExponential L s)

/-- Claim 15523: for an actual compactly supported shifted-zeta
 distribution, a nonzero positive-order derivative in the active lower-edge
jet yields the exact higher-order Cauchy pole in its logarithmic derivative,
so the actual exponential has no nonzero single-valued meromorphic edge
germ. -/
def claim15523_positiveOrderEdgeDerivative : Prop :=
  ∀ (T : RealDistribution) (a : ℝ) (logZeta L : ℂ → ℂ)
    (c : ℝ) (k : ℕ) (lower : Fin k → ℝ),
    T ≠ 0 →
      IsCompact (Distribution.dsupport T) →
        IsLeast (Distribution.dsupport T) a →
          IsActualShiftedZetaLog T a logZeta L →
            c ≠ 0 →
              1 ≤ k →
                HasActivePositiveOrderEdgeJet T a c k lower →
                  ∃ r : ℝ, 0 < r ∧
                    ∃ H : ℂ → ℂ,
                      AnalyticOnNhd ℂ H (Metric.ball (0 : ℂ) r) ∧
                        (∀ z : ℂ,
                          z ∈ Metric.ball (0 : ℂ) r →
                            0 < z.re →
                              shiftedEdgeLogDerivative a L z =
                                edgePrincipalPart c k lower z + H z) ∧
                        meromorphicOrderAt
                            (fun z : ℂ => edgePrincipalPart c k lower z + H z)
                            (0 : ℂ) =
                          (-(k + 1 : ℤ) : WithTop ℤ) ∧
                        ¬ HasNonzeroMeromorphicContinuation a L

/-- The concrete delta-prime witness at the lower edge zero. -/
noncomputable def deltaPrime : RealDistribution :=
  deltaDerivative 0 1

/-- The explicit action convention for the actual delta-prime distribution. -/
def IsDeltaPrimeDistribution : Prop :=
  ∀ φ : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ),
    deltaPrime φ =
      -((TestFunction.lineDerivCLM ℝ (n := ⊤) (k := ⊤)
        (1 : ℝ) φ) (0 : ℝ))

/-- The value of the actual delta-prime shift paired with a specified
holomorphic branch of `log ζ`. -/
noncomputable def deltaPrimeShiftLog
    (logZeta : ℂ → ℂ) (s : ℂ) : ℂ :=
  -deriv (fun α : ℝ => logZeta (s + (α : ℂ))) 0

/-- The distributional pairing assertion for the delta-prime shift. -/
def IsDeltaPrimeShiftPairing
    (logZeta : ℂ → ℂ) (s : ℂ) : Prop :=
  DistributionalPairing deltaPrime
    (fun α : ℝ => logZeta (s + (α : ℂ)))
    (deltaPrimeShiftLog logZeta s)

/-- The exact positive-integer inverse-power term in the von Mangoldt
Dirichlet series. -/
noncomputable def naturalComplexInversePower (n : ℕ) (s : ℂ) : ℂ :=
  Complex.exp (-s * (Real.log (n : ℝ) : ℂ))

/-- The `n ≥ 2` von Mangoldt series for the delta-prime logarithm. -/
noncomputable def vonMangoldtDirichletSeries (s : ℂ) : ℂ :=
  ∑' n : {n : ℕ // 2 ≤ n},
    (ArithmeticFunction.vonMangoldt n.1 : ℂ) *
      naturalComplexInversePower n.1 s

/-- Absolute ordinary Dirichlet expansion with real nonnegative
coefficients, including the exact prime coefficient. -/
def HasNonnegativeOrdinaryDirichletExpansion
    (F : ℂ → ℂ) : Prop :=
  ∃ a : ℕ+ → ℝ,
    (∀ s : ℂ, 1 < s.re →
      Summable (fun n : ℕ+ =>
        ‖(a n : ℂ) * naturalComplexInversePower n.1 s‖) ∧
        F s = ∑' n : ℕ+,
          (a n : ℂ) * naturalComplexInversePower n.1 s) ∧
      (∀ n : ℕ+, 0 ≤ a n) ∧
      (∀ (p : ℕ) (hp : Nat.Prime p),
        a ⟨p, Nat.Prime.pos hp⟩ = Real.log (p : ℝ) ∧
          0 < Real.log (p : ℝ))

/-- The pole expansion `L_T(s)=1/(s-1)+O(1)` on the right-half-plane
germ. -/
def HasRightEdgePoleExpansion (F : ℂ → ℂ) : Prop :=
  IsBigO (nhdsWithin (1 : ℂ) {s : ℂ | 1 < s.re})
    (fun s : ℂ => F s - (s - 1)⁻¹)
    (fun _ : ℂ => (1 : ℂ))

/-- Nonexistence of a nonzero single-valued meromorphic continuation of a
right-half-plane germ at `s=1`. -/
def HasNoNonzeroMeromorphicContinuationAtOne (F : ℂ → ℂ) : Prop :=
  ¬ ∃ r : ℝ, 0 < r ∧
    ∃ M : ℂ → ℂ,
      MeromorphicOn M (Metric.ball (1 : ℂ) r) ∧
        (∃ w : ℂ, w ∈ Metric.ball (1 : ℂ) r ∧ M w ≠ 0) ∧
          (∀ s : ℂ,
            s ∈ Metric.ball (1 : ℂ) r → 1 < s.re → M s = F s)

/-- The actual delta-prime shifted-zeta exponential. -/
noncomputable def deltaPrimeShiftExponential
    (logZeta : ℂ → ℂ) (s : ℂ) : ℂ :=
  Complex.exp (deltaPrimeShiftLog logZeta s)

/-- Claim 15526: for a holomorphic log-zeta branch normalized on the
positive real axis, the actual `δ₀'` pairing is `-ζ'/ζ`, its exponent is the
`n ≥ 2` von Mangoldt series, the exponential has an absolutely convergent
ordinary Dirichlet series with nonnegative coefficients and prime coefficient
`log p`, and its edge behavior is essential/nonmeromorphic. -/
def claim15526_deltaPrimeEssentialSingularity : Prop :=
  ∃ logZeta : ℂ → ℂ,
    ZetaLogBranch logZeta ∧
      IsDeltaPrimeDistribution ∧
      (∀ s : ℂ, 1 < s.re →
        IsDeltaPrimeShiftPairing logZeta s ∧
          deltaPrimeShiftLog logZeta s =
            -deriv riemannZeta s / riemannZeta s ∧
          deltaPrimeShiftLog logZeta s = vonMangoldtDirichletSeries s) ∧
      HasNonnegativeOrdinaryDirichletExpansion
        (deltaPrimeShiftExponential logZeta) ∧
      HasRightEdgePoleExpansion (deltaPrimeShiftLog logZeta) ∧
      HasNoNonzeroMeromorphicContinuationAtOne
        (deltaPrimeShiftExponential logZeta)

end

end MathlibPlus.Open.ResearchFormalization.O0338
