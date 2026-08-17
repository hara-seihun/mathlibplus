import MathlibPlus.Open.Analysis.PositiveAxisPoissonBessel

open scoped BigOperators
open MeasureTheory Set Filter Topology

namespace MathlibPlus.Open.Analysis

noncomputable section

open MathlibPlus.Open.Analysis.PositiveAxisPoissonBessel

/-- The normalized signal used by the admitted critical Poisson--Bessel channel. -/
def vonMangoldtRecoveryNormalizedSignal (u : ℝ) : ℝ :=
  (phi u + 1) / Real.sqrt u

/-- The phase-matched macroscopic Fourier transform of that literal signal. -/
def vonMangoldtRecoveryTransform (φ : ℝ → ℝ) (q : ℕ) (U : ℝ) : ℂ :=
  ((1 / U : ℝ) : ℂ) *
    ∫ u in Set.Ioi (0 : ℝ),
      ((φ (u / U) : ℝ) : ℂ) *
          (vonMangoldtRecoveryNormalizedSignal u : ℂ) *
        Complex.exp
          (-Complex.I *
            ((2 : ℂ) * (u : ℂ) *
                (Real.sqrt (Real.log (q : ℝ)) : ℂ) -
              (3 : ℂ) * (Real.pi : ℂ) / 4))

/-- The scalar map from an extracted limit amplitude to its recovered
von Mangoldt coefficient. -/
def vonMangoldtRecoveredCoefficientMap (q : ℕ) : ℂ → ℂ :=
  fun L =>
    (2 : ℂ) * (Real.sqrt Real.pi : ℂ) * (q : ℂ) *
      (Real.rpow (Real.log (q : ℝ)) (3 / 4 : ℝ) : ℂ) * L

/-- A candidate literal coefficient family is compatible with the recovered
transform when it has exactly the recovered value at every q-frequency. -/
def vonMangoldtRecoveryCompatible (φ : ℝ → ℝ)
    (a : {q : ℕ // 2 ≤ q} → ℝ) : Prop :=
  ∀ q : {q : ℕ // 2 ≤ q},
    ∃ L : ℂ,
      Filter.Tendsto (vonMangoldtRecoveryTransform φ q.1) Filter.atTop (𝓝 L) ∧
        Complex.ofReal (a q) = vonMangoldtRecoveredCoefficientMap q.1 L

/-- Exact recovery of every literal von Mangoldt value from the normalized
signal, including injectivity on the literal coefficient data and the zero
amplitude at non-prime-power frequencies. -/
def exactVonMangoldtRecovery : Prop :=
  ∀ (φ : ℝ → ℝ),
    ContDiff ℝ ⊤ φ ∧
        HasCompactSupport φ ∧
          tsupport φ ⊆ Set.Ioo (1 : ℝ) 2 ∧
            (∫ u : ℝ, φ u) = 1 →
      (∀ (q : ℕ),
        2 ≤ q →
          ∃ L : ℂ,
            Filter.Tendsto (vonMangoldtRecoveryTransform φ q) Filter.atTop (𝓝 L) ∧
              Complex.ofReal (ArithmeticFunction.vonMangoldt q) =
                vonMangoldtRecoveredCoefficientMap q L ∧
              ((∀ p k : ℕ,
                  ¬ (Nat.Prime p ∧ 1 ≤ k ∧ q = p ^ k)) →
                L = 0)) ∧
      (∀ a b : {q : ℕ // 2 ≤ q} → ℝ,
        vonMangoldtRecoveryCompatible φ a →
          vonMangoldtRecoveryCompatible φ b →
            a = b)

end

end MathlibPlus.Open.Analysis
