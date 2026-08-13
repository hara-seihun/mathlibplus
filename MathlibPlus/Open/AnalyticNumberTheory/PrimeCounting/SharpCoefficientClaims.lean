import Mathlib

/-!
# Sharp prime-counting coefficient records

Statement-fidelity registry nodes for the admitted sharp-coefficient and
normalization claims around the two finite prime-counting ranges.  Real
`π(x)` is represented by `(Nat.primeCounting ⌊x⌋₊ : ℝ)`, the convention used
by the neighboring prime-counting registry nodes.  Ellipsized decimal displays
are retained as half-open rational enclosures rather than as informal syntax.
-/

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

noncomputable section

/-- Claim 820: the exact sharp coefficient at `1526671`, with the displayed
long decimal represented by its prefix interval and the three useful decimal
bounds. -/
def exactCoefficientAndNumericalEnclosure_claim820 : Prop :=
  let aStar : ℝ :=
    Real.log (1526671 : ℝ) - (1526671 : ℝ) / 116053
  let displayedLower : ℝ :=
    (10836536589641492328911007601835673174480798422918 : ℝ) /
      10 ^ (49 : ℕ)
  let displayedUpper : ℝ :=
    (10836536589641492328911007601835673174480798422919 : ℝ) /
      10 ^ (49 : ℕ)
  displayedLower ≤ aStar ∧
    aStar < displayedUpper ∧
    (1083 : ℝ) / 1000 < aStar ∧
    aStar < (108365366 : ℝ) / 100000000 ∧
    (108365366 : ℝ) / 100000000 < (108366 : ℝ) / 100000

/-- Claim 821: the finite-range score has its unique maximum at the left
endpoint, and the prime endpoints have their unique maximum at `1526687`.
The displayed positive gap is represented by its 34-place prefix interval. -/
def uniqueFiniteRangeMaximizer_claim821 : Prop :=
  let primeCount : ℝ → ℝ := fun x =>
    (Nat.primeCounting ⌊x⌋₊ : ℝ)
  let score : ℝ → ℝ := fun x =>
    Real.log x - x / primeCount x
  let aStar : ℝ :=
    Real.log (1526671 : ℝ) - (1526671 : ℝ) / 116053
  let gapLower : ℝ :=
    (140346469405653426219392640554 : ℝ) /
      10 ^ (34 : ℕ)
  let gapUpper : ℝ :=
    (140346469405653426219392640555 : ℝ) /
      10 ^ (34 : ℕ)
  (∀ x : ℝ, (1526671 : ℝ) ≤ x → x ≤ (1529630 : ℝ) →
    score x ≤ aStar ∧ (score x = aStar ↔ x = (1526671 : ℝ))) ∧
    (Finset.filter Nat.Prime (Finset.Ioc 1526671 1529630)).card = 202 ∧
    Nat.Prime 1526687 ∧
    (∀ p : ℕ, 1526671 < p → p ≤ 1529630 → Nat.Prime p →
      score (p : ℝ) ≤ score (1526687 : ℝ) ∧
        (score (p : ℝ) = score (1526687 : ℝ) ↔ p = 1526687)) ∧
    gapLower < aStar - score (1526687 : ℝ) ∧
    aStar - score (1526687 : ℝ) < gapUpper

/-- Claim 823: the sharp non-strict bound on the full real half-line and its
unique equality point. -/
def globalSharpNonStrictBound_claim823 : Prop :=
  let primeCount : ℝ → ℝ := fun x =>
    (Nat.primeCounting ⌊x⌋₊ : ℝ)
  let aStar : ℝ :=
    Real.log (1526671 : ℝ) - (1526671 : ℝ) / 116053
  ∀ x : ℝ, (1526671 : ℝ) ≤ x →
    primeCount x ≤ x / (Real.log x - aStar) ∧
      (primeCount x = x / (Real.log x - aStar) ↔
        x = (1526671 : ℝ))

/-- Claim 824: exact classification of strict coefficients below the start's
logarithm. -/
def strictCoefficientClassification_claim824 : Prop :=
  let primeCount : ℝ → ℝ := fun x =>
    (Nat.primeCounting ⌊x⌋₊ : ℝ)
  let aStar : ℝ :=
    Real.log (1526671 : ℝ) - (1526671 : ℝ) / 116053
  ∀ a : ℝ, a < Real.log (1526671 : ℝ) →
    ((∀ x : ℝ, (1526671 : ℝ) ≤ x →
        primeCount x < x / (Real.log x - a)) ↔ aStar < a)

/-- Claim 825: the improved eight-decimal strict coefficient on the same
half-line. -/
def improvedEightDecimalCoefficient_claim825 : Prop :=
  let primeCount : ℝ → ℝ := fun x =>
    (Nat.primeCounting ⌊x⌋₊ : ℝ)
  ∀ x : ℝ, (1526671 : ℝ) ≤ x →
    primeCount x < x /
      (Real.log x - (108365366 : ℝ) / 100000000)

/-- Claim 826: the first point below the Axler start is a counterexample to the
coefficient `1.08366`. -/
def axlerStartFailure_claim826 : Prop :=
  let primeCount : ℝ → ℝ := fun x =>
    (Nat.primeCounting ⌊x⌋₊ : ℝ)
  let score : ℝ → ℝ := fun x =>
    Real.log x - x / primeCount x
  let x0 : ℝ := 1526670
  let coefficient : ℝ := (108366 : ℝ) / 100000
  score x0 > coefficient ∧
    ¬ (primeCount x0 < x0 / (Real.log x0 - coefficient)) ∧
    ¬ (∀ x : ℝ, 1000000 < x →
      primeCount x < x / (Real.log x - coefficient))

/-- Claim 863: the real prime-counting normalization and the exact algebraic
conversion between the strict denominator bound and the score bound, under the
stated positivity conditions. -/
def primeCountingNormalization_claim863 : Prop :=
  let primeCount : ℝ → ℝ := fun x =>
    (Nat.primeCounting ⌊x⌋₊ : ℝ)
  let score : ℝ → ℝ := fun x =>
    Real.log x - x / primeCount x
  ∀ x a : ℝ, 0 ≤ x → 0 < primeCount x →
    0 < Real.log x - a →
      (primeCount x < x / (Real.log x - a) ↔ score x < a)

/-- Claim 864: the prime `22078033` supplies the counterexample to the
coefficient `1.071` row and therefore refutes its published half-line claim. -/
def axlerCoefficient1071Counterexample_claim864 : Prop :=
  let primeCount : ℝ → ℝ := fun x =>
    (Nat.primeCounting ⌊x⌋₊ : ℝ)
  let score : ℝ → ℝ := fun x =>
    Real.log x - x / primeCount x
  let coefficient : ℝ := (1071 : ℝ) / 1000
  Nat.Prime 22078033 ∧
    Nat.primeCounting 22078033 = 1393895 ∧
    primeCount 22078033 >
      (22078033 : ℝ) / (Real.log 22078033 - coefficient) ∧
    score 22078033 > coefficient ∧
    ¬ (∀ x : ℝ, (22078017 : ℝ) ≤ x →
      primeCount x < x / (Real.log x - coefficient))

/-- Claim 865: between consecutive prime endpoints the prime-counting score is
on a strictly decreasing logarithmic plateau, and the jump at the next prime
has the displayed size; the final clause records the finite candidate reduction.
Prime indices are one-based through `Nat.nth Nat.Prime (n - 1)`. -/
def plateauMonotonicityPrimeEndpointReduction_claim865 : Prop :=
  let primeCount : ℝ → ℝ := fun x =>
    (Nat.primeCounting ⌊x⌋₊ : ℝ)
  let score : ℝ → ℝ := fun x =>
    Real.log x - x / primeCount x
  let primeAtIndex : ℕ → ℝ := fun n =>
    (Nat.nth Nat.Prime (n - 1) : ℝ)
  (∀ n : ℕ, 1 ≤ n → ∀ x : ℝ,
    primeAtIndex n ≤ x → x < primeAtIndex (n + 1) →
      primeCount x = n ∧
        HasDerivAt (fun y : ℝ => Real.log y - y / (n : ℝ))
          (1 / x - 1 / (n : ℝ)) x ∧
        1 / x - 1 / (n : ℝ) < 0) ∧
    (∀ n : ℕ, 1 ≤ n →
      score (primeAtIndex (n + 1)) -
          (Real.log (primeAtIndex (n + 1)) -
            primeAtIndex (n + 1) / (n : ℝ)) =
        primeAtIndex (n + 1) /
          ((n : ℝ) * ((n + 1 : ℕ) : ℝ))) ∧
    (∀ m n : ℕ, 1 ≤ m → m ≤ n → ∀ s : ℝ,
      primeAtIndex m ≤ s → s < primeAtIndex (m + 1) →
      ∃ c : ℝ,
        (c = s ∨
          (∃ k : ℕ, m < k ∧ k ≤ n ∧ c = primeAtIndex k) ∨
          c = primeAtIndex (n + 1)) ∧
        ∀ x : ℝ, s ≤ x →
          x ≤ primeAtIndex (n + 1) → score x ≤ score c)

/-- Claim 866: the corrected range has global score maximum `a*`, attained
exactly at `22078033`; the displayed decimal is retained as a prefix interval. -/
def globalSameRangeOptimum_claim866 : Prop :=
  let primeCount : ℝ → ℝ := fun x =>
    (Nat.primeCounting ⌊x⌋₊ : ℝ)
  let score : ℝ → ℝ := fun x =>
    Real.log x - x / primeCount x
  let aStar : ℝ :=
    Real.log (22078033 : ℝ) - (22078033 : ℝ) / 1393895
  let displayedLower : ℝ :=
    (10710003582657636764570888764805506 : ℝ) /
      10 ^ (34 : ℕ)
  let displayedUpper : ℝ :=
    (10710003582657636764570888764805507 : ℝ) /
      10 ^ (34 : ℕ)
  (∀ x : ℝ, (22078017 : ℝ) ≤ x → score x ≤ aStar) ∧
    (∀ x : ℝ, (22078017 : ℝ) ≤ x →
      (score x = aStar ↔ x = (22078033 : ℝ))) ∧
    displayedLower ≤ aStar ∧ aStar < displayedUpper

/-- Claim 867: exact strict-coefficient classification on the corrected range,
together with the sharp non-strict statement. -/
def sharpCoefficientClassification_claim867 : Prop :=
  let primeCount : ℝ → ℝ := fun x =>
    (Nat.primeCounting ⌊x⌋₊ : ℝ)
  let aStar : ℝ :=
    Real.log (22078033 : ℝ) - (22078033 : ℝ) / 1393895
  (∀ a : ℝ, a < Real.log (22078017 : ℝ) →
    ((∀ x : ℝ, (22078017 : ℝ) ≤ x →
        primeCount x < x / (Real.log x - a)) ↔ aStar < a)) ∧
    (∀ x : ℝ, (22078017 : ℝ) ≤ x →
      primeCount x ≤ x / (Real.log x - aStar) ∧
        (primeCount x = x / (Real.log x - aStar) ↔
          x = (22078033 : ℝ)))

/-- Claim 868: the convenient decimal repair is strictly above the sharp
coefficient and yields a strict bound on the corrected range. -/
def convenientDecimalCoefficientRepair_claim868 : Prop :=
  let primeCount : ℝ → ℝ := fun x =>
    (Nat.primeCounting ⌊x⌋₊ : ℝ)
  let aStar : ℝ :=
    Real.log (22078033 : ℝ) - (22078033 : ℝ) / 1393895
  let coefficient : ℝ := (107100036 : ℝ) / 100000000
  aStar < coefficient ∧
    ∀ x : ℝ, (22078017 : ℝ) ≤ x →
      primeCount x < x / (Real.log x - coefficient)

end

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
