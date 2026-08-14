import Mathlib

open scoped BigOperators Interval Topology
open MeasureTheory
open Filter

namespace MathlibPlus.Open.ResearchFormalization


/-! Exact elementary carriers used by the admitted geometric-kernel claims. -/

noncomputable def geometricCoefficient (q n : ℕ) : ℝ :=
  if q ∣ n then 1 - (q : ℝ) else 1

noncomputable def geometricPartialSum (q n : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 n, geometricCoefficient q j

noncomputable def geometricSection (q M : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 M,
    (geometricCoefficient q n : ℂ) *
      Complex.exp (-(((1 / 2 : ℂ) + (t : ℂ) * Complex.I) * Complex.log (n : ℂ)))

noncomputable def geometricKernelEnergy (q M : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 M,
    ∑ n ∈ Finset.Icc 1 M,
      geometricCoefficient q m * geometricCoefficient q n / ((max m n : ℕ) : ℝ)

noncomputable def geometricN (q : ℕ) : ℝ :=
  ∑' n : ℕ,
    if 1 ≤ n then
      (((n % q : ℕ) : ℝ) ^ 2) / ((n : ℝ) * ((n + 1 : ℕ) : ℝ))
    else 0

noncomputable def geometricCanceller (q : ℕ) (s : ℂ) : ℂ :=
  if s = 1 then Complex.ofReal (Real.log (q : ℝ))
  else (1 - Complex.exp ((1 - s) * Complex.log (q : ℂ))) * riemannZeta s

noncomputable def geometricBoundary (q : ℕ) (t : ℝ) : ℂ :=
  geometricCanceller q ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)

noncomputable def geometricWeightedEnergy (f : ℝ → ℂ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ∫ t : ℝ, ‖f t‖ ^ 2 / ((1 / 4 : ℝ) + t ^ 2)

noncomputable def geometricWeightedDistance (f g : ℝ → ℂ) : ℝ :=
  Real.sqrt (geometricWeightedEnergy (fun t => f t - g t))

noncomputable def geometricDigammaExpression (q : ℕ) : ℂ :=
  (1 / (q : ℂ)) *
    ∑ r ∈ Finset.Icc 1 (q - 1),
      ((r : ℂ) ^ 2) *
        (Complex.digamma ((((r + 1 : ℕ) : ℝ) / (q : ℝ) : ℂ)) -
          Complex.digamma (((r : ℝ) / (q : ℝ) : ℂ)))

noncomputable def geometricZero (q : ℕ) (k : ℤ) : ℂ :=
  1 + ((2 * Real.pi * (k : ℝ) / Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I

noncomputable def geometricFactor (q : ℕ) (s : ℂ) : ℂ :=
  1 - Complex.exp ((1 - s) * Complex.log (q : ℂ))

noncomputable def geometricRiemannExpression (q : ℕ) : ℝ :=
  (1 / (q : ℝ)) *
    ∑ r ∈ Finset.Icc 1 (q - 1),
      ∑' k : ℕ,
        (((r : ℝ) / (q : ℝ)) ^ 2) /
          (((k : ℝ) + (r : ℝ) / (q : ℝ)) *
            ((k : ℝ) + (r : ℝ) / (q : ℝ) + 1 / (q : ℝ)))

noncomputable def geometricConstant : ℝ :=
  ∑' k : ℕ, ∫ u in (0 : ℝ)..1, u ^ 2 / ((k : ℝ) + u) ^ 2

noncomputable def geometricPartialConstant (K : ℕ) : ℝ :=
  2 + 2 * (K : ℝ) -
      (∑ n ∈ Finset.Icc 1 (K + 1), 1 / (n : ℝ)) -
      2 * (K : ℝ) * Real.log ((K + 1 : ℕ) : ℝ) +
      2 * Real.log (Nat.factorial K : ℝ)

noncomputable def geometricSlack (q : ℕ) : ℝ :=
  (1 / 2 : ℝ) * Real.log
    (((q : ℝ) * geometricN q) / ((q - 1 : ℕ) : ℝ) ^ 2)

/-- Claim 15272: the geometric factor has a removable pole-cancelling value. -/
def claim_15272 : Prop :=
  ∀ q : ℕ, 2 ≤ q →
    let F : ℂ → ℂ := fun s =>
      if s = 1 then Complex.ofReal (Real.log (q : ℝ))
      else (1 - Complex.exp ((1 - s) * Complex.log (q : ℂ))) * riemannZeta s
    DifferentiableAt ℂ F 1 ∧
      F 1 = Complex.ofReal (Real.log (q : ℝ)) ∧
      (∀ s : ℂ, s ≠ 1 →
        F s = (1 - Complex.exp ((1 - s) * Complex.log (q : ℂ))) * riemannZeta s)

/-- Claim 15276: finite max-kernel energy and summation by parts. -/
def claim_15276 : Prop :=
  ∀ q M : ℕ, 2 ≤ q → 1 ≤ M →
    (1 / (2 * Real.pi)) *
        ∫ t : ℝ, ‖geometricSection q M t‖ ^ 2 /
          ((1 / 4 : ℝ) + t ^ 2) = geometricKernelEnergy q M ∧
      geometricKernelEnergy q M =
        geometricPartialSum q M ^ 2 / (M : ℝ) +
          ∑ n ∈ Finset.Icc 1 (M - 1),
            geometricPartialSum q n ^ 2 / ((n : ℝ) * ((n + 1 : ℕ) : ℝ))

/-- Claim 15277: the finite sections are Cauchy in the exact weighted boundary norm. -/
def claim_15277 : Prop :=
  ∀ q : ℕ, 2 ≤ q →
    (∃ C : ℝ, ∀ n : ℕ, |geometricPartialSum q n| ≤ C) ∧
      (∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
          geometricWeightedDistance
              (geometricSection q m) (geometricSection q n) < ε) ∧
      geometricWeightedEnergy (geometricBoundary q) = geometricN q

/-- Claim 15278: the exact digamma expression and the q=2 evaluation. -/
def claim_15278 : Prop :=
  ∀ q : ℕ, 2 ≤ q →
    (geometricN q : ℂ) = geometricDigammaExpression q ∧
      geometricN 2 = Real.log 2

/-- Claim 15279: all non-removable geometric zeros and their complete Jensen sum. -/
def claim_15279 : Prop :=
  ∀ q : ℕ, 2 ≤ q →
    (∀ k : ℤ, k ≠ 0 →
      geometricFactor q (geometricZero q k) = 0 ∧
        (geometricZero q k).re = 1 ∧
        (geometricZero q k).im = 2 * Real.pi * (k : ℝ) / Real.log (q : ℝ)) ∧
      (∀ s : ℂ, (1 / 2 : ℝ) < s.re → geometricFactor q s = 0 → s ≠ 1 →
        ∃ k : ℤ, k ≠ 0 ∧ s = geometricZero q k) ∧
      (∀ k : ℕ, 1 ≤ k →
        2 * Real.log ‖geometricZero q (k : ℤ) /
              (1 - geometricZero q (k : ℤ))‖ =
          Real.log (1 + (Real.log (q : ℝ)) ^ 2 /
            (4 * Real.pi ^ 2 * (k : ℝ) ^ 2))) ∧
      (∑' k : ℕ, Real.log
          (1 + (Real.log (q : ℝ)) ^ 2 /
            (4 * Real.pi ^ 2 * ((k + 1 : ℕ) : ℝ) ^ 2)) =
        Real.log
          (Real.sinh (Real.log (q : ℝ) / 2) /
            (Real.log (q : ℝ) / 2)))

/-- Claim 15283: the Riemann-sum expression and limiting norm constant. -/
def claim_15283 : Prop :=
  (∀ q : ℕ, 2 ≤ q → geometricN q / (q : ℝ) = geometricRiemannExpression q) ∧
    Tendsto (fun q : ℕ => geometricN q / (q : ℝ)) atTop (𝓝 geometricConstant)

/-- Claim 15284: evaluation of the limiting constant. -/
def claim_15284 : Prop :=
  (∀ k : ℕ, 1 ≤ k →
      ∫ u in (0 : ℝ)..1, u ^ 2 / ((k : ℝ) + u) ^ 2 =
        2 - 1 / ((k + 1 : ℕ) : ℝ) -
          2 * (k : ℝ) * Real.log (1 + 1 / (k : ℝ))) ∧
    (∀ K : ℕ,
      geometricPartialConstant K =
        ∑ k ∈ Finset.Icc 0 K,
          ∫ u in (0 : ℝ)..1, u ^ 2 / ((k : ℝ) + u) ^ 2) ∧
    geometricConstant = Real.log (2 * Real.pi) - Real.eulerMascheroniConstant ∧
      1 < geometricConstant

/-- Claim 15285: positive limiting slack and a uniform positive floor. -/
def claim_15285 : Prop :=
  (∀ q : ℕ, 2 ≤ q → 0 < geometricSlack q) ∧
    Tendsto (fun q : ℕ => geometricSlack q) atTop
      (𝓝 ((1 / 2 : ℝ) * Real.log geometricConstant)) ∧
    0 < sInf (Set.range (fun q : {q : ℕ // 2 ≤ q} => geometricSlack q))


end MathlibPlus.Open.ResearchFormalization
