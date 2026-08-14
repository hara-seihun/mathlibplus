import Mathlib

namespace MathlibPlus.Open.Analysis.FormalizationBatchArcsine

open Filter MeasureTheory Set Topology

noncomputable section

/-- The density appearing in the arcsine law, represented as an `ENNReal` density. -/
def arcsineDensity (y : ℝ) : ENNReal :=
  ENNReal.ofReal (if |y| < 2 then 1 / (Real.pi * Real.sqrt (4 - y ^ 2)) else 0)

/-- The measure with the density stated in the packet. -/
noncomputable def alpha : Measure ℝ :=
  Measure.withDensity volume arcsineDensity

def L (n : ℕ) : ℝ := Real.log ((n : ℝ) + Real.exp 1)

def epsilon (n : ℕ) : ℝ := Real.rpow (L n) (-1 / 2)

/-- The mixture in the slow-convergence construction. -/
noncomputable def sigma (n : ℕ) : Measure ℝ :=
  ENNReal.ofReal (1 - epsilon n) • alpha +
    ENNReal.ofReal (epsilon n) • Measure.dirac (0 : ℝ)

/-- Weak convergence tested against bounded continuous real observables. -/
def weaklyConverges (μ : ℕ → Measure ℝ) (ν : Measure ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, Continuous φ → Bornology.IsBounded (Set.range φ) →
    Tendsto (fun n => ∫ y, φ y ∂(μ n)) atTop
      (𝓝 (∫ y, φ y ∂ν))

/-- Tail uniform integrability for one real-valued observable over a family of measures. -/
def uniformlyIntegrableObservable (f : ℝ → ℝ) (μ : ℕ → Measure ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
    ∀ n : ℕ,
      ∫ y, ({y | R ≤ |f y|}).indicator (fun z => |f z|) y ∂(μ n) < ε

/-- The continuous-extension value at zero of the logarithmic observable. -/
def logObservable (y : ℝ) : ℝ :=
  if y = 0 then 0 else |y| * Real.log (|y| / (2 * Real.pi))

def claim_13619 : Prop :=
  alpha = Measure.withDensity volume arcsineDensity ∧
    (∀ y : ℝ,
      arcsineDensity y = ENNReal.ofReal
        (if |y| < 2 then 1 / (Real.pi * Real.sqrt (4 - y ^ 2)) else 0)) ∧
    IsProbabilityMeasure alpha ∧
    alpha.support ⊆ Set.Icc (-2 : ℝ) 2 ∧
    (∫ y : ℝ, y ^ 2 ∂alpha) = 2 ∧
    (∫ y : ℝ, |y| ∂alpha) = 4 / Real.pi


def claim_13620 : Prop :=
  (∀ n : ℕ,
      L n = Real.log ((n : ℝ) + Real.exp 1) ∧
      epsilon n = Real.rpow (L n) (-1 / 2) ∧
      sigma n = ENNReal.ofReal (1 - epsilon n) • alpha +
        ENNReal.ofReal (epsilon n) • Measure.dirac (0 : ℝ)) ∧
    ∀ n : ℕ,
      IsProbabilityMeasure (sigma n) ∧
        (sigma n).support ⊆ Set.Icc (-2 : ℝ) 2


def claim_13621 : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    (∀ n : ℕ,
      (∫ y : ℝ, y ^ k ∂(sigma n)) =
        (1 - epsilon n) * (∫ y : ℝ, y ^ k ∂alpha)) ∧
    Tendsto (fun n : ℕ => ∫ y : ℝ, y ^ k ∂(sigma n)) atTop
      (𝓝 (∫ y : ℝ, y ^ k ∂alpha))


def claim_13622 : Prop :=
  weaklyConverges sigma alpha ∧
    (∀ n : ℕ, IsProbabilityMeasure (sigma n)) ∧
    (∀ n : ℕ, (sigma n).support ⊆ Set.Icc (-2 : ℝ) 2) ∧
    sSup (Set.range (fun n : ℕ => ∫ y : ℝ, y ^ 2 ∂(sigma n))) ≤ 2 ∧
    uniformlyIntegrableObservable (fun y : ℝ => |y|) sigma ∧
    uniformlyIntegrableObservable logObservable sigma


def claim_13623 : Prop :=
  ∀ n : ℕ,
    (∫ y : ℝ, |y| ∂(sigma n)) = (1 - epsilon n) * (4 / Real.pi)


def claim_13624 : Prop :=
  ∀ n : ℕ,
    (∫ y : ℝ, logObservable y ∂(sigma n)) =
      (1 - epsilon n) * (4 / Real.pi) * (Real.log (2 / Real.pi) - 1)


def claim_13625 : Prop :=
  (∀ n : ℕ,
    L n * ((∫ y : ℝ, |y| ∂(sigma n)) - 4 / Real.pi) =
      -(4 / Real.pi) * Real.sqrt (L n)) ∧
    Tendsto
      (fun n : ℕ => L n * ((∫ y : ℝ, |y| ∂(sigma n)) - 4 / Real.pi))
      atTop atBot


def claim_13626 : Prop :=
  Tendsto L atTop atTop ∧
    weaklyConverges sigma alpha ∧
    (∀ k : ℕ, 1 ≤ k →
      Tendsto (fun n : ℕ => ∫ y : ℝ, y ^ k ∂(sigma n)) atTop
        (𝓝 (∫ y : ℝ, y ^ k ∂alpha))) ∧
    (∀ n : ℕ, (sigma n).support ⊆ Set.Icc (-2 : ℝ) 2) ∧
    sSup (Set.range (fun n : ℕ => ∫ y : ℝ, y ^ 2 ∂(sigma n))) ≤ 2 ∧
    uniformlyIntegrableObservable (fun y : ℝ => |y|) sigma ∧
    uniformlyIntegrableObservable logObservable sigma ∧
    ¬ Tendsto
      (fun n : ℕ => L n * ((∫ y : ℝ, |y| ∂(sigma n)) - 4 / Real.pi))
      atTop (𝓝 0)

end

end MathlibPlus.Open.Analysis.FormalizationBatchArcsine
