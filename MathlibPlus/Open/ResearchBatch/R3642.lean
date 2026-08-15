import Mathlib

noncomputable section
open MeasureTheory
open scoped BigOperators Interval

namespace MathlibPlus.Open.ResearchBatch.R3642

def thetaShellMeasure (s : ℝ) : MeasureTheory.Measure ℝ :=
  Measure.restrict
    (Measure.withDensity volume (fun u =>
      ENNReal.ofReal (2 * Real.exp (u / 2 - Real.pi * s^2 * Real.exp (2 * u)))))
    (Set.Ici 0)

def thetaShellMoment (s : ℝ) (j : ℕ) : ℝ :=
  (1 / (Nat.factorial (2 * j) : ℝ)) *
    ∫ u, u^(2 * j) ∂(thetaShellMeasure s)

def normalizedThetaShellMomentSequence_claim51116 (s : ℝ) (j : ℕ) : ℝ :=
  1 / (Nat.factorial (2 * j) : ℝ) *
    ∫ u, u^(2 * j) ∂(thetaShellMeasure s)

def periodSixP : Set ℕ :=
  {n | ∃ k : ℕ, n = 6 * k + 3 ∨ n = 6 * k + 4}
def periodSixN : Set ℕ :=
  {n | ∃ k : ℕ, n = 6 * k + 1 ∨ n = 6 * k + 6}

def baselineP : Set ℕ := periodSixP
def baselineN : Set ℕ := periodSixN

def periodSixBaselineSupports_claim51125 : Set ℕ × Set ℕ :=
  (baselineP, baselineN)

def shellPhi (n : ℕ) (u : ℝ) : ℝ :=
  Real.exp (u / 2) *
    (4 * (Real.pi * (n : ℝ)^2 * Real.exp (2 * u))^2 -
      6 * (Real.pi * (n : ℝ)^2 * Real.exp (2 * u))) *
    Real.exp (-(Real.pi * (n : ℝ)^2 * Real.exp (2 * u)))

def finiteShellReflection_claim51130 : Prop :=
  ∀ M : ℕ, ∀ n : Fin M → ℕ, (∀ j, 0 < n j) →
    (Function.Injective n) → ∀ a : Fin M → ℝ,
    (∀ u : ℝ, (∑ j : Fin M, a j * shellPhi (n j) u) =
      ∑ j : Fin M, a j * shellPhi (n j) (-u)) →
    ∀ j : Fin M, a j = 0

end MathlibPlus.Open.ResearchBatch.R3642
