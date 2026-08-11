import Mathlib.NumberTheory.Chebyshev

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeSums

/-!
Claims 767, 770, and 774.  The phrase "same envelope" is anchored to the
preceding source normalization `R = 5.5666305`.  The coefficient-two source estimate and the tail amplitude in claim 770 are
spelled out from the adjacent certified records.  Printed ellipses in claim
774 are represented by adjacent rational truncation bounds.
-/

def previouslyPublishedThetaAmplitude : Prop :=
  let R : ℝ := 55666305 / 10000000
  let envelope : ℝ → ℝ → ℝ := fun A x =>
    A * Real.rpow (Real.log x / R) (3 / 2 : ℝ) *
      Real.exp (-2 * Real.sqrt (Real.log x / R))
  ∀ x : ℝ, 2 ≤ x →
    (Chebyshev.theta x - x) / x ≤ envelope (1210961 / 10000 : ℝ) x

def threeRangePsiEnvelopeReconstruction : Prop :=
  let R : ℝ := 55666305 / 10000000
  let A : ℝ := 121096 / 1000
  let envelope : ℝ → ℝ → ℝ := fun amplitude x =>
    amplitude * Real.rpow (Real.log x / R) (3 / 2 : ℝ) *
      Real.exp (-2 * Real.sqrt (Real.log x / R))
  let Eψ : ℝ → ℝ := fun x => (Chebyshev.psi x - x) / x
  let cStar : ℝ := A / Real.rpow R (3 / 2 : ℝ)
  let dStar : ℝ := 2 / Real.sqrt R
  (∀ x : ℝ, 0 < Real.log x → Real.log x ≤ 2100 →
      |Eψ x| ≤
        2 * Real.rpow (Real.log x) (3 / 2 : ℝ) *
          Real.exp (-0.8476836 * Real.sqrt (Real.log x))) ∧
    cStar - 2 * Real.exp
      ((dStar - 0.8476836) * Real.sqrt 2100) > 7.22 ∧
    (∀ x : ℝ, 2100 < Real.log x → Real.log x ≤ 200000 →
      Eψ x ≤ envelope A x) ∧
    (∀ x : ℝ, 200000 < Real.log x →
      Eψ x ≤ envelope (121036 / 1000 : ℝ) x) ∧
    (121036 / 1000 : ℝ) < A

def alternativeEnvelopeNormalizationCheck : Prop :=
  let R : ℝ := 55666305 / 10000000
  let c : ℝ := (121096 / 1000 : ℝ) / Real.rpow R (3 / 2 : ℝ)
  let d : ℝ := 2 / Real.sqrt R
  (92202183441759598 : ℝ) / 10 ^ 16 < c ∧
    c < (92202183441759599 : ℝ) / 10 ^ 16 ∧
    c < 922022 / 100000 ∧
    (8476836336683192 : ℝ) / 10 ^ 16 < d ∧
    d < (8476836336683193 : ℝ) / 10 ^ 16

end MathlibPlus.Open.AnalyticNumberTheory.PrimeSums
