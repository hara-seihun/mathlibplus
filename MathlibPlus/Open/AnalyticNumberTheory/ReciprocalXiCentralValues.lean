import Mathlib

/-!
# Certified reciprocal-xi central values

Statement-fidelity formalization of admitted claim 430.  Each printed positive
decimal followed by an ellipsis is represented by the half-open interval from
that decimal prefix to the next value at its final displayed place.
-/

open MeasureTheory

namespace MathlibPlus.Open.AnalyticNumberTheory.ReciprocalXi

/--
The four certified central quantities for the reciprocal Riemann-xi weight,
with every displayed decimal prefix retained as a rigorous enclosure.
-/
noncomputable def certifiedCentralValues : Prop :=
  let xi : ℂ → ℂ := fun s =>
    (1 + s * (s - 1) * completedRiemannZeta₀ s) / 2
  let xiOnCenteredRealAxis : ℝ → ℝ := fun x =>
    (xi ((1 / 2 : ℂ) + (x : ℂ))).re
  let Q : ℝ → ℝ := fun x => Real.log (xiOnCenteredRealAxis x)
  let reciprocalWeight : ℝ → ℝ := fun x => 1 / xiOnCenteredRealAxis x
  let secondMomentIntegrand : ℝ → ℝ := fun x => x ^ 2 / xiOnCenteredRealAxis x
  let C : ℝ := iteratedDeriv 2 Q 0
  let Z : ℝ := ∫ x : ℝ, reciprocalWeight x
  let M₂ : ℝ := ∫ x : ℝ, secondMomentIntegrand x
  let b₁Sq : ℝ := M₂ / Z
  let cPrefix : ℝ := 0.0462099862308379415778676208606780280
  let zPrefix : ℝ := 24.00707225200737367058789336143
  let m₂Prefix : ℝ := 567.9463649789735221913187375
  let b₁SqPrefix : ℝ := 23.657460560668082246008241492
  Integrable reciprocalWeight ∧
    Integrable secondMomentIntegrand ∧
    cPrefix ≤ C ∧ C < cPrefix + 1 / (10 : ℝ) ^ 37 ∧
    zPrefix ≤ Z ∧ Z < zPrefix + 1 / (10 : ℝ) ^ 29 ∧
    m₂Prefix ≤ M₂ ∧ M₂ < m₂Prefix + 1 / (10 : ℝ) ^ 25 ∧
    b₁SqPrefix ≤ b₁Sq ∧ b₁Sq < b₁SqPrefix + 1 / (10 : ℝ) ^ 27

end MathlibPlus.Open.AnalyticNumberTheory.ReciprocalXi
