import Mathlib

open scoped BigOperators Topology Interval
open BigOperators
open MeasureTheory Filter

namespace MathlibPlus.Open.Research

def positiveRealLaplaceSetup (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Set.Ici 0) ∧
    (∀ u : ℝ, 0 ≤ u → 0 ≤ f u) ∧
    (∀ z : ℂ, 0 < z.re →
      IntegrableOn
        (fun u : ℝ => (f u : ℂ) * Complex.exp (-z * (u : ℂ)))
        (Set.Ici 0)) ∧
    (∀ z : ℂ, 0 < z.re →
      0 ≤ (∫ u in Set.Ici 0, (f u : ℂ) * Complex.exp (-z * (u : ℂ))).re)

def realAxisLaplaceBoundEndpointRigidity : Prop :=
  ∀ f : ℝ → ℝ, positiveRealLaplaceSetup f →
    ((∀ x : ℝ, 0 < x →
        (∫ u in Set.Ici 0, f u * Real.exp (-x * u)) ≤ f 0 / x) ∧
      (f 0 = 0 → ∀ u : ℝ, 0 ≤ u → f u = 0) ∧
      ((∃ u : ℝ, 0 ≤ u ∧ f u ≠ 0) → 0 < f 0))

def endpointCancelingFiniteDifferenceCounterexample : Prop :=
  ∀ h : ℝ, 0 < h →
    let f : ℝ → ℝ := fun u => 1 - Real.exp (-h * u)
    f 0 = 0 ∧
      (∀ u : ℝ, 0 ≤ u → 0 ≤ f u) ∧
      (∀ z : ℂ, 0 < z.re →
        (∫ u in Set.Ici 0, (f u : ℂ) * Complex.exp (-z * (u : ℂ))) =
            1 / z - 1 / (z + h) ∧
          1 / z - 1 / (z + h) = h / (z * (z + h))) ∧
      (∀ x y : ℝ, 0 < x →
        let z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
        (((h : ℂ) / (z * (z + h))).re =
            h * (x * (x + h) - y ^ 2) /
              ((x ^ 2 + y ^ 2) * ((x + h) ^ 2 + y ^ 2))) ∧
          (y ^ 2 > x * (x + h) → (h / (z * (z + h))).re < 0))

def higherDerivativeSignFailure : Prop :=
  ∀ q : ℕ, 1 ≤ q →
    (∀ u : ℝ, 0 ≤ u → 0 ≤ u ^ q) ∧
      (0 : ℝ) ^ q = 0 ∧
      (∀ z : ℂ, 0 < z.re →
        IntegrableOn
            (fun u : ℝ => (u ^ q : ℂ) * Complex.exp (-z * (u : ℂ)))
            (Set.Ici 0) ∧
          (∫ u : ℝ in Set.Ici 0, ((u ^ q : ℝ) : ℂ) * Complex.exp (-z * (u : ℂ))) =
            (Nat.factorial q : ℂ) / z ^ (q + 1)) ∧
      (∃ zpos zneg : ℂ,
        0 < zpos.re ∧ 0 < zneg.re ∧
          0 < ((Nat.factorial q : ℂ) / zpos ^ (q + 1)).re ∧
          ((Nat.factorial q : ℂ) / zneg ^ (q + 1)).re < 0)

end MathlibPlus.Open.Research
