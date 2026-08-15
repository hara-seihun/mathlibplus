import Mathlib

open scoped BigOperators Interval
open Filter MeasureTheory

namespace MathlibPlus.Open.Analysis

/-- Claim 8846: the local arcsine phase and its phase sum. -/
noncomputable def localArcsinePhaseAndPhaseSumClaim : Prop :=
  ∀ (a : ℕ → ℝ),
    (∀ j, 0 < a j) →
    (∀ᶠ n in (atTop : Filter ℕ),
      ∀ ⦃j k : ℕ⦄, n ≤ j → j < k → a k < a j) →
    Tendsto a atTop (nhds 0) →
    let s : ℕ → ℝ := fun j => (2 * a j)⁻¹
    let M : ℝ → ℕ := fun T => Set.ncard {j : ℕ | 1 ≤ j ∧ s j ≤ T}
    let μ : Measure ℝ := Measure.map s (Measure.count.restrict (Set.Ici 1))
    let F : ℝ → ℝ := fun u =>
      (Real.pi)⁻¹ * Real.arccos u *
        Set.indicator (Set.Icc (0 : ℝ) 1) (fun _ => (1 : ℝ)) u
    let Φ : ℝ → ℝ := fun T =>
      ∑' j : ℕ, if 1 ≤ j then F (s j / T) else 0
    ∀ T : ℝ, 0 < T →
      Φ T = ∫ x in Set.Ioc (0 : ℝ) T, F (x / T) ∂μ

/-- Claim 9347: the fixed-direction radial limit. -/
noncomputable def fixedDirectionRadialLimitClaim : Prop :=
  let Φ : ℝ → ℝ := fun t =>
    ∫ r in Set.Ioc t (Real.exp 2 * t),
      Real.rpow r (1 / 2 : ℝ) * Real.exp (-r)
  let δ : ℕ → ℝ := fun q =>
    (riemannZeta (2 : ℂ)).re⁻¹ *
      (∏ p ∈ Nat.primeFactors q, (p : ℝ) / ((p : ℝ) + 1))
  let S : ℕ → ℝ → ℝ := fun q c =>
    ∑' d : ℕ,
      if 0 < d ∧ Nat.Coprime d q then
        (((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2) *
          (d : ℝ)⁻¹ * Φ (c / (d : ℝ) ^ 2)
      else 0
  (∀ q : ℕ, 0 < q →
    Asymptotics.IsBigO atTop
      (fun c : ℝ => S q c - δ q * Real.Gamma (3 / 2 : ℝ))
      (fun c : ℝ => Real.rpow c (-1 / 4 : ℝ))) ∧
  (∀ a b : ℕ, 0 < a → 0 < b → Nat.Coprime a b →
    Tendsto
      (fun X : ℝ =>
        S (a * b)
          (X * ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) /
            ((a : ℝ) ^ 2 * (b : ℝ) ^ 2)))
      atTop
      (nhds
        (Real.Gamma (3 / 2 : ℝ) * (riemannZeta (2 : ℂ)).re⁻¹ *
          (∏ p ∈ Nat.primeFactors (a * b),
            (p : ℝ) / ((p : ℝ) + 1)))))

end MathlibPlus.Open.Analysis
