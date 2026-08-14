import Mathlib

open scoped BigOperators Interval

namespace MathlibPlus
namespace Open
namespace ResearchFormalizationBatch_01a000d8_acb7_756f_b736_0e7d3a7e5309

/-- The natural density of a subset of `ℕ`, with the counting function taken on
initial intervals, is zero. -/
noncomputable def naturalDensityZero (A : Set ℕ) : Prop := by
  classical
  exact
    Filter.Tendsto
      (fun N : ℕ =>
        ((Finset.filter (fun n : ℕ => n ∈ A) (Finset.range N)).card : ℝ) / (N : ℝ))
      Filter.atTop (nhds (0 : ℝ))

/-- The reciprocal mass in the claim, with the harmless index `0` omitted. -/
noncomputable def reciprocalMass (A : Set ℕ) : ENNReal := by
  classical
  exact ∑' n : ℕ, (if n ∈ A then if n = 0 then 0 else (n : ENNReal)⁻¹ else 0)

/-- Claim 3705: reciprocal summability forces natural density zero. -/
noncomputable def claim3705 : Prop :=
  ∀ A : Set ℕ, reciprocalMass A < ⊤ → naturalDensityZero A

/-- The negative part of the real logarithm. -/
noncomputable def logNegative (u : ℝ) : ℝ := max (-Real.log u) 0

/-- The shrinking load `I_T(ρ)` from claim 3712/3721. -/
noncomputable def shrinkingLoad (T : ℝ) (ρ : ℂ) : ℝ :=
  ∫ x in T..(2 * T),
    logNegative ‖(1 : ℂ) - (x : ℂ) ^ 2 / ρ ^ 2‖

/-- Claim 3721: the one-zero shrinking load has an absolute linear bound. -/
noncomputable def claim3721 : Prop :=
  ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ T : ℝ, 0 < T → ∀ ρ : ℂ, ρ ≠ 0 → shrinkingLoad T ρ ≤ C₀ * T

/-- Claim 3714, with the asymptotic `-O(T log² T)` expanded as one
constant lower bound on the stated range. -/
noncomputable def claim3714 : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ T : ℝ, 3 ≤ T →
      -C * T * (Real.log T) ^ 2 ≤
        ∫ t in T..(2 * T),
          Real.log ‖riemannZeta ((1 / 2 : ℂ) + Complex.I * (t : ℂ))‖

end ResearchFormalizationBatch_01a000d8_acb7_756f_b736_0e7d3a7e5309
end Open
end MathlibPlus
