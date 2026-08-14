import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch_019ffedb_e193_7d58_8384_b6a13ce76e32

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators Interval

/-- Local energy on the logarithmic block used by the toggle claims. -/
def localEnergy (a : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ x in (a / Real.exp 1)..a, (f x) ^ 2

/-- Applying the commuting finite dilation toggles in a chosen finite order. -/
def toggleList : List ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | [], f => f
  | p :: ps, f => fun x => toggleList ps f x - toggleList ps f (p * x)

/-- A precise first nonzero jet condition at the origin. -/
def firstNonzeroJet (f : ℝ → ℝ) (r : ℕ) : Prop :=
  (∀ k : ℕ, ContDiffAt ℝ k f 0) ∧
  (∀ k < r, iteratedDeriv k f 0 = 0) ∧
  iteratedDeriv r f 0 ≠ 0

/--
Claim 10273: the displayed oscillatory net has the stated explicit moderate
bounds, vanishing test-function pairings, and divergent squared L² mass.
-/
def claim10273 : Prop :=
  (∀ ε : ℝ, 0 < ε → ε ≤ 1 →
    (∀ m : ℕ, ∀ x : ℝ,
      |iteratedDeriv m (fun x : ℝ => Real.rpow ε (-1 / 2) * Real.sin (x / ε)) x| ≤
        Real.rpow ε (-((m : ℝ)) - 1 / 2)) ∧
    (∀ φ : ℝ → ℝ, ContDiff ℝ ⊤ φ → HasCompactSupport φ →
      Function.support φ ⊆ Ioo (0 : ℝ) 1 →
      |∫ x in (0 : ℝ)..1,
        (Real.rpow ε (-1 / 2) * Real.sin (x / ε)) * φ x| ≤
        Real.sqrt ε * (∫ x in (0 : ℝ)..1, |deriv φ x|)) ∧
    (∀ φ : ℝ → ℝ, ContDiff ℝ ⊤ φ → HasCompactSupport φ →
      Function.support φ ⊆ Ioo (0 : ℝ) 1 →
      Tendsto
        (fun ε : ℝ => ∫ x in (0 : ℝ)..1,
          (Real.rpow ε (-1 / 2) * Real.sin (x / ε)) * φ x)
        (nhdsWithin 0 (Ioi 0)) (nhds 0)) ∧
    (∫ x in (0 : ℝ)..1,
      (Real.rpow ε (-1 / 2) * Real.sin (x / ε)) ^ 2 =
      1 / (2 * ε) - (1 / 4) * Real.sin (2 / ε))) ∧
  Tendsto
    (fun ε : ℝ => ∫ x in (0 : ℝ)..1,
      (Real.rpow ε (-1 / 2) * Real.sin (x / ε)) ^ 2)
    (nhdsWithin 0 (Ioi 0)) atTop

/--
Claim 10293: finite dilation toggles multiply the first nonzero jet by the
corresponding product, and the specified four-toggle energy factor is 2304.
-/
def claim10293 : Prop :=
  (∀ (ps : List ℕ) (f : ℝ → ℝ) (r : ℕ),
    ps.Nodup →
    firstNonzeroJet f r →
    iteratedDeriv r (toggleList ps f) 0 =
      ((ps.map (fun p => (1 : ℝ) - (p : ℝ) ^ r)).prod) *
        iteratedDeriv r f 0) ∧
  (∀ f : ℝ → ℝ, firstNonzeroJet f 1 →
    Tendsto
      (fun a : ℝ =>
        localEnergy a (toggleList [2, 3, 5, 7] f) / localEnergy a f)
      (nhdsWithin 0 (Ioi 0)) (nhds 2304)) ∧
  ((([2, 3, 5, 7].map (fun p => (1 : ℝ) - (p : ℝ))).prod) ^ 2 = 2304)

end
end MathlibPlus.Open.ResearchFormalizationBatch_019ffedb_e193_7d58_8384_b6a13ce76e32
