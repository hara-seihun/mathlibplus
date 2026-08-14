import Mathlib

open scoped BigOperators
open Set
open MeasureTheory

noncomputable section

namespace MathlibPlus.Open.Analysis

abbrev Prime := {p : ℕ // Nat.Prime p}
abbrev PositiveNat := {k : ℕ // 1 ≤ k}

def primeTowerTerm (p : Prime) (t : ℝ) (k : PositiveNat) : ℂ :=
  ((Real.log (p : ℝ) / Real.rpow (p : ℝ) ((k.1 : ℝ) / 2) : ℝ) : ℂ) *
    Complex.exp (-Complex.I *
      ((k.1 : ℂ) * (t : ℂ) * (Real.log (p : ℝ) : ℂ)))

def primeTower (p : Prime) (t : ℝ) : ℂ :=
  ∑' k : PositiveNat, primeTowerTerm p t k

def primeTowerAbsolutelyConvergent (p : Prime) (t : ℝ) : Prop :=
  Summable (fun k : PositiveNat => ‖primeTowerTerm p t k‖)

def primeTowerSum (P : Finset Prime) (t : ℝ) : ℂ :=
  Finset.sum P (fun p => primeTower p t)

def primeTowerM (P : Finset Prime) : ℝ :=
  Finset.sum P (fun p => Real.log (p : ℝ) / (Real.sqrt (p : ℝ) - 1))

def primeTowerL (P : Finset Prime) : ℝ :=
  Finset.sum P (fun p => (Real.log (p : ℝ)) ^ 3 / ((p : ℝ) - 1) ^ 2)

def primeTowerLevelSet (P : Finset Prime) (β : ℝ) : Set ℝ :=
  {t | 0 ≤ t ∧ β ≤ (primeTowerSum P t).re}

def primeTowerMixedMoment (P : Finset Prime) : Prop :=
  Filter.Tendsto
    (fun T : ℝ =>
      (1 / T : ℂ) *
        ∫ t in (0 : ℝ)..T,
          (primeTowerSum P t) ^ 2 * star (primeTowerSum P t))
    Filter.atTop (nhds (primeTowerL P : ℂ))

def primeTowerThirdMomentCollision : Prop :=
  ∀ (P : Finset Prime),
    P.Nonempty →
      (∀ p ∈ P, ∀ t : ℝ, primeTowerAbsolutelyConvergent p t) ∧
      primeTowerMixedMoment P ∧
      ∀ β : ℝ,
        0 ≤ β →
        β < primeTowerL P / (primeTowerM P) ^ 2 →
          Filter.liminf
              (fun T : ℝ =>
                (volume (primeTowerLevelSet P β ∩ Set.Icc (0 : ℝ) T)).toReal / T)
              Filter.atTop ≥
              (primeTowerL P - β * (primeTowerM P) ^ 2) /
                ((primeTowerM P) ^ 3 - β * (primeTowerM P) ^ 2) ∧
            0 <
              (primeTowerL P - β * (primeTowerM P) ^ 2) /
                ((primeTowerM P) ^ 3 - β * (primeTowerM P) ^ 2)

end MathlibPlus.Open.Analysis
