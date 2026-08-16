import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable section

open MeasureTheory
open scoped BigOperators

noncomputable def baezDuarteMeasure : Measure ℝ :=
  Measure.withDensity (Measure.restrict volume (Set.Ici (1 : ℝ)))
    (fun t => ENNReal.ofReal (t⁻¹ ^ 2))

abbrev baezDuarteH := MeasureTheory.Lp ℝ 2 baezDuarteMeasure

def baezDuarteGamma (n : ℕ+) (t : ℝ) : ℝ :=
  (Int.floor (t / (n : ℝ)) : ℝ) - (Int.floor t : ℝ) / (n : ℝ)

def baezDuarteCoefficient (u : ℝ) (n : ℕ+) : ℝ :=
  (ArithmeticFunction.moebius (n : ℕ) : ℝ) * Real.exp (-((n : ℝ) * u))

def baezDuarteTerm (u : ℝ) (n : ℕ+) : ℝ → ℝ :=
  fun t => baezDuarteCoefficient u n * baezDuarteGamma n t

def baezDuartePoint (u : ℝ) : ℝ → ℝ :=
  fun t => ∑' n : ℕ+, baezDuarteTerm u n t

def baezDuarteLpTerm
    (hγ : ∀ n : ℕ+, MeasureTheory.MemLp (baezDuarteGamma n) 2 baezDuarteMeasure)
    (u : ℝ) (n : ℕ+) : baezDuarteH :=
  baezDuarteCoefficient u n •
    MeasureTheory.MemLp.toLp (baezDuarteGamma n) (hγ n)

def baezDuarteApproximants : Prop :=
  ∃ hγ : ∀ n : ℕ+, MeasureTheory.MemLp (baezDuarteGamma n) 2 baezDuarteMeasure,
    ∀ u : ℝ, 0 < u →
      ∃ hf : MeasureTheory.MemLp (baezDuartePoint u) 2 baezDuarteMeasure,
        Summable (fun n : ℕ+ => baezDuarteLpTerm hγ u n) ∧
          HasSum (fun n : ℕ+ => baezDuarteLpTerm hγ u n)
            (MeasureTheory.MemLp.toLp (baezDuartePoint u) hf)

def baezDuarteHk (k : ℕ+) (x : ℝ) : ℝ :=
  ∑' n : ℕ+,
    (ArithmeticFunction.moebius (n : ℕ) : ℝ) *
      (((k : ℕ) % (n : ℕ)) : ℝ) / (n : ℝ) * x ^ (n : ℕ)

def baezDuarteR (j : ℕ) (x : ℝ) : ℝ :=
  ∑' n : ℕ+,
    if (n : ℕ) ∣ j then
      (ArithmeticFunction.moebius (n : ℕ) : ℝ) * x ^ (n : ℕ)
    else 0

def baezDuarteG (x : ℝ) : ℝ :=
  ∑' n : ℕ+,
    (ArithmeticFunction.moebius (n : ℕ) : ℝ) / (n : ℝ) * x ^ (n : ℕ)

def baezDuarteUnitIntervalFormula : Prop :=
  ∀ u : ℝ, 0 < u →
    ∀ k : ℕ+, ∀ t : ℝ,
      (k : ℝ) ≤ t → t < (k : ℝ) + 1 →
        let x := Real.exp (-u)
        baezDuartePoint u t = -baezDuarteHk k x ∧
          -baezDuarteHk k x =
            (∑ j ∈ Finset.Icc 1 (k : ℕ), baezDuarteR j x) -
              (k : ℝ) * baezDuarteG x

def baezDuarteUniversalContraction : Prop :=
  ∀ u : ℝ, 0 < u →
    ∀ hf : MeasureTheory.MemLp (baezDuartePoint u) 2 baezDuarteMeasure,
      ‖MeasureTheory.MemLp.toLp (baezDuartePoint u) hf‖ ≤ (1 : ℝ)

def baezDuarteFullApproximantNormExceedsOne : Prop :=
  (∃ hf : MeasureTheory.MemLp (baezDuartePoint (1 / 800 : ℝ)) 2 baezDuarteMeasure,
    ‖MeasureTheory.MemLp.toLp (baezDuartePoint (1 / 800 : ℝ)) hf‖ >
      (1.00060 : ℝ)) ∧
    ¬ baezDuarteUniversalContraction

end

end MathlibPlus.Open.Analysis
