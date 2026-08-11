import Mathlib
open MeasureTheory
noncomputable section
example : Prop :=
  letI : MeasurableSpace Circle := borel Circle
  letI : BorelSpace Circle := ⟨rfl⟩
  let μ : Measure Circle := MeasureTheory.Measure.haar (G := Circle)
  IsProbabilityMeasure μ
