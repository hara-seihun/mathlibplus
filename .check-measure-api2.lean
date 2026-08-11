import Mathlib
open MeasureTheory
#check IsProbabilityMeasure
#synth IsProbabilityMeasure (Measure.haar Circle)
#check Circle.instMeasurableSpace
#check Circle.norm
#check Circle.coe
#check Circle.coe_norm
#check Circle.ext
#check Complex.abs.map_mul
#check Measure.map_map
#check MeasureTheory.Measure.map_apply_of_aemeasurable
#check MeasureTheory.Measure.ext_iff
#check MeasureTheory.Measure.withDensity_apply
