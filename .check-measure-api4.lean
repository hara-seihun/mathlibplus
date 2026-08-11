import Mathlib
open MeasureTheory
#synth IsProbabilityMeasure (MeasureTheory.Measure.haar (G := Circle))
#check Circle
#check Circle.instGroup
#check Circle.instTopologicalSpace
#check Circle.instMeasurableSpace
#check Circle.isTopologicalGroup
#check Circle.instBorelSpace
#check Circle.instLocallyCompactSpace
#check Circle.coe
#check Circle.ext
#check Complex.re
#check Complex.abs
