import Mathlib

namespace MathlibPlus.Open.Analysis

/-- The real phase translation orbit from admitted claim 2213. -/
def translationOrbitDense_claim2213 : Prop :=
  DenseRange (fun u : ℝ =>
    ![
      (QuotientAddGroup.mk (Real.pi * u / 3) : AddCircle (2 * Real.pi)),
      (QuotientAddGroup.mk (2 * Real.pi * u * Real.log 3 / Real.log 8) :
        AddCircle (2 * Real.pi)),
      (QuotientAddGroup.mk (2 * Real.pi * u * Real.log 5 / Real.log 8) :
        AddCircle (2 * Real.pi)),
      (QuotientAddGroup.mk (2 * Real.pi * u * Real.log 7 / Real.log 8) :
        AddCircle (2 * Real.pi))
    ])

end MathlibPlus.Open.Analysis
