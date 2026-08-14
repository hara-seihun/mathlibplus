import Mathlib

namespace MathlibPlus.Open.Research.Batch1457

abbrev C7 := ZMod 7

def pointwiseOneSet (multiplier : C7 → ZMod 7) : Set C7 :=
  {h | multiplier h = 1}

def leftPeriodSet (multiplier : C7 → ZMod 7) : Set C7 :=
  {q | ∀ h : C7, multiplier (q + h) = multiplier h}

/-- The explicit additive C₇ form of the pointwise-one counterfeit: the group
identity is 0, and the two scalar values 1 and 2 are nonzero in 𝔽₇. -/
def pointwiseOneCounterfeit : Prop :=
  ∃ (multiplier : C7 → ZMod 7) (a : C7),
    a ≠ 0 ∧
    (∀ h : C7, multiplier h ≠ 0) ∧
    multiplier 0 = 1 ∧
    multiplier a = 1 ∧
    (∀ h : C7, h ≠ 0 → h ≠ a → multiplier h = 2) ∧
    pointwiseOneSet multiplier = ({0, a} : Set C7) ∧
    (¬ ∃ H : AddSubgroup C7,
      ∀ h : C7, h ∈ H ↔ h ∈ pointwiseOneSet multiplier) ∧
    leftPeriodSet multiplier = ({0} : Set C7)

end MathlibPlus.Open.Research.Batch1457
