import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatch.R1156Claim41421

abbrev F7_41421 := ZMod 7

/-- The relative derivative of a label at an offset. -/
def relativeDerivative41421
    (δ : F7_41421 → F7_41421) (r : F7_41421) :
    F7_41421 → F7_41421 :=
  fun s => δ (r + s) - δ r

/-- The compatibility predicate for a normalized offset assignment and a
family of labels. -/
def shiftedDerivativeCompatibility_claim41421
    (X : Finset F7_41421) (_hX : 2 ≤ X.card) (_a : X)
    (r : (↥X) → F7_41421) (_hr : r _a = 0)
    (labels : F7_41421 → F7_41421 → F7_41421) : Prop :=
  ∀ (x x' : X) (y : F7_41421),
    relativeDerivative41421 (labels y) (r x) =
      relativeDerivative41421
        (labels (y + (x' : F7_41421) - (x : F7_41421))) (r x')

end MathlibPlus.Open.Research.FormalizationBatch.R1156Claim41421
