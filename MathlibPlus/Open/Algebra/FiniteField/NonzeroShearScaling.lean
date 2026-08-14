import Mathlib

namespace MathlibPlus.Open.Algebra.FiniteField

noncomputable section

private abbrev F := ZMod 3
private abbrev State := F × F × F × F

private def scale : State → State :=
  fun z => (z.1, z.2.1, z.2.2.1, 2 * z.2.2.2)

private def shearOne (q : F → F → F) : State → State :=
  fun z => (z.1 + z.2.2.1 ^ 2,
    z.2.1 + q z.2.2.1 z.2.2.2,
    z.2.2.1 + z.2.2.2,
    z.2.2.2)

private def shearTwo (q : F → F → F) : State → State :=
  fun z => (z.1 + z.2.2.1 ^ 2,
    z.2.1 + q z.2.2.1 z.2.2.2,
    z.2.2.1 + 2 * z.2.2.2,
    z.2.2.2)

/-- Claim 39815: scaling the last coordinate by `2` gives the exact
conjugacy between the two nonzero lower-shear families and transforms the
carry function by `q(v,w) ↦ q(v,2w)`. -/
def claim39815_secondNonzeroShearEquivalentByScaling : Prop :=
  (Function.Bijective scale) ∧
    (∀ (q : F → F → F),
      let q₂ : F → F → F := fun v w => q v (2 * w)
      (∀ (x u v w : F),
        scale (shearOne q (x, u, v, w)) =
          shearTwo q₂ (scale (x, u, v, w))) ∧
      (∀ (v w : F), q₂ v w = q v (2 * w)))

end

end MathlibPlus.Open.Algebra.FiniteField
