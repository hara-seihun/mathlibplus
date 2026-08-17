import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationR1100

/-- Claim 28880: the affine image has dimension two, measured from all
translated values `F x - F 0` in the stated ternary cube. -/
def affineImageDimension_claim28880
    (F : (Fin 2 → ZMod 3) → (Fin 3 → ZMod 3)) : Prop :=
  Module.finrank (ZMod 3)
      (Submodule.span (ZMod 3) (Set.range (fun x => F x - F 0))) = 2

end MathlibPlus.Open.ResearchFormalizationR1100
