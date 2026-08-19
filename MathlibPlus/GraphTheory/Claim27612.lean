import Mathlib.Data.ZMod.Basic

namespace MathlibPlus.GraphTheory.R0959

/-- Claim 27612: the concrete C2-by-C2 shear has trivial normalized relative
 derivatives but moves a singleton derivative orbit on the nonidentity fibre. -/
def properDisplacementSpanInsufficient_claim27612 : Prop :=
  ∃ f : (ZMod 2 × ZMod 2) ≃+ (ZMod 2 × ZMod 2),
    (∀ v h : ZMod 2, f (v, h) = (v + h, h)) ∧
    f.toEquiv 0 = 0 ∧
    (∀ k x : ZMod 2 × ZMod 2,
      f.toEquiv.symm (f.toEquiv (x + k) - f.toEquiv k) = x) ∧
    ∃ S : Set (ZMod 2 × ZMod 2),
      S = {((0 : ZMod 2), 1)} ∧
      f '' S = {((1 : ZMod 2), 1)} ∧
      f '' S ≠ S

end MathlibPlus.GraphTheory.R0959
