import Mathlib

namespace MathlibPlus.Open.GroupTheory.Claim27714

abbrev BooleanFiberGroup := ZMod 2 × ZMod 2

def normalizedShear (v : BooleanFiberGroup) : BooleanFiberGroup :=
  (v.1 + v.2, v.2)

def normalizedRelativeDerivative (f : BooleanFiberGroup ≃+ BooleanFiberGroup)
    (k : BooleanFiberGroup) : Equiv.Perm BooleanFiberGroup :=
  (((Equiv.addRight k).trans f.toEquiv).trans
      (Equiv.addRight (-(f k)))).trans f.toEquiv.symm

def derivativeOrbit (Delta : Subgroup (Equiv.Perm BooleanFiberGroup))
    (x : BooleanFiberGroup) : Set BooleanFiberGroup :=
  {y | ∃ d : Delta, (d : Equiv.Perm BooleanFiberGroup) x = y}

/-- Claim 27714: the even-order `C₂ × C₂` affine shear is a sharp
counterexample to the odd-order orbit-fixing conclusion, while remaining a
(group) automorphism. -/
def claim27714 : Prop :=
  ∃ f : BooleanFiberGroup ≃+ BooleanFiberGroup,
    (∀ v h : ZMod 2, f (v, h) = (v + h, h)) ∧
      (∀ h : ZMod 2, f (0, h) = (0, h)) ∧
      (∀ h : ZMod 2, f (1, h) = (1 + h, h)) ∧
      f 0 = 0 ∧
      let Delta : Subgroup (Equiv.Perm BooleanFiberGroup) :=
        Subgroup.closure
          (Set.range (normalizedRelativeDerivative f))
      Delta = ⊥ ∧
        derivativeOrbit Delta ((0 : ZMod 2), 1) =
          {((0 : ZMod 2), 1)} ∧
        Set.image f.toEquiv
            (derivativeOrbit Delta ((0 : ZMod 2), 1)) =
          {((1 : ZMod 2), 1)} ∧
        Set.image f.toEquiv
            (derivativeOrbit Delta ((0 : ZMod 2), 1)) ≠
          derivativeOrbit Delta ((0 : ZMod 2), 1)

end MathlibPlus.Open.GroupTheory.Claim27714
