import Mathlib

namespace MathlibPlus.Open.Research.ShearBatch

noncomputable section

abbrev TernaryVector (W : Type*) := W

def oddMapOverTernary {W Q : Type*} [AddGroup W] [AddGroup Q]
    (c : W → Q) : Prop :=
  ∀ w : W, c (-w) = -c w

def ternaryShear {W Q : Type*} [Add Q] (c : W → Q) : W × Q → W × Q
  | (w, z) => (w, z + c w)

def claim_28829 : Prop :=
  ∀ {W Q : Type*}
    [AddCommGroup W] [AddCommGroup Q]
    [Module (ZMod 3) W] [Module (ZMod 3) Q]
    [FiniteDimensional (ZMod 3) W] [FiniteDimensional (ZMod 3) Q]
    (c : W → Q),
    oddMapOverTernary c →
      ∃! f : W × Q → W × Q,
        ∀ w : W, ∀ z : Q, f (w, z) = (w, z + c w)

end
end MathlibPlus.Open.Research.ShearBatch
