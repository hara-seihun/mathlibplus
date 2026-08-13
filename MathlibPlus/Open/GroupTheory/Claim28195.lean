import Mathlib

namespace MathlibPlus.Open.GroupTheory

/-- Claim 28195: the automorphism group of `C₂³ × C₃²` splits into the
corresponding general-linear factors.  The cyclic factors are represented by
finite-dimensional vector spaces over their prime fields. -/
def automorphismGroupC2CubeC3Square : Prop :=
  Nonempty (
    Multiplicative (AddAut ((Fin 3 → ZMod 2) × (Fin 2 → ZMod 3))) ≃*
      (LinearMap.GeneralLinearGroup (ZMod 2) (Fin 3 → ZMod 2) ×
        LinearMap.GeneralLinearGroup (ZMod 3) (Fin 2 → ZMod 3)))

end MathlibPlus.Open.GroupTheory
