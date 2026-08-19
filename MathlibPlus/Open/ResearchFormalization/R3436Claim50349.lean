import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R3436Claim50349

/-- Claim 50349: the balanced four-term defect factors into the two endpoint
secants over every commutative ring. -/
def factorizedDefect_claim50349 : Prop :=
  ∀ (R : Type*) [CommRing R] (H_A H_B H_C H_D : R),
    H_A + H_B = H_C + H_D →
      let D_W := H_A * H_B - H_C * H_D
      D_W = (H_A - H_C) * (H_B - H_C)

end MathlibPlus.Open.ResearchFormalization.R3436Claim50349
