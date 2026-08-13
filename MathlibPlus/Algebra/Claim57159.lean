import Mathlib

namespace MathlibPlus.Algebra

theorem pluckerCircuit_claim57159 {R : Type*} [CommRing R]
    (Fa Fb Fc Fd : R) :
    (Fa - Fb) * (Fc - Fd) - (Fa - Fc) * (Fb - Fd) +
        (Fa - Fd) * (Fb - Fc) = 0 := by
  ring

theorem pluckerContext_claim57159 {R : Type*} [CommRing R]
    (C Fa Fb Fc Fd : R) :
    C * ((Fa - Fb) * (Fc - Fd) - (Fa - Fc) * (Fb - Fd) +
        (Fa - Fd) * (Fb - Fc)) = 0 := by
  rw [pluckerCircuit_claim57159]
  simp

end MathlibPlus.Algebra
