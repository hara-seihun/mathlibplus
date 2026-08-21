import MathlibPlus.Algebra.PluckerCircuit

namespace MathlibPlus.Algebra

theorem pluckerContext_claim57159 {R : Type*} [CommRing R]
    (C Fa Fb Fc Fd : R) :
    C * ((Fa - Fb) * (Fc - Fd) - (Fa - Fc) * (Fb - Fd) +
        (Fa - Fd) * (Fb - Fc)) = 0 := by
  rw [PluckerCircuit.fourFactorPluckerCircuit]
  simp

end MathlibPlus.Algebra
