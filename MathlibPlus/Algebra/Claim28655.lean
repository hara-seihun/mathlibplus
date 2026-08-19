import Mathlib

namespace MathlibPlus.Algebra.R1077

abbrev K3_28655 := ZMod 3
abbrev W3_28655 := Fin 3 → K3_28655
abbrev V5_28655 := Fin 5 → K3_28655
abbrev G8_28655 := W3_28655 × V5_28655

/-- The explicit cubic correction polynomial in Claim 28655. -/
def correction28655 (w : W3_28655) : V5_28655 :=
  ![w 0 * (w 1) ^ 2,
    w 0 * (w 2) ^ 2,
    (w 1) ^ 2 * w 2,
    w 1 * (w 2) ^ 2,
    w 0 * w 1 * w 2]

/-- Claim 28655: the displayed polynomial shear is an isomorphism of the
rank-eight additive carrier. -/
def explicitRankEightPolynomialCorrection_claim28655 : Prop :=
  let psi : G8_28655 → G8_28655 :=
    fun p => (p.1, p.2 + correction28655 p.1)
  Function.Bijective psi ∧
    (∀ w v, psi (w, v) = (w, v + correction28655 w)) ∧
    ∃ inv : G8_28655 → G8_28655,
      Function.Bijective inv ∧
        (∀ p, inv (psi p) = p) ∧ (∀ p, psi (inv p) = p)

end MathlibPlus.Algebra.R1077
