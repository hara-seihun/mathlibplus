import Mathlib

namespace MathlibPlus.Open.Research

abbrev a7 := alternatingGroup (Fin 7)
abbrev s7 := Equiv.Perm (Fin 7)

def a7_inner : Subgroup (MulAut a7) :=
  (MulAut.conj : a7 →* MulAut a7).range

/-- Claim 39497: automorphisms, centralizer, and outer quotient of `A₇`. -/
def a7_automorphisms_centralizer_outer : Prop :=
  let A := a7
  let S := s7
  let I := a7_inner
  (∀ α : MulAut A, ∃ s : S, ∀ x : A,
      ((α x : A) : S) = s * (x : S) * s⁻¹) ∧
    (∀ s : S, (∀ x : A, s * (x : S) = (x : S) * s) → s = 1) ∧
    (∃ h : I.Normal,
      letI : I.Normal := h
      Nonempty ((MulAut A ⧸ I) ≃* Multiplicative (ZMod 2))) ∧
    (∀ α : MulAut A, α ∉ I →
      ∃ s : S, s ∉ alternatingGroup (Fin 7) ∧
        ∀ x : A, ((α x : A) : S) = s * (x : S) * s⁻¹)

end MathlibPlus.Open.Research
