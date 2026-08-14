import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatch019ffedfPermutation

abbrev A4 := (Equiv.Perm.sign : Equiv.Perm (Fin 4) →* ℤˣ).ker
abbrev A12 := (Equiv.Perm.sign : Equiv.Perm (Fin 12) →* ℤˣ).ker

/-- Claim 29885: a regular A₄ and a seven-cycle generate A₁₂. -/
def claim29885 : Prop :=
  ∀ (A : Subgroup (Equiv.Perm (Fin 12))) (z : Equiv.Perm (Fin 12)),
    Nonempty (A ≃* A4) →
    (∀ x y : Fin 12,
      ∃! a : A, (a : Equiv.Perm (Fin 12)) x = y) →
    orderOf z = 7 →
    (Finset.univ.filter (fun x : Fin 12 => z x = x)).card = 5 →
    Subgroup.closure
        ((A : Set (Equiv.Perm (Fin 12))) ∪ ({z} : Set (Equiv.Perm (Fin 12)))) =
      A12

end MathlibPlus.Open.Research.FormalizationBatch019ffedfPermutation
