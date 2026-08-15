import Mathlib

namespace MathlibPlus.Open.FormalizationBatch.LocalizedTranslation

private abbrev H := Fin 5 → ZMod 3
private abbrev D := Fin 2 → ZMod 3

/-- A nonidentity envelope coset supports exactly the stated localized line
    translation by a nonzero vector in the one-dimensional subspace. -/
def localizedLineTranslation : Prop := by
  classical
  exact
    let H' := H
    let D' := D
    ∀ (L E : Submodule (ZMod 3) H')
      (hLE : L ≤ E) (hE : E < ⊤)
      (hLdim : Module.finrank (ZMod 3) L = 1)
      (C : Set H') (hC : ∃ h₀ : H', C = {h : H' | h - h₀ ∈ E})
      (hCnonid : C ≠ (E : Set H'))
      (f : H') (hfL : f ∈ L) (hfne : f ≠ 0),
      ∃! q : H' → H', ∀ h : H', q h = if h ∈ C then h + f else h

end MathlibPlus.Open.FormalizationBatch.LocalizedTranslation
