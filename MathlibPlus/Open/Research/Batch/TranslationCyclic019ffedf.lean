import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatch019ffedfCyclic

abbrev A4 := (Equiv.Perm.sign : Equiv.Perm (Fin 4) →* ℤˣ).ker

/-- The displacement appearing in the translation-only cyclic telescoping claim. -/
def derivativeDisplacement (p : ℕ) (h : A4) (τ : A4 → ZMod p) (j : ℕ) : ZMod p :=
  τ (h ^ (j + 1)) - τ (h ^ j) - τ h

/-- The prime-fiber span of all cyclic derivative displacements. -/
def derivativeSpan (p : ℕ) (h : A4) (τ : A4 → ZMod p) : Submodule (ZMod p) (ZMod p) :=
  Submodule.span (ZMod p) (Set.range (derivativeDisplacement p h τ))

/-- Claim 29867: translation-only cyclic telescoping. -/
def claim29867 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → 5 ≤ p →
    ∀ (h : A4) (m : ℕ),
      orderOf h = m → (m = 2 ∨ m = 3) →
      ∀ (τ : A4 → ZMod p),
        (∀ j : ℕ,
          τ (h ^ j) - j • τ h ∈ derivativeSpan p h τ) ∧
        m • τ h ∈ derivativeSpan p h τ ∧
        IsUnit (m : ZMod p) ∧
        τ h ∈ derivativeSpan p h τ

end MathlibPlus.Open.Research.FormalizationBatch019ffedfCyclic
