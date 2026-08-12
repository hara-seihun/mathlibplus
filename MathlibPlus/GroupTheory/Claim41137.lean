import Mathlib

namespace MathlibPlus.GroupTheory

/-!
Claim 41137 (R-1343).

`Fin 3 → ZMod 2` is the coordinate model for `C₂³`, and
`Fin r → ZMod 3` is the coordinate model for an arbitrary finite-dimensional
`F₃`-vector space.  The normalization hypotheses on `σ` and `s` are retained
by the companion theorem below; the profile itself is the exact displayed
map.
-/

/-- The fiber-preserving translation profile attached to a base permutation
and a ternary translation function. -/
def fiberPreservingTranslationProfile_claim41137
    (r : ℕ)
    (σ : (Fin 3 → ZMod 2) ≃ (Fin 3 → ZMod 2))
    (s : (Fin 3 → ZMod 2) → (Fin r → ZMod 3)) :
    (Fin 3 → ZMod 2) × (Fin r → ZMod 3) →
      (Fin 3 → ZMod 2) × (Fin r → ZMod 3) :=
  fun p => (σ p.1, p.2 + s p.1)

/-- A normalized base permutation and translation profile fix the zero fiber
at the zero vector. -/
theorem fiberPreservingTranslationProfile_claim41137_zero
    (r : ℕ)
    (σ : (Fin 3 → ZMod 2) ≃ (Fin 3 → ZMod 2))
    (s : (Fin 3 → ZMod 2) → (Fin r → ZMod 3))
    (hσ : σ 0 = 0) (hs : s 0 = 0) :
    fiberPreservingTranslationProfile_claim41137 r σ s (0, 0) = (0, 0) := by
  simp [fiberPreservingTranslationProfile_claim41137, hσ, hs]

end MathlibPlus.GroupTheory
