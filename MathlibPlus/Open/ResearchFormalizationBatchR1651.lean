import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatchR1651

abbrev ElementaryAbelianCarrier (p n : ℕ) := Fin n → ZMod p

def additiveCoset {H : Type*} [AddGroup H]
    (a : H) (E : AddSubgroup H) : Set H :=
  {x | ∃ e : H, e ∈ E ∧ x = a + e}

noncomputable def localizedTranslation {H : Type*} [AddGroup H]
    (C : Set H) (f : H) : H → H :=
  letI : DecidablePred (fun h : H => h ∈ C) :=
    fun h => Classical.propDecidable (h ∈ C)
  fun h => if h ∈ C then h + f else h

/-- Claim 32957: a translation localized to one subgroup coset is a permutation. -/
def localizedTranslationIsPermutation : Prop :=
  ∀ (p n : ℕ) [Fact (Nat.Prime p)]
    (F E : AddSubgroup (ElementaryAbelianCarrier p n))
    (a f : ElementaryAbelianCarrier p n),
    F ≤ E → f ∈ F →
      let C := additiveCoset a E
      let τ := localizedTranslation C f
      let τinv := localizedTranslation C (-f)
      Function.Bijective τ ∧
        (∀ h, τinv (τ h) = h) ∧
        (∀ h, τ (τinv h) = h)

/-- Claim 32960: a nonidentity-coset localized translation is not additive or linear. -/
def localizedTranslationIsNonlinear : Prop :=
  ∀ (p n : ℕ) [Fact (Nat.Prime p)], p % 2 = 1 →
    ∀ (F E : AddSubgroup (ElementaryAbelianCarrier p n))
      (a f c : ElementaryAbelianCarrier p n),
      F ≤ E → f ∈ F → f ≠ 0 →
      let C := additiveCoset a E
      C ≠ (E : Set (ElementaryAbelianCarrier p n)) →
      c ∈ C →
      let τ := localizedTranslation C f
      let twoC : Set (ElementaryAbelianCarrier p n) :=
        {x | ∃ y, y ∈ C ∧ x = y + y}
      twoC ≠ C ∧
        τ 0 = 0 ∧
        τ (c + c) = c + c ∧
        τ c = c + f ∧
        τ c + τ c ≠ τ (c + c) ∧
        ¬ (∀ x y, τ (x + y) = τ x + τ y) ∧
        ¬ (∃ L : (ElementaryAbelianCarrier p n) →ₗ[ZMod p]
              (ElementaryAbelianCarrier p n),
            ∀ x, L x = τ x)

end MathlibPlus.Open.ResearchFormalizationBatchR1651
