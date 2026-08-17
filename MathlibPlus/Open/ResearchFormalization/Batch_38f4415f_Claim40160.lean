import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.Claim40160

private abbrev H (A : Type*) := A × Equiv.Perm (Fin 3)

private def linearitySet {A : Type*} [Group A]
    (b : H A → ZMod 2) : Set (H A) :=
  {h | ∀ u : H A, b (h * u) = b h + b u}

private def isLinearitySubgroup {A : Type*} [Group A]
    (b : H A → ZMod 2) (L : Subgroup (H A)) : Prop :=
  ∀ h : H A, h ∈ L ↔ h ∈ linearitySet b

/-- The linearity subgroup of a normalized Boolean switching extends across
    H=A×S₃ to a global C₂ character, with the odd A-part killed. -/
def claim40160 : Prop :=
  ∀ (A : Type*) [Finite A] [Fintype A] [Group A]
    (hcoprime : Nat.Coprime (Nat.card A) 6)
    (b : H A → ZMod 2), b (1, 1) = 0 →
    ∃ L : Subgroup (H A),
      isLinearitySubgroup b L ∧
      (∀ a : A, (a, 1) ∈ L → b (a, 1) = 0) ∧
      ∃ χ : H A → ZMod 2,
        χ (1, 1) = 0 ∧
        (∀ h u : H A, χ (h * u) = χ h + χ u) ∧
        (∀ h : H A, h ∈ L → χ h = b h)

end MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.Claim40160
