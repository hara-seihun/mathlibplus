import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R5562Claim56673

noncomputable section

abbrev C4 := ZMod 4
abbrev F2 := ZMod 2

noncomputable def orderTwoCorrection (e : F2) : C4 :=
  if e = 0 then 0 else 2

noncomputable def paritySheetMap
    {H : Type*} [AddCommGroup H]
    (β : H ≃+ H) (s₀ s₁ : H → F2) : C4 × H → C4 × H :=
  fun ah =>
    (ah.1 + orderTwoCorrection
      (if ah.1.val % 2 = 0 then s₀ ah.2 else s₁ ah.2),
      β ah.2)

/-- The parity-preserving C4 sheet switch with an odd-order abelian fiber is
bijective for every automorphism beta and the stated rooted s0 normalization. -/
def paritySheetBijection_claim56673 : Prop :=
  ∀ (H : Type*) [Fintype H] [AddCommGroup H],
    Odd (Fintype.card H) →
    ∀ (β : H ≃+ H) (s₀ s₁ : H → F2),
      s₀ 0 = 0 →
      Function.Bijective (paritySheetMap β s₀ s₁)

end

end MathlibPlus.Open.ResearchFormalization.R5562Claim56673
