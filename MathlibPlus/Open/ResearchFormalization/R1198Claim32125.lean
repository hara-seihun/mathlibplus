import MathlibPlus.Open.ResearchFormalization.PrimeFibreOrbitShadowR1198

namespace MathlibPlus.Open.ResearchFormalization.R1198

noncomputable section

open MathlibPlus.Open.ResearchFormalization.PrimeFibreOrbitShadowR1198

/-- The additive-locus carrier used for the character extension. -/
def additiveLocusSubgroup32125
    {p : ℕ} {H : Type*} [AddCommGroup H] [Fact p.Prime]
    (lambda : H → (ZMod p)ˣ) (s : H → ZMod p)
    (L : AddSubgroup H) : Prop :=
  (L : Set H) = additiveLocus lambda s

def pPrimeOrderElement32125
    {p : ℕ} {H : Type*} [AddCommGroup H]
    (h : H) : Prop :=
  Nat.Coprime (orderOf (Multiplicative.ofAdd h)) p

/-- Character extension on the exact additive-locus carrier, including the
vanishing on all prime-to-`p` elements. -/
def claim32125 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime]
    (H : Type*) [Fintype H] [AddCommGroup H]
    (lambda : H → (ZMod p)ˣ) (s : H → ZMod p),
    elementarySylowP p H →
    ∀ L : AddSubgroup H,
      additiveLocusSubgroup32125 lambda s L →
      (∀ x y : L, s (x + y) = s x + s y) →
      ∃ χ : H →+ ZMod p,
        (∀ x : L, χ x = s x) ∧
        (∀ h : H, pPrimeOrderElement32125 (p := p) h → χ h = 0)

end
end MathlibPlus.Open.ResearchFormalization.R1198
