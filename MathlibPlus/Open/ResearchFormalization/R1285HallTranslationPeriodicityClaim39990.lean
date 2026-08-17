import MathlibPlus.Open.ResearchFormalization.R1285.Claim39994

namespace MathlibPlus.Open.ResearchFormalization.R1285.HallTranslationPeriodicity

open MathlibPlus.Open.ResearchFormalization.R1182.Claim31941
open MathlibPlus.Open.ResearchFormalization.R1285

private def derivativeTranslationsAt
    (n : ℕ) (f : Equiv.Perm (HallQ12Carrier n))
    (h : Q12) : Set (ZMod n) :=
  {c | ∃ d ∈ hallQ12DerivativeGenerators n f,
    d (0, h) = (c, h)}

private def derivativeSubgroupAt
    (n : ℕ) (f : Equiv.Perm (HallQ12Carrier n))
    (h : Q12) : AddSubgroup (ZMod n) :=
  AddSubgroup.closure (derivativeTranslationsAt n f h)

private def atomTranslationSubgroup
    (n : ℕ) (f : Equiv.Perm (HallQ12Carrier n))
    (X : Set Q12) : AddSubgroup (ZMod n) :=
  AddSubgroup.closure
    {c | ∃ h ∈ X, c ∈ derivativeTranslationsAt n f h}

private def sectionPeriodic
    (n : ℕ) (S : Set (HallQ12Carrier n))
    (X : Set Q12) (D : AddSubgroup (ZMod n)) : Prop :=
  ∀ h ∈ X, ∀ x : ZMod n, ∀ c ∈ D,
    ((x + c, h) ∈ S ↔ (x, h) ∈ S)

/-- Claim 39990: for each of the two exact projected atoms, the Hall
translations from derivatives stabilizing a base point generate a subgroup
independent of that base point, and every invariant connection-set section is
periodic under that subgroup. -/
def hallTranslationPeriodicity_claim39990 : Prop :=
  ∀ n : ℕ, Squarefree n → Nat.Coprime n 6 →
    ∀ (lam : Q12 → (ZMod n)ˣ) (tau : Q12 → ZMod n)
      (σ : Equiv.Perm Q12)
      (f : Equiv.Perm (HallQ12Carrier n)),
      normalizedHallQ12AffineLift n lam tau σ f →
      ∀ X : Set Q12,
        (X = axisAtom ∨ X = outerAtom) →
        let D := atomTranslationSubgroup n f X
        (∀ h ∈ X, derivativeSubgroupAt n f h = D) ∧
          (∀ S : Set (HallQ12Carrier n),
            hallQ12IdentityFree n S →
            hallQ12InverseClosed n S →
            hallQ12DerivativeInvariant n f S →
            sectionPeriodic n S X D)

end MathlibPlus.Open.ResearchFormalization.R1285.HallTranslationPeriodicity
