import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.Claim31631

private abbrev H (A : Type*) := A × (ZMod 2 × ZMod 2)
private abbrev LiftSpace (A : Type*) := H A × ZMod 2

private def normalizedLift {A : Type*} [AddCommGroup A]
    (f : Equiv.Perm (LiftSpace A)) : Prop :=
  (∀ h : H A, ∀ e : ZMod 2, (f (h, e)).1 = h) ∧
    f (0, 0) = (0, 0)

/-- Every normalized relabeling left after the quotient alignment is the
    displayed Boolean switching on H×C₂, with b(0)=0. -/
def claim31631 : Prop :=
  ∀ {A : Type*} [AddCommGroup A]
    (f : Equiv.Perm (LiftSpace A)),
    normalizedLift f →
      ∃ b : H A → ZMod 2,
        b 0 = 0 ∧
        ∀ (h : H A) (e : ZMod 2),
          f (h, e) = (h, e + b h)

end MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.Claim31631
