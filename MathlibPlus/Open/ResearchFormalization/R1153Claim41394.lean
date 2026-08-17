import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1153Claim41394

abbrev QuaternionBase (A : Type*) := A × (ZMod 2 × ZMod 2)
abbrev LiftSpace (A : Type*) := QuaternionBase A × ZMod 2

def normalizedRelabeling {A : Type*} [AddCommGroup A]
    (f : Equiv.Perm (LiftSpace A)) : Prop :=
  (∀ h : QuaternionBase A, ∀ e : ZMod 2, (f (h, e)).1 = h) ∧
    f (0, 0) = (0, 0)

/-- Claim 41394: after quotient alignment, the normalized lift is a Boolean
switch on each two-point fibre, and its switch is zero at the identity fibre. -/
def claim41394 : Prop :=
  ∀ {A : Type*} [AddCommGroup A]
    (f : Equiv.Perm (LiftSpace A)),
    normalizedRelabeling f →
      ∃ b : QuaternionBase A → ZMod 2,
        b 0 = 0 ∧
        ∀ (h : QuaternionBase A) (e : ZMod 2),
          f (h, e) = (h, e + b h)

end MathlibPlus.Open.ResearchFormalization.R1153Claim41394
