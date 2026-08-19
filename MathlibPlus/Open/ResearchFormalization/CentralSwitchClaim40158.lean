import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.CentralSwitchClaim40158

noncomputable section

private abbrev H (A : Type*) := A × Equiv.Perm (Fin 3)
private abbrev Lift (A : Type*) := H A × ZMod 2

private def normalizedCocycle {A : Type*} [Group A]
    (κ : H A → H A → ZMod 2) : Prop :=
  (∀ h : H A, κ 1 h = 0) ∧
  (∀ h : H A, κ h 1 = 0) ∧
  (∀ h u v : H A,
    κ h u + κ (h * u) v = κ u v + κ h (u * v))

private def centralSwap {A : Type*} [Group A] : Equiv.Perm (Lift A) :=
  Equiv.prodCongr (Equiv.refl (H A)) (Equiv.addRight 1)

private def fixesTwoPointBlocks {A : Type*} [Group A]
    (f : Equiv.Perm (Lift A)) : Prop :=
  ∀ h : H A, ∀ e : ZMod 2, (f (h, e)).1 = h

private def commutesWithCentralSwap {A : Type*} [Group A]
    (f : Equiv.Perm (Lift A)) : Prop :=
  ∀ x : Lift A, f (centralSwap x) = centralSwap (f x)

/-- Claim 40158: after quotient alignment, a normalized relabeling of the
    two-point central extension is a Boolean block switching. -/
def claim40158 : Prop :=
  ∀ (A : Type*) [Finite A] [Fintype A] [Group A]
    (hcoprime : Nat.Coprime (Nat.card A) 6)
    (κ : H A → H A → ZMod 2)
    (f : Equiv.Perm (Lift A)),
    normalizedCocycle κ →
    fixesTwoPointBlocks f →
    commutesWithCentralSwap f →
    f ((1 : H A), 0) = ((1 : H A), 0) →
    ∃ b : H A → ZMod 2,
      b 1 = 0 ∧
      ∀ (h : H A) (e : ZMod 2),
        f (h, e) = (h, e + b h)

end
end MathlibPlus.Open.ResearchFormalization.CentralSwitchClaim40158
