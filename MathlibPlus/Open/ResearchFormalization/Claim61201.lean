import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim61201

abbrev semidirectGroup {W H : Type*} [AddCommGroup W] [Group H]
    (ρ : H →* MulAut (Multiplicative W)) :=
  (Multiplicative W) ⋊[ρ] H

def semidirectPoint {W H : Type*} [AddCommGroup W] [Group H]
    (ρ : H →* MulAut (Multiplicative W)) (w : W) (h : H) :
    semidirectGroup ρ :=
  ⟨Multiplicative.ofAdd w, h⟩

def quotientSection {W H : Type*} [AddCommGroup W] [Group H]
    (ρ : H →* MulAut (Multiplicative W))
    (S : Set (semidirectGroup ρ)) (h : H) : Set W :=
  {w | semidirectPoint ρ w h ∈ S}

def translateSection {W : Type*} [AddCommGroup W]
    (A : Set W) (p : W) : Set W :=
  (fun x : W => x + p) '' A

def translationPeriod {W : Type*} [AddCommGroup W]
    (A : Set W) : Set W :=
  {p | translateSection A p = A}

def actedAdd {W H : Type*} [AddCommGroup W] [Group H]
    (ρ : H →* MulAut (Multiplicative W)) (h : H) (u : W) : W :=
  Multiplicative.toAdd ((ρ h) (Multiplicative.ofAdd u))

def pointedQuotientIdentity {W H : Type*} [AddCommGroup W] [Group H]
    (ρ : H →* MulAut (Multiplicative W)) (F : H → Equiv.Perm W)
    (f : Equiv.Perm (semidirectGroup ρ)) : Prop :=
  ∀ w h,
    f (semidirectPoint ρ w h) = semidirectPoint ρ (F h w) h

def directedCayleyIsomorphism {G : Type*} [Group G]
    (S T : Set G) (f : Equiv.Perm G) : Prop :=
  ∀ x y, x⁻¹ * y ∈ S ↔ (f x)⁻¹ * f y ∈ T

def oneCocycle {W H : Type*} [AddCommGroup W] [Group H]
    (ρ : H →* MulAut (Multiplicative W)) (z : H → W) : Prop :=
  ∀ h k, z (h * k) = z h + actedAdd ρ h (z k)

def claim_61201 : Prop :=
  ∀ (W H : Type*) [AddCommGroup W] [Finite W] [Group H] [Finite H]
    (ρ : H →* MulAut (Multiplicative W))
    (S T : Set (semidirectGroup ρ)) (F : H → Equiv.Perm W),
    F 1 = 1 →
      ∀ f : Equiv.Perm (semidirectGroup ρ),
        pointedQuotientIdentity ρ F f →
          directedCayleyIsomorphism S T f →
            (∀ h,
                quotientSection ρ T h =
                    translateSection (quotientSection ρ S h) (F h 0) ∧
                  ∀ w,
                    F h w - w - F h 0 ∈
                      translationPeriod (quotientSection ρ S h)) ∧
              ∀ z : H → W,
                oneCocycle ρ z →
                  (∀ h,
                    F h 0 - z h ∈
                      translationPeriod (quotientSection ρ S h)) →
                    ∃ α : semidirectGroup ρ ≃* semidirectGroup ρ,
                      (∀ w h,
                        α (semidirectPoint ρ w h) =
                          semidirectPoint ρ (w + z h) h) ∧
                        α '' S = T

end MathlibPlus.Open.ResearchFormalization.Claim61201
