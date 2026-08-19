import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1618

noncomputable section

abbrev Fiber := ZMod 5

def isFibreTranslation (π : Equiv.Perm Fiber) : Prop :=
  ∃ t : Fiber, π = Equiv.addRight t

def nonlinearSupport {F : Type*} [Group F]
    (π : F → Equiv.Perm Fiber) : Set F :=
  {h | h ≠ 1 ∧ ¬ isFibreTranslation (π h)}

/-- The normalized common-coordinate chart determined by the fibre profile and
quotient permutation. -/
def commonCoordinateChart {F : Type*}
    (π : F → Equiv.Perm Fiber) (σ : Equiv.Perm F) :
    Fiber × F → Fiber × F :=
  fun xh => (π xh.2 xh.1, σ xh.2)

/-- The displayed all-translation chart form. -/
def translationChart {F : Type*}
    (τ : F → Fiber) (σ : Equiv.Perm F) : Fiber × F → Fiber × F :=
  fun xh => (xh.1 + τ xh.2, σ xh.2)

/-- Claim 39664: on the empty nonlinear support, every fibre permutation is a
translation, with the unique normalized translation profile and the displayed
chart form, over the actual `C₇ ⋊ C₃` quotient carrier. -/
def claim39664 : Prop :=
  ∀ (φ : Multiplicative (ZMod 3) →* MulAut (Multiplicative (ZMod 7))),
    (∀ x : Multiplicative (ZMod 7),
      φ (Multiplicative.ofAdd (1 : ZMod 3)) x =
        Multiplicative.ofAdd ((2 : ZMod 7) * Multiplicative.toAdd x)) →
      let F := Multiplicative (ZMod 7) ⋊[φ] Multiplicative (ZMod 3)
      ∀ (π : F → Equiv.Perm Fiber) (σ : Equiv.Perm F),
        σ 1 = 1 →
          π 1 = Equiv.refl Fiber →
            nonlinearSupport π = ∅ →
              ∃! τ : F → Fiber,
                τ 1 = 0 ∧
                  (∀ h : F, π h = Equiv.addRight (τ h)) ∧
                  (∀ (x : Fiber) (h : F),
                    commonCoordinateChart π σ (x, h) =
                      translationChart τ σ (x, h))

end
end MathlibPlus.Open.ResearchFormalization.R1618
