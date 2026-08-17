import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1153Claim31632

noncomputable section

abbrev Base (A : Type*) := A × (ZMod 2 × ZMod 2)
abbrev Extension (A : Type*) := Base A × ZMod 2

/-- A normalized central two-cocycle on the concrete `A×C₂²` base. -/
def normalizedCocycle {A : Type*} [AddCommGroup A]
    (κ : Base A → Base A → ZMod 2) : Prop :=
  (∀ h, κ 0 h = 0) ∧
    (∀ h, κ h 0 = 0) ∧
    (∀ h u v,
      κ h u + κ (h + u) v = κ u v + κ h (u + v))

def nonsplitCentralExtension {A : Type*} [AddCommGroup A]
    (κ : Base A → Base A → ZMod 2) : Prop :=
  normalizedCocycle κ ∧
    ¬ ∃ splitting : Base A → ZMod 2,
      splitting 0 = 0 ∧
        ∀ h u,
          splitting (h + u) = splitting h + splitting u + κ h u

def extensionMul {A : Type*} [AddCommGroup A]
    (κ : Base A → Base A → ZMod 2)
    (x y : Extension A) : Extension A :=
  (x.1 + y.1, x.2 + y.2 + κ x.1 y.1)

def extensionInv {A : Type*} [AddCommGroup A]
    (κ : Base A → Base A → ZMod 2) (x : Extension A) : Extension A :=
  (-x.1, -x.2 - κ x.1 (-x.1))

def normalizedLift {A : Type*} [AddCommGroup A]
    (b : Base A → ZMod 2) : Prop :=
  b 0 = 0

def liftShear {A : Type*} [AddCommGroup A]
    (b : Base A → ZMod 2) : Extension A → Extension A :=
  fun x => (x.1, x.2 + b x.1)

/-- The actual group-relative derivative: apply the lift to the right
translate, divide by the lifted direction, then undo the lift. -/
def normalizedRelativeDerivative {A : Type*} [AddCommGroup A]
    (κ : Base A → Base A → ZMod 2)
    (b : Base A → ZMod 2) (u : Base A) : Extension A → Extension A :=
  fun x =>
    liftShear b
      (extensionMul κ
        (liftShear b (extensionMul κ x (u, 0)))
        (extensionInv κ (liftShear b (u, 0))))

/-- Claim 31632: the cocycle disappears from the normalized relative
 derivative of the normalized Boolean lift, leaving the displayed three
switching terms. -/
def claim31632 : Prop :=
  ∀ {A : Type*} [Fintype A] [AddCommGroup A]
    (κ : Base A → Base A → ZMod 2),
    nonsplitCentralExtension κ →
    ∀ (b : Base A → ZMod 2), normalizedLift b →
      ∀ (h u : Base A) (e : ZMod 2),
        normalizedRelativeDerivative κ b u (h, e) =
          (h, e + b (h + u) + b h + b u)

end
end MathlibPlus.Open.ResearchFormalization.R1153Claim31632
