import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1148Claim41323

noncomputable section

abbrev F7 := ZMod 7
abbrev V := F7 × F7

/-- Translation by twice a vector in the additive plane `𝔽₇²`. -/
def doubleTranslate (S : Set V) (z : V) : Set V :=
  {v | ∃ s ∈ S, v = s + 2 • z}

/-- Translation by twice an element of a vertical fiber. -/
def fiberDoubleTranslate (S : Set F7) (w : F7) : Set F7 :=
  {y | ∃ b ∈ S, y = b + 2 • w}

/-- The vertical fiber `B_x`. -/
def verticalFiber (B : Set V) (x : F7) : Set F7 :=
  {y | (x, y) ∈ B}

/-- The common-sign zero-fixing section-map hypotheses. -/
def sameSignProfile
    (ε : F7) (p q : F7 → F7 → F7)
    (σ τ : Equiv.Perm V) : Prop :=
  (ε = 1 ∨ ε = -1) ∧
    (∀ x y : F7, σ (x, y) = (ε * x, p x y)) ∧
      (∀ x y : F7, τ (x, y) = (ε * x, q x y)) ∧
        σ (0, 0) = (0, 0) ∧ τ (0, 0) = (0, 0)

/-- The set equation in the same-sign adjacent theorem. -/
def adjacentSetEquation
    (B : Set V) (σ τ : Equiv.Perm V) : Prop :=
  ∀ z : V,
    σ '' doubleTranslate B z = doubleTranslate (σ '' B) (τ z)

/-- The displayed equation on all vertical fibers. -/
def adjacentFiberEquation
    (B : Set V) (p q : F7 → F7 → F7) : Prop :=
  ∀ (x u w : F7),
    (fun y => p (x + 2 • u) y) ''
        fiberDoubleTranslate (verticalFiber B x) w =
      fiberDoubleTranslate
        ((fun y => p x y) '' verticalFiber B x) (q u w)

/-- The order-84 triangular linear stabilizer from the exact `𝔽₇²` model. -/
def triangularLinearStabilizer : Set (Equiv.Perm V) :=
  {φ | ∃ (e c d : F7),
    (e = 1 ∨ e = -1) ∧ d ≠ 0 ∧
      ∀ v : V, φ v = (e * v.1, c * v.1 + d * v.2)}

/-- Claim 41323: the exact same-sign adjacent equation, its vertical-fiber
form, and transport by one member of the order-84 triangular stabilizer. -/
def claim41323 : Prop :=
  Set.ncard triangularLinearStabilizer = 84 ∧
    ∀ (B : Set V) (ε : F7)
      (p q : F7 → F7 → F7) (σ τ : Equiv.Perm V),
      sameSignProfile ε p q σ τ →
        (adjacentSetEquation B σ τ ↔ adjacentFiberEquation B p q) ∧
          (adjacentSetEquation B σ τ →
            ∃ φ : Equiv.Perm V,
              φ ∈ triangularLinearStabilizer ∧ φ '' B = σ '' B)

end

end MathlibPlus.Open.ResearchFormalization.R1148Claim41323
