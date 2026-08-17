import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1148

noncomputable section

private abbrev V := ZMod 7 × ZMod 7

private def translateSet (B : Set V) (z : V) : Set V :=
  {v | ∃ b, b ∈ B ∧ v = b + 2 • z}

private def sameSignSection
    (ε : ZMod 7) (p : ZMod 7 → ZMod 7 → ZMod 7)
    (σ : Equiv V V) : Prop :=
  ∀ x y : ZMod 7, σ (x, y) = (ε * x, p x y)

private def triangularAffineTransport (B C : Set V) : Prop :=
  ∃ (e c d : ZMod 7) (φ : Equiv V V),
    (e = 1 ∨ e = -1) ∧
    d ≠ 0 ∧
    (∀ v : V, φ v = (e * v.1, c * v.1 + d * v.2)) ∧
    φ '' B = C

/-- Claim 31566: in the concrete F₇² section carrier, inverse maps satisfy
 the same-sign adjacent equation and the point/Fano affine-offset transport
 classification applies to the target section. -/
def claim31566 : Prop :=
  ∀ (B C : Set V) (ε : ZMod 7)
    (p q : ZMod 7 → ZMod 7 → ZMod 7)
    (σ τ : Equiv V V),
    C = σ '' B →
    (ε = 1 ∨ ε = -1) →
    sameSignSection ε p σ →
    sameSignSection ε q τ →
    σ (0, 0) = (0, 0) →
    τ (0, 0) = (0, 0) →
    (∀ z : V,
      σ '' translateSet B z = translateSet C (τ z)) →
    (∀ w : V,
      σ.symm '' translateSet C w =
        translateSet (σ.symm '' C) (τ.symm w)) ∧
      triangularAffineTransport C (σ.symm '' C)

end
end MathlibPlus.Open.ResearchFormalization.R1148
