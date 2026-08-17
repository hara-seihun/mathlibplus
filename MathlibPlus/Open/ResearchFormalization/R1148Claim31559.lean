import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1148Claim31559

noncomputable section

private abbrev F7 := ZMod 7
private abbrev V := F7 × F7

private def translateSet (B : Set V) (z : V) : Set V :=
  {v | ∃ b, b ∈ B ∧ v = b + 2 • z}

private def sectionForm
    (ε : F7) (p : F7 → F7 → F7) (σ : Equiv V V) : Prop :=
  ∀ x y : F7, σ (x, y) = (ε * x, p x y)

private def verticalFiber (B : Set V) (x : F7) : Set F7 :=
  {y | (x, y) ∈ B}

private def verticalFiberEquation
    (B : Set V) (p q : F7 → F7 → F7) : Prop :=
  ∀ x u w : F7,
    {y | ∃ b, b ∈ verticalFiber B x ∧
      y = p (x + 2 * u) (b + 2 * w)} =
    {y | ∃ b, b ∈ verticalFiber B x ∧
      y = p x b + 2 * q u w}

private def sameSignAdjacentEquation
    (B : Set V) (σ τ : Equiv V V) : Prop :=
  ∀ z : V,
    Set.image (fun v => σ v) (translateSet B z) =
      translateSet (Set.image (fun v => σ v) B) (τ z)

private def triangularAffineTransport
    (B : Set V) (σ : Equiv V V) : Prop :=
  ∃ (e c d : F7) (φ : Equiv V V),
    (e = 1 ∨ e = -1) ∧
      d ≠ 0 ∧
      (∀ v : V, φ v = (e * v.1, c * v.1 + d * v.2)) ∧
      Set.image (fun v => φ v) B =
        Set.image (fun v => σ v) B

/-- Claim 31559: every concrete same-sign adjacent profile on the F₇²
    section carrier has a transporter in the triangular order-84 linear
    stabilizer. -/
def exactSameSignAdjacentTheorem_claim31559 : Prop :=
  ∀ (B : Set V) (ε : F7)
    (p q : F7 → F7 → F7)
    (σ τ : Equiv V V),
    (ε = 1 ∨ ε = -1) →
      sectionForm ε p σ →
      sectionForm ε q τ →
      σ (0, 0) = (0, 0) →
      τ (0, 0) = (0, 0) →
      (sameSignAdjacentEquation B σ τ ↔
        verticalFiberEquation B p q) ∧
      (sameSignAdjacentEquation B σ τ →
        triangularAffineTransport B σ)

end

end MathlibPlus.Open.ResearchFormalization.R1148Claim31559
