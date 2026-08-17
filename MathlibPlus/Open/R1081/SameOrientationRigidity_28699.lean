import MathlibPlus.Open.R1081.FactorGraphs_01a000db_a016_792b_b33f_00a9410f47c6

namespace MathlibPlus.Open.R1081

private abbrev A := Z7 × Z7

private def translateSet (B : Set A) (z : A) : Set A :=
  Set.image (fun v : A => v + z) B

private def aperiodicSet (B : Set A) : Prop :=
  ∀ z : A, translateSet B z = B → z = 0

private def partialFiber (B : Set A) (x : Z7) : Prop :=
  (∃ y : Z7, (x, y) ∈ B) ∧
    ∃ y : Z7, (x, y) ∉ B

private def exactlyOnePartialFiber (B : Set A) : Prop :=
  ∃ x : Z7, partialFiber B x ∧
    ∀ x' : Z7, partialFiber B x' → x' = x

private def atLeastTwoPartialFibers (B : Set A) : Prop :=
  ∃ x x' : Z7, x ≠ x' ∧ partialFiber B x ∧ partialFiber B x'

private def zeroStabilizerForm
    (Q I : Set Z7) (σ : Equiv.Perm A)
    (a : Z7) (ε b : Z7 → Z7) : Prop :=
  kernelGraphAut Q I σ ∧
    σ (0, 0) = (0, 0) ∧
    (a = 1 ∨ a = -1) ∧
    b 0 = 0 ∧
    (∀ x : Z7, ε x = 1 ∨ ε x = -1) ∧
    ∀ x y : Z7, σ (x, y) = (a * x, ε x * y + b x)

private def sameOrientationEquation
    (σ τ : Equiv.Perm A) (B : Set A) : Prop :=
  ∀ z : A,
    Set.image (fun v : A => σ v) (translateSet B (2 • z)) =
      translateSet
        (Set.image (fun v : A => σ v) B)
        (2 • τ z)

private def triangularLinear (L : (Z7 × Z7) ≃ₗ[Z7] (Z7 × Z7)) : Prop :=
  ∃ a d c : Z7,
    (a = 1 ∨ a = -1) ∧
    (d = 1 ∨ d = -1) ∧
    ∀ x y : Z7, L (x, y) = (a * x, c * x + d * y)

private def linearConnectionStabilizerMember
    (Q I : Set Z7) (L : (Z7 × Z7) ≃ₗ[Z7] (Z7 × Z7)) : Prop :=
  Set.image (fun p : A => L p) (kernelConnectionSet Q I) =
    kernelConnectionSet Q I

private def verticalAffineTransport
    (Q I : Set Z7) (σ : Equiv.Perm A) (B : Set A) : Prop :=
  ∃ L : (Z7 × Z7) ≃ₗ[Z7] (Z7 × Z7),
    linearConnectionStabilizerMember Q I L ∧
    triangularLinear L ∧
    ∃ v : Z7,
      translateSet
          (Set.image (fun p : A => L p) B)
          (0, v) =
        Set.image (fun p : A => σ p) B

/-- Claim 28699: same-orientation zero-stabilizer pairs obey the two
partial-fiber alternatives, with the order-28 triangular subgroup in the
one-partial-fiber case and common linear offsets otherwise. -/
def claim28699 : Prop :=
  ∀ Q I : Set Z7, admissibleQI Q I →
    ∀ (σ τ : Equiv.Perm A) (B : Set A)
      (a : Z7) (ε η b c : Z7 → Z7),
      zeroStabilizerForm Q I σ a ε b →
      zeroStabilizerForm Q I τ a η c →
      aperiodicSet B →
      sameOrientationEquation σ τ B →
      (exactlyOnePartialFiber B →
        verticalAffineTransport Q I σ B) ∧
      (atLeastTwoPartialFibers B →
        ∃ d k : Z7,
          (d = 1 ∨ d = -1) ∧
          (∀ x : Z7,
            ε x = d ∧ η x = d ∧ b x = k * x ∧ c x = k * x) ∧
          σ = τ ∧
          ∀ x y : Z7, σ (x, y) = (a * x, k * x + d * y))

end MathlibPlus.Open.R1081
