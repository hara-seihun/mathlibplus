import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1121Claim29149

noncomputable section

abbrev F7 := ZMod 7
private abbrev NormalizedOuter := {p : Equiv.Perm F7 // p 0 = 0}

private def outerDerivative
    (p q : NormalizedOuter) (u x : F7) : F7 :=
  p.1.symm (p.1 (x + 2 * u) - 2 * q.1 u)

private def derivativeStep
    (p q : NormalizedOuter) (x y : F7) : Prop :=
  ∃ u : F7, y = outerDerivative p q u x

private def derivativeOrbit
    (p q : NormalizedOuter) (x : F7) : Set F7 :=
  {y | Relation.ReflTransGen (derivativeStep p q) x y}

private def singletonOrbitShape
    (p q : NormalizedOuter) : Prop :=
  ∀ x : F7, derivativeOrbit p q x = ({x} : Set F7)

private def differenceLaw
    (p q : NormalizedOuter) : Prop :=
  ∀ x u : F7,
    p.1 (x + 2 * u) - p.1 x = 2 * q.1 u

private def commonScalarOuter
    (p q : NormalizedOuter) : Prop :=
  ∃ a : F7, ∀ x : F7,
    p.1 x = a * x ∧ q.1 x = a * x

private abbrev Plane := F7 × F7

private def fiber (B : Set Plane) (x : F7) : Set F7 :=
  {y | (x, y) ∈ B}

private def twoPartialFibers (B : Set Plane) : Prop :=
  ∃ x₁ x₂ : F7,
    x₁ ≠ x₂ ∧
      (fiber B x₁).Nonempty ∧ fiber B x₁ ≠ Set.univ ∧
      (fiber B x₂).Nonempty ∧ fiber B x₂ ≠ Set.univ

private def shiftSet {α : Type*} [Add α]
    (S : Set α) (v : α) : Set α :=
  {z | ∃ w, w ∈ S ∧ z = w + v}

private def translatedPartialFibers
    (B : Set Plane) (T : Set F7) (t : F7 → F7) : Prop :=
  ∀ x : F7,
    (fiber B x).Nonempty → fiber B x ≠ Set.univ →
      fiber B x = shiftSet T (t x)

/-- The common-sign vertical equation for the successor offset b, predecessor
offset c, and translated-fiber potential t. -/
private def verticalEquation
    (p q : NormalizedOuter)
    (b c t : F7 → F7) : Prop :=
  ∀ x u : F7,
    t (outerDerivative p q u x) - t x =
      b (x + 2 * u) - b (outerDerivative p q u x) - 2 * c u

private def affineFunction (b : F7 → F7) : Prop :=
  ∃ m k : F7, ∀ x : F7, b x = m * x + k

/-- Claim 29149: singleton outer derivative orbits force the displayed
identity derivative, difference law, and common scalar outer maps. In the
same normalized translated-fiber setting, the exact vertical equation forces
affine successor offsets. -/
def claim29149 : Prop :=
  (∀ p q : NormalizedOuter,
    singletonOrbitShape p q →
      (∀ u x : F7, outerDerivative p q u x = x) ∧
      differenceLaw p q ∧
      commonScalarOuter p q) ∧
  (∀ (p q : NormalizedOuter) (B : Set Plane) (T : Set F7)
      (t b c : F7 → F7),
    singletonOrbitShape p q →
      twoPartialFibers B →
      translatedPartialFibers B T t →
      verticalEquation p q b c t →
      affineFunction b)

end

end MathlibPlus.Open.ResearchFormalization.R1121Claim29149
