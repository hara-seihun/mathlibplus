import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R0970Claim27735

abbrev Scalar := ZMod 3
abbrev H := Fin 5 → Scalar
abbrev E := Scalar × H

private def xFormula (h : H) : H :=
  ![h 0, h 1, h 2 + h 0, h 3 + h 1, h 4]

private def yFormula (h : H) : H :=
  ![h 0, h 1, h 2, h 3 + h 0, h 4 + h 1]

private def gFormula (h : H) : H :=
  ![h 0, h 1, h 2 + h 0 * (h 0 - 1),
    h 3 + (2 * h 0 - 1) * h 1, h 4 + h 1 ^ 2]

private def displayedAffineMaps (x y g : Equiv.Perm H) : Prop :=
  (∀ h, x h = xFormula h) ∧
    (∀ h, y h = yFormula h) ∧
    (∀ h, g h = gFormula h)

private def translationSubgroup (V : Type*) [AddGroup V] :
    Subgroup (Equiv.Perm V) :=
  Subgroup.closure
    (Set.range (fun v : V => (Equiv.addRight v : Equiv.Perm V)))

private def conjugateSubgroup {V : Type*}
    (q : Equiv.Perm V) (T : Subgroup (Equiv.Perm V)) :
    Subgroup (Equiv.Perm V) :=
  Subgroup.closure
    {u | ∃ t : T, u = q⁻¹ * (t : Equiv.Perm V) * q}

private def liftFormula (α : H →+ Scalar) (x : Equiv.Perm H)
    (z : Scalar) (h : H) : E :=
  (z + α h, x h)

private def validLiftData
    (α β : H →+ Scalar) (x y : Equiv.Perm H)
    (xLift yLift : Equiv.Perm E) : Prop :=
  (∀ z h, xLift (z, h) = liftFormula α x z h) ∧
    (∀ z h, yLift (z, h) = liftFormula β y z h) ∧
    xLift ^ 3 = 1 ∧
    yLift ^ 3 = 1 ∧
    xLift * yLift = yLift * xLift ∧
    (∀ z, xLift (z, 0) = (z, 0)) ∧
    (∀ z, yLift (z, 0) = (z, 0))

private def extensionGroup
    (xLift yLift : Equiv.Perm E) : Subgroup (Equiv.Perm E) :=
  Subgroup.closure
    ((translationSubgroup E : Set (Equiv.Perm E)) ∪ {xLift, yLift})

private def projectsTo (e : Equiv.Perm E) (v : Equiv.Perm H) : Prop :=
  ∀ z h, (e (z, h)).2 = v h

private def fullPreimage
    (Ext : Subgroup (Equiv.Perm E)) (Q : Subgroup (Equiv.Perm H)) :
    Set (Equiv.Perm E) :=
  {e | e ∈ Ext ∧ ∃ v : Q, projectsTo e (v : Equiv.Perm H)}

private def regularElementaryAbelianOrderSix
    (P : Set (Equiv.Perm E)) : Prop :=
  Set.ncard P = 3 ^ 6 ∧
    (1 : Equiv.Perm E) ∈ P ∧
    (∀ a b : Equiv.Perm E, a ∈ P → b ∈ P → a * b ∈ P) ∧
    (∀ a : Equiv.Perm E, a ∈ P → a⁻¹ ∈ P) ∧
    (∀ a b : Equiv.Perm E, a ∈ P → b ∈ P → a * b = b * a) ∧
    (∀ a : Equiv.Perm E, a ∈ P → a ^ 3 = 1) ∧
    (∀ u v : E, ∃! a : Equiv.Perm E, a ∈ P ∧ a u = v)

private def pureABCTranslation (a b c : Scalar) : Equiv.Perm E :=
  Equiv.addRight ((0 : Scalar), ![0, 0, a, b, c])

private def pureABCCommutation
    (P : Set (Equiv.Perm E)) (xLift yLift : Equiv.Perm E) : Prop :=
  (∀ a b c : Scalar, pureABCTranslation a b c ∈ P) ∧
    (∀ a b c : Scalar,
      pureABCTranslation a b c * xLift =
        xLift * pureABCTranslation a b c ∧
      pureABCTranslation a b c * yLift =
        yLift * pureABCTranslation a b c)

private def normalLiftPair
    (α β : H →+ Scalar) (A B C D E₁ : Scalar) : Prop :=
  (∀ h, α h = A * h 2 + B * h 3 + C * h 4) ∧
    (∀ h, β h = D * h 0 + B * h 2 + C * h 3 + E₁ * h 4)

/-- Claim 27735: in the displayed rank-five quotient, every valid fixed-central-
 fibre linear-affine lift has a regular full preimage in either displayed
 quotient direction exactly in the untwisted normal-form class. -/
def claim27735_nonlinearRegularPreimagesSplitOnlyUntwisted : Prop :=
  ∀ (x y g : Equiv.Perm H) (α β : H →+ Scalar)
    (xLift yLift : Equiv.Perm E)
    (A B C D E₁ : Scalar),
    displayedAffineMaps x y g →
    normalLiftPair α β A B C D E₁ →
    validLiftData α β x y xLift yLift →
    (∀ q : Equiv.Perm H, q = g ∨ q = g ^ 2 →
      let P := fullPreimage (extensionGroup xLift yLift)
        (conjugateSubgroup q (translationSubgroup H))
      regularElementaryAbelianOrderSix P ↔
        (α = 0 ∧ β = 0)) ∧
    (∀ q : Equiv.Perm H, q = g ∨ q = g ^ 2 →
      let P := fullPreimage (extensionGroup xLift yLift)
        (conjugateSubgroup q (translationSubgroup H))
      regularElementaryAbelianOrderSix P →
        pureABCCommutation P xLift yLift ∧
        A = 0 ∧ B = 0 ∧ C = 0 ∧ E₁ = 0 ∧
        ((A = 0 ∧ B = 0 ∧ C = 0 ∧ E₁ = 0) → D = 0))

end MathlibPlus.Open.ResearchFormalization.R0970Claim27735
