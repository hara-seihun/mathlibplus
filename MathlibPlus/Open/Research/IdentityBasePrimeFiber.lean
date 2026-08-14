import Mathlib

namespace MathlibPlus.Open.Research

abbrev A4 := alternatingGroup (Fin 4)

/-- A translation of the additive prime field by `a`. -/
def translation (p : ℕ) (a : ZMod p) : Equiv (ZMod p) (ZMod p) :=
  { toFun := fun x => x + a
    invFun := fun x => x - a
    left_inv := by
      intro x
      simp [sub_eq_add_neg, add_assoc]
    right_inv := by
      intro x
      simp [sub_eq_add_neg, add_assoc] }

/-- Being one of the translations of `𝔽_p`. -/
def isTranslation (p : ℕ) (e : Equiv (ZMod p) (ZMod p)) : Prop :=
  ∃ a : ZMod p, e = translation p a

/-- The coordinate chart described in the admitted identity-base claim. -/
def identityBaseCommonCoordinateFiberChart
    (p : ℕ) (σ : A4 → Equiv (ZMod p) (ZMod p))
    (f : ZMod p × A4 → ZMod p × A4) : Prop :=
  Nat.Prime p ∧ 5 ≤ p ∧ σ 1 = Equiv.refl (ZMod p) ∧
    f = fun x => ((σ x.2) x.1, x.2)

/-- The restriction called `R_u` in the inverse-chart claim. -/
def inverseChartDerivative
    (p : ℕ) (σ : A4 → Equiv (ZMod p) (ZMod p)) (h : A4) (u : ZMod p) :
    Equiv (ZMod p) (ZMod p) :=
  (translation p (u - (σ (h⁻¹)) u)).trans (σ h).symm

/-- Conjugation of a translation by a permutation of the field. -/
def conjugateTranslation
    (p : ℕ) (e : Equiv (ZMod p) (ZMod p)) (c : ZMod p) :
    Equiv (ZMod p) (ZMod p) :=
  (e.trans (translation p c)).trans e.symm

/-- All points lie in one orbit of the displayed permutation. -/
def isFullCycle (p : ℕ) (e : Equiv (ZMod p) (ZMod p)) : Prop :=
  ∀ x y : ZMod p, ∃ k : ℕ, (e ^ k) x = y

/-- Exact open statement of the inverse-chart nontranslation claim. -/
def inverseChartNontranslationForcesFullCycle
    (p : ℕ) (σ : A4 → Equiv (ZMod p) (ZMod p))
    (f : ZMod p × A4 → ZMod p × A4) (h : A4) : Prop :=
  identityBaseCommonCoordinateFiberChart p σ f →
    ¬ isTranslation p (σ (h⁻¹)) →
      ∃ u z c : ZMod p,
        c ≠ 0 ∧
        (inverseChartDerivative p σ h z).symm.trans
            (inverseChartDerivative p σ h u) =
          conjugateTranslation p (σ h) c ∧
        isFullCycle p (conjugateTranslation p (σ h) c)

/-- The restriction called `Q_u` in the order-three opposite-orientation claim. -/
def orderThreeDerivative
    (p : ℕ) (σ : A4 → Equiv (ZMod p) (ZMod p)) (h : A4)
    (τ : A4 → ZMod p) (u : ZMod p) : Equiv (ZMod p) (ZMod p) :=
  (translation p (u + τ (h⁻¹) - (σ h) u)).trans (σ h).symm

/-- Exact open statement of the order-three opposite-orientation claim. -/
def orderThreeOppositeOrientationForcesFullCycle
    (p : ℕ) (σ : A4 → Equiv (ZMod p) (ZMod p))
    (f : ZMod p × A4 → ZMod p × A4) (h : A4)
    (τ : A4 → ZMod p) : Prop :=
  identityBaseCommonCoordinateFiberChart p σ f →
    (isTranslation p (σ (h⁻¹)) ∧
      σ (h⁻¹) = translation p (τ (h⁻¹)) ∧
      ¬ isTranslation p (σ h)) →
      orderOf h = 3 ∧
        ∃ u z c : ZMod p,
          c ≠ 0 ∧
          (orderThreeDerivative p σ h τ z).symm.trans
              (orderThreeDerivative p σ h τ u) =
            conjugateTranslation p (σ h) c ∧
          isFullCycle p (conjugateTranslation p (σ h) c)

end MathlibPlus.Open.Research
