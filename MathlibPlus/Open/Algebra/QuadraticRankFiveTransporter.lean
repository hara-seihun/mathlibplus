import Mathlib

noncomputable section

namespace MathlibPlus.Open.Algebra

private abbrev F₃ := ZMod 3
private abbrev H := F₃ × F₃ × F₃ × F₃ × F₃
private abbrev E := F₃ × H
private abbrev Coefficients := F₃ × F₃ → F₃ × F₃ × F₃
private def quadraticTransporter (h : H) : H :=
  (h.1, h.2.1,
    h.2.2.1 + h.1 * (h.1 - 1),
    h.2.2.2.1 + (2 * h.1 - 1) * h.2.1,
    h.2.2.2.2 + h.2.1 ^ 2)
private def coefficientDot (F : Coefficients) (h : H) : F₃ :=
  (F (h.1, h.2.1)).1 * h.2.2.1 +
    (F (h.1, h.2.1)).2.1 * h.2.2.2.1 +
    (F (h.1, h.2.1)).2.2 * h.2.2.2.2
private def qFormula (F : Coefficients) (z : E) : E :=
  (z.1 + coefficientDot F z.2, quadraticTransporter z.2)
private def translation (v : E) : Equiv.Perm E :=
  Equiv.addRight v
private def translationGroup : Subgroup (Equiv.Perm E) :=
  Subgroup.closure (Set.range translation)

/-- Claim 28456: the fixed quadratic rank-five transporter and its generated group. -/
def claim28456
    (F : Coefficients) (qF : E ≃ E) (Tq : Subgroup (Equiv.Perm E)) : Prop :=
  Function.Bijective quadraticTransporter ∧
    (∀ i j a b c : F₃,
    quadraticTransporter (i, j, a, b, c) =
      (i, j, a + i * (i - 1), b + (2 * i - 1) * j, c + j ^ 2)) ∧
    (∀ h : H, coefficientDot F h =
      (F (h.1, h.2.1)).1 * h.2.2.1 +
        (F (h.1, h.2.1)).2.1 * h.2.2.2.1 +
        (F (h.1, h.2.1)).2.2 * h.2.2.2.2) ∧
    (∀ z : E, qF z = qFormula F z) ∧
    (∀ u : Equiv.Perm E,
      u ∈ Tq ↔ ∃ v : Equiv.Perm E, v ∈ translationGroup ∧
        u = qF⁻¹ * v * qF) ∧
    let T := translationGroup
    let G_F := Subgroup.closure (T ⊔ Tq)
    (∀ v : E, translation v ∈ T) ∧ T ≤ G_F ∧ Tq ≤ G_F

end MathlibPlus.Open.Algebra
