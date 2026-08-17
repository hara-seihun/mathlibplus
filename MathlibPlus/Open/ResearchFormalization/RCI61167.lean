import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.RCI61167

private def discrepancy {E : Type*} [Group E]
    {P Q : Subgroup E} (φ : P ≃* Q) (x : P) : E :=
  (φ x : E) * (x : E)⁻¹

private def conjugationOnA {E : Type*} [Group E]
    (x : E) (a : E) : E :=
  x * a * x⁻¹

private def coboundaryValue {E : Type*} [Group E]
    (x : E) (a : E) : E :=
  a * (conjugationOnA x a)⁻¹

private def conjugatedSubgroup {E : Type*} [Group E]
    {P : Subgroup E} (a : E) : Subgroup E :=
  Subgroup.map (MulAut.conj a).toMonoidHom P

private def differenceAutomorphismFormula
    {E : Type*} [Group E] {A : Subgroup E}
    (c : E) (δ : A ≃* A) : Prop :=
  ∀ b : A,
    (δ b : E) =
      conjugationOnA c (b : E) * (b : E)⁻¹

/-- Claim 61167: a quotient-compatible isomorphism of subgroup lifts has the
common conjugation action, its multiplicative form of the section discrepancy
is a 1-cocycle, and a central fixed-point-free difference automorphism supplies
the displayed literal conjugating element. -/
def quotientCompatibleSectionCocycleAndCentralCorrection_claim61167 : Prop :=
  ∀ (E : Type*) [Group E]
    (A : Subgroup E) [A.Normal]
    (P Q : Subgroup E) (φ : P ≃* Q),
    (∀ a b : A, (a : E) * (b : E) = (b : E) * (a : E)) →
    (∀ x : P,
      QuotientGroup.mk' (N := A) (φ x : E) =
        QuotientGroup.mk' (N := A) (x : E)) →
      let z := discrepancy φ
      (∀ x : P, z x ∈ A) ∧
        (∀ x : P, ∀ a : A,
          conjugationOnA (φ x : E) (a : E) =
            conjugationOnA (x : E) (a : E)) ∧
        (∀ x y : P,
          z (x * y) =
            z x * conjugationOnA (x : E) (z y)) ∧
        (∀ a : A,
          (∀ x : P, z x = coboundaryValue (x : E) (a : E)) →
            (∀ x : P,
              (φ x : E) = (a : E) * (x : E) * (a : E)⁻¹) ∧
              Q = conjugatedSubgroup (P := P) (a : E)) ∧
        (∀ c : P,
          (∀ x : P, c * x = x * c) →
            (∀ δ : A ≃* A, differenceAutomorphismFormula (c : E) δ →
              ∃ hz : z c ∈ A, ∃ a : A,
                (a : A) = (δ.symm ⟨z c, hz⟩)⁻¹ ∧
                (∀ x : P,
                  z x = coboundaryValue (x : E) (a : E)) ∧
                (∀ x : P,
                  (φ x : E) = (a : E) * (x : E) * (a : E)⁻¹) ∧
                Q = conjugatedSubgroup (P := P) (a : E)))

end MathlibPlus.Open.ResearchFormalization.RCI61167
