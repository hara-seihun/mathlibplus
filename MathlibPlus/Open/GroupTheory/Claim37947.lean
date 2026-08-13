import MathlibPlus.Basic

namespace MathlibPlus.Open.GroupTheory

/--
Claim 37947.  In a direct product of finite groups of coprime orders, the
prime support of an element's order detects the factor in which it lies.  The
same support characterization makes the two coordinate factors characteristic.
The two factor axes are written as subsets rather than by an unreviewed
subgroup definition, so the statement records both the element classification
and the characteristic conclusion explicitly.
-/
def coprimeFactorsCharacteristicHallFactors_claim37947 : Prop :=
  ∀ (A B : Type*) [Fintype A] [Fintype B] [Group A] [Group B],
    Nat.Coprime (Fintype.card A) (Fintype.card B) →
    let G := A × B
    let AAxis : Set G := {g | g.2 = 1}
    let BAxis : Set G := {g | g.1 = 1}
    (∀ g : G,
      ((∀ p : ℕ, Nat.Prime p → p ∣ orderOf g → p ∣ Fintype.card A) ↔
        g.2 = 1)) ∧
      (∀ g : G,
        ((∀ p : ℕ, Nat.Prime p → p ∣ orderOf g → p ∣ Fintype.card B) ↔
          g.1 = 1)) ∧
      (∀ φ : G ≃* G, φ '' AAxis = AAxis) ∧
      (∀ φ : G ≃* G, φ '' BAxis = BAxis)

end MathlibPlus.Open.GroupTheory
