import MathlibPlus.Open.Geometry.HeisenbergBorel39693_39697

namespace MathlibPlus.Open.ResearchFormalization.R1621Claim39690

noncomputable section

open MathlibPlus.Open.Geometry.HeisenbergBorel39693_39697

/-- The parameter action is the action induced by the second coordinate on
right cosets of the core.  The displayed equality ties the quotient action to
 the actual affine permutation action rather than supplying an unrelated map. -/
private def primeToSevenAffineParameterFixedOrbit7
    (Γ P : Subgroup Perm7) : Prop :=
  Nat.Coprime (Nat.card Γ / Nat.card P) 7 ∧
    ∃ parameterAction :
        Quotient (QuotientGroup.rightRel (P.subgroupOf Γ)) → Equiv.Perm F7,
      (∀ q, ∃ a : (F7)ˣ, ∃ b : F7,
        ∀ y : F7,
          parameterAction q y = (a : F7) * y + b) ∧
      (∀ h : Γ, ∀ z : W7,
        ((h : Perm7) z).2 =
          parameterAction
            (Quotient.mk (QuotientGroup.rightRel (P.subgroupOf Γ)) h) z.2) ∧
      (∃ y : F7,
        (∀ q, parameterAction q y = y) ∧
          (∃ x : F7,
            orbit7 Γ (x, y) = horizontalLine7 y ∧
              (∀ h : Γ,
                (h : Perm7) '' horizontalLine7 y = horizontalLine7 y)))

/-- Claim 39690: flag-line containment and nontransitivity give the
horizontal-line orbit partition; the prime-to-seven quotient has an affine
parameter action with a fixed parameter, and the resulting stabilizers are
exactly the flag line. -/
def claim39690_nontransitive_flag_line_case : Prop :=
  ∀ (Γ : Subgroup Perm7), Γ ≤ affineBorel7 →
    let P := heisenbergCore7 Γ
    flagTranslationGroup7 ≤ P →
      ¬ transitive7 P →
        (∀ x : W7, orbit7 P x = horizontalLine7 x.2) ∧
          primeToSevenAffineParameterFixedOrbit7 Γ P ∧
          translationStabilizer7 Γ = flagVectors7 ∧
            translationStabilizer7 P = flagVectors7

end

end MathlibPlus.Open.ResearchFormalization.R1621Claim39690
