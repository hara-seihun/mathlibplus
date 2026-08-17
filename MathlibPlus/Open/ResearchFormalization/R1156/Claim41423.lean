import MathlibPlus.Open.ResearchFormalization.R1156Claim31657_31660

namespace MathlibPlus.Open.ResearchFormalization.R1156

noncomputable section

/-- Claim 41423: every normalized affine assignment on a finite support has
exactly the 84 compatible families of nonlinear normalized labels. -/
def exactlyEightyFourCompatibleFamilies_claim41423 : Prop :=
  ∀ (X : Finset F7) (a : X) (r : (↥X) → F7),
    2 ≤ X.card →
      r a = 0 →
        (∃ m : F7,
          ∀ x : X,
            r x = m * ((x : F7) - (a : F7))) →
          Nat.card
              {labels : F7 → F7 → F7 //
                (∀ y : F7, nonlinearNormalizedLabel (labels y)) ∧
                  shiftedCompatibilityEquation X r labels} = 84

end

end MathlibPlus.Open.ResearchFormalization.R1156
