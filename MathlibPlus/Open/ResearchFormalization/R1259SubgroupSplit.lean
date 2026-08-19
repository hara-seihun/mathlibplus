import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1259SubgroupSplit

noncomputable section

/-- Claim 30707: a subgroup of the direct product of an exponent-`p`
abelian factor and a finite `p'` factor splits into its two coordinate
subgroups.  The pointwise equivalence is the exact subgroup-product
statement, with the coordinate projection represented by `(1,j)`. -/
def elementaryAbelianFactorSplitting_claim30707 : Prop :=
  ∀ (p : ℕ) (A J : Type*) [CommGroup A] [Finite A]
    [Group J] [Finite J],
    Nat.Prime p →
      (∀ a : A, a ^ p = 1) →
        ¬ p ∣ Nat.card J →
          ∀ M : Subgroup (A × J),
            ∀ a : A, ∀ j : J,
              (a, j) ∈ M ↔
                ((a, 1) : A × J) ∈ M ∧
                  ((1, j) : A × J) ∈ M

end

end MathlibPlus.Open.ResearchFormalization.R1259SubgroupSplit
