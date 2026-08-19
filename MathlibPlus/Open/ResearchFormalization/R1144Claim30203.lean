import MathlibPlus.Open.ResearchFormalization.R1144DistinctLabels

namespace MathlibPlus.Open.ResearchFormalization.R1144Claim30203

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1144DistinctLabels

abbrev C7 := ZMod 7

private def scalarLabel (δ : C7 → C7) : Prop :=
  ∃ a : C7ˣ, ∀ t : C7, δ t = (a : C7) * t

private def pointLabels (π : Equiv.Perm C7) : Set (C7 → C7) :=
  {δ | ∃ F : Set (Set C7),
    fanoSupportSystem π F ∧
      ∃ B : Set C7, B ∈ F ∧ normalizedLabel π B δ}

private def nonlinearLabels : Set (C7 → C7) :=
  {δ | (∃ π : Equiv.Perm C7,
      nonlinearDevelopmentPermutation π ∧ δ ∈ pointLabels π) ∧
    ¬ scalarLabel δ}

private def nonaffineLabelIncidences :
    Set (Equiv.Perm C7 × (C7 → C7)) :=
  {p | nonlinearDevelopmentPermutation p.1 ∧ p.2 ∈ pointLabels p.1}

/-- Claim 30203: the 588 nonlinear development permutations have seven
translated labels each, yielding 4116 incidences; exactly 84 nonlinear
normalized labels occur, each with multiplicity 49, and no label in this
branch is scalar. -/
def uniformNonlinearLabelIncidence_claim30203 : Prop :=
  Nat.card {π : Equiv.Perm C7 // nonlinearDevelopmentPermutation π} = 588 ∧
    (∀ π : Equiv.Perm C7, nonlinearDevelopmentPermutation π →
      Set.ncard (pointLabels π) = 7 ∧
        ∀ δ ∈ pointLabels π, δ ∈ nonlinearLabels) ∧
      (∀ π : Equiv.Perm C7, nonlinearDevelopmentPermutation π →
        ∀ δ ∈ pointLabels π, ¬ scalarLabel δ) ∧
        Set.ncard nonlinearLabels = 84 ∧
          Set.ncard nonaffineLabelIncidences = 4116 ∧
            ∀ δ ∈ nonlinearLabels,
              Set.ncard
                {π : Equiv.Perm C7 |
                  (π, δ) ∈ nonaffineLabelIncidences} = 49

end

end MathlibPlus.Open.ResearchFormalization.R1144Claim30203
