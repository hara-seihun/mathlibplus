import MathlibPlus.Open.ResearchFormalization.R1144DistinctLabels
import MathlibPlus.Open.ResearchFormalization.R1144FanoCounts30198
import MathlibPlus.Open.ResearchFormalization.R1144Claim30197

namespace MathlibPlus.Open.ResearchFormalization.R1144Claims30196_30204

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

private def translatedLabelRelation
    (π : Equiv.Perm C7) (B : Set C7) (δ : C7 → C7)
    (t s : C7) : Prop :=
  Set.image π (translateSet (translateSet B t) s) =
    translateSet (Set.image π (translateSet B t))
      (translatedLabel δ t s)

private def complementaryLabelRelation
    (π : Equiv.Perm C7) (B : Set C7) (δ : C7 → C7)
    (t s : C7) : Prop :=
  Set.image π (translateSet (translateSet (Set.univ \ B) t) s) =
    translateSet (Set.image π (translateSet (Set.univ \ B) t))
      (translatedLabel δ t s)

/-- Claim 30196: every nonlinear development permutation has exactly one
    source Fano system, whose seven lines and seven complements are its full
    fourteen-set support. -/
def uniqueFanoSupport_claim30196 : Prop :=
  ∀ π : Equiv.Perm C7, nonlinearDevelopmentPermutation π →
    ∃! F : Set (Set C7),
      fanoSupportSystem π F ∧
        Set.ncard (fanoSupportSystemCarrier F) = 14

/-- Claim 30204: the nonlinear development branch is the four ordered Fano
    source-target classes with transported relative labels and uniform
    84-label, 49-fold incidence. -/
def structuredFanoDevelopmentBranch_claim30204 : Prop :=
  Nat.card {π : Equiv.Perm C7 // nonlinearDevelopmentPermutation π} = 588 ∧
    MathlibPlus.Open.ResearchFormalization.R1144Claim30197.claim_30197 ∧
      MathlibPlus.Open.ResearchFormalization.R1144FanoCounts30198.claim30198 ∧
        (∀ π : Equiv.Perm C7, nonlinearDevelopmentPermutation π →
          ∃! F : Set (Set C7), fanoSupportSystem π F ∧
            Set.ncard (fanoSupportSystemCarrier F) = 14) ∧
          (∀ π : Equiv.Perm C7, nonlinearDevelopmentPermutation π →
            ∀ F : Set (Set C7), fanoSupportSystem π F →
              ∀ B : Set C7, B ∈ F →
                ∃ δ : C7 → C7, normalizedLabel π B δ) ∧
            (∀ π : Equiv.Perm C7, nonlinearDevelopmentPermutation π →
              ∀ F : Set (Set C7), fanoSupportSystem π F →
                ∀ B : Set C7, B ∈ F →
                  ∀ δ : C7 → C7, normalizedLabel π B δ →
                    ∀ t s : C7, translatedLabelRelation π B δ t s ∧
                      complementaryLabelRelation π B δ t s ∧
                      ∀ t' : C7, t ≠ t' →
                        translatedLabel δ t ≠ translatedLabel δ t') ∧
              (∀ π : Equiv.Perm C7, nonlinearDevelopmentPermutation π →
                ∀ F : Set (Set C7), fanoSupportSystem π F →
                  ∀ B : Set C7, B ∈ F →
                    ∀ δ : C7 → C7, normalizedLabel π B δ →
                      ¬ scalarLabel δ) ∧
                (∀ π : Equiv.Perm C7,
                  nonlinearDevelopmentPermutation π →
                    Set.ncard (pointLabels π) = 7 ∧
                      ∀ δ ∈ pointLabels π,
                        δ ∈ nonlinearLabels) ∧
                  Set.ncard nonlinearLabels = 84 ∧
                    Set.ncard nonaffineLabelIncidences = 4116 ∧
                      ∀ δ ∈ nonlinearLabels,
                        Set.ncard
                          {π : Equiv.Perm C7 |
                            (π, δ) ∈ nonaffineLabelIncidences} = 49

end

end MathlibPlus.Open.ResearchFormalization.R1144Claims30196_30204
