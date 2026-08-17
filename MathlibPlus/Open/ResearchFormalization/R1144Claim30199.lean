import MathlibPlus.Combinatorics.Claim30192

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R1144Claim30199

noncomputable section

private abbrev C7 := ZMod 7

private def translateSet (B : Set C7) (t : C7) : Set C7 :=
  {x | ∃ b ∈ B, x = b + t}

private def development (B : Set C7) : Set (Set C7) :=
  {C | ∃ t : C7, C = translateSet B t}

private def affinePointPermutation (π : Equiv.Perm C7) : Prop :=
  ∃ a b : C7, ∀ x : C7, π x = a * x + b

private def nonlinearDevelopmentPermutation (π : Equiv.Perm C7) : Prop :=
  ¬ affinePointPermutation π ∧
    ∃ B : Set C7,
      2 ≤ B.ncard ∧ B.ncard ≤ 5 ∧
      Set.image π '' development B = development (Set.image π B)

private def fanoA : Set (Set C7) :=
  development ({0, 1, 3} : Set C7)

private def fanoB : Set (Set C7) :=
  development ({0, 2, 3} : Set C7)

private def supportedLine (π : Equiv.Perm C7)
    (F : Set (Set C7)) (B : Set C7) : Prop :=
  B ∈ F ∧ Set.image π '' development B = development (Set.image π B)

private def normalizedLabel (π : Equiv.Perm C7)
    (B : Set C7) (δ : C7 → C7) : Prop :=
  δ 0 = 0 ∧
    ∀ s : C7,
      Set.image π (translateSet B s) =
        translateSet (Set.image π B) (δ s)

private def translatedLabel (π : Equiv.Perm C7)
    (B : Set C7) (δ : C7 → C7) (t : C7) : C7 → C7 :=
  fun s => δ (t + s) - δ t

private def labelRelation (π : Equiv.Perm C7)
    (B : Set C7) (δ : C7 → C7) (t s : C7) : Prop :=
  Set.image π (translateSet (translateSet B t) s) =
    translateSet (Set.image π (translateSet B t))
      (translatedLabel π B δ t s)

/-- Claim 30199: every exact supported Fano line has a normalized translate
    label map with delta(0)=0. -/
def normalizedTranslateLabelAction_claim30199 : Prop :=
  ∀ (π : Equiv.Perm C7), nonlinearDevelopmentPermutation π →
    ∀ F : Set (Set C7), (F = fanoA ∨ F = fanoB) →
      ∀ B : Set C7, supportedLine π F B →
        ∃ δ : C7 → C7, normalizedLabel π B δ


end

end MathlibPlus.Open.ResearchFormalization.R1144Claim30199
