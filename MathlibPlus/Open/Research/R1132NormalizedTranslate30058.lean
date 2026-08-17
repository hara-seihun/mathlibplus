import MathlibPlus.Open.ResearchFormalization.R1132

namespace MathlibPlus.Open.Research.R1132NormalizedTranslate30058

noncomputable section

abbrev C7 := ZMod 7

private def translateSet (B : Set C7) (t : C7) : Set C7 :=
  {x | ∃ b ∈ B, x = b + t}

private def pointImage (π : Equiv.Perm C7) (B : Set C7) : Set C7 :=
  π '' B

private def translationDevelopment (B : Set C7) : Set (Set C7) :=
  {C | ∃ t : C7, C = translateSet B t}

private def developmentPreserved (B : Set C7) (π : Equiv.Perm C7) : Prop :=
  Set.image (pointImage π) (translationDevelopment B) =
    translationDevelopment (pointImage π B)

private def normalizedTranslateLabel
    (B : Set C7) (π δ : Equiv.Perm C7) : Prop :=
  δ 0 = 0 ∧
    ∀ t : C7,
      pointImage π (translateSet B t) =
        translateSet (pointImage π B) (δ t)

/-- Claim 30058: for a proper small subset development in C₇, the label
permutation normalized at zero is uniquely determined by the development
transport. -/
def claim30058_uniqueNormalizedTranslateLabel : Prop :=
  ∀ (B : Set C7) (π : Equiv.Perm C7),
    2 ≤ B.ncard → B.ncard ≤ 5 →
      developmentPreserved B π →
        ∃! δ : Equiv.Perm C7,
          normalizedTranslateLabel B π δ

end

end MathlibPlus.Open.Research.R1132NormalizedTranslate30058
