import MathlibPlus.Combinatorics.Claim30063OffsetDerivativeSignature

namespace MathlibPlus.Open.ResearchFormalization.R1132

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

private def scalarLabel (δ : Equiv.Perm C7) : Prop :=
  ∃ a : C7ˣ, ∀ t : C7, δ t = (a : C7) * t

private def normalizedLabels : Set (Equiv.Perm C7) :=
  {δ | ∃ B : Set C7, ∃ π : Equiv.Perm C7,
    2 ≤ B.ncard ∧ B.ncard ≤ 5 ∧
      developmentPreserved B π ∧
      normalizedTranslateLabel B π δ}

private def nonlinearLabels : Set (Equiv.Perm C7) :=
  {δ | δ ∈ normalizedLabels ∧ ¬ scalarLabel δ}

private def affinePoint (π : Equiv.Perm C7) : Prop :=
  ∃ a : C7ˣ, ∃ b : C7, ∀ x : C7,
    π x = (a : C7) * x + b

private def admittedSubsets (π : Equiv.Perm C7) : Set (Set C7) :=
  {B | 2 ≤ B.ncard ∧ B.ncard ≤ 5 ∧ developmentPreserved B π}

private def nonaffineSupportedPoints : Set (Equiv.Perm C7) :=
  {π | ¬ affinePoint π ∧ (admittedSubsets π).Nonempty}

private def translateOrbit (B : Set C7) : Set (Set C7) :=
  {C | ∃ t : C7, C = translateSet B t}

private def complementOrbit (B : Set C7) : Set (Set C7) :=
  {C | ∃ t : C7, C = (translateSet B t)ᶜ}

/-- Claim 30065: the 84 nonlinear normalized label maps have pairwise
    distinct offset-derivative signatures. -/
def claim30065 : Prop :=
  Set.ncard nonlinearLabels = 84 ∧
    ∀ δ ∈ nonlinearLabels, ∀ v v' : C7,
      MathlibPlus.Combinatorics.offsetDerivativeSignature_claim30063 δ v =
          MathlibPlus.Combinatorics.offsetDerivativeSignature_claim30063 δ v' →
        v = v'

/-- Claim 30066: the nonaffine development-preserving point branch has the
    exact 588-point and fourteen-subset support census. -/
def claim30066 : Prop :=
  Set.ncard nonaffineSupportedPoints = 588 ∧
    ∀ π ∈ nonaffineSupportedPoints,
      Set.ncard (admittedSubsets π) = 14 ∧
        ∃ B : Set C7,
          B.ncard = 3 ∧
          admittedSubsets π = translateOrbit B ∪ complementOrbit B ∧
          Set.ncard (translateOrbit B) = 7 ∧
          Set.ncard (complementOrbit B) = 7 ∧
          (∀ C ∈ translateOrbit B, C.ncard = 3) ∧
          (∀ C ∈ complementOrbit B, C.ncard = 4)

/-- Claim 30067: no point in the nonaffine support branch induces a scalar
    normalized label on any of its admitted subsets. -/
def claim30067 : Prop :=
  Set.ncard nonaffineSupportedPoints = 588 ∧
    ∀ π ∈ nonaffineSupportedPoints,
      ∀ B ∈ admittedSubsets π, ∀ δ : Equiv.Perm C7,
        normalizedTranslateLabel B π δ →
          ¬ scalarLabel δ

end

end MathlibPlus.Open.ResearchFormalization.R1132
