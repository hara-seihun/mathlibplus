import MathlibPlus.Open.ResearchFormalization.R1132

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R1132NormalizedLabelCensus30060

noncomputable section

abbrev C7 := ZMod 7

def translateSet (B : Set C7) (t : C7) : Set C7 :=
  {x | ∃ b ∈ B, x = b + t}

def pointImage (π : Equiv.Perm C7) (B : Set C7) : Set C7 :=
  π '' B

def translationDevelopment (B : Set C7) : Set (Set C7) :=
  {C | ∃ t : C7, C = translateSet B t}

def developmentPreserved (B : Set C7) (π : Equiv.Perm C7) : Prop :=
  Set.image (pointImage π) (translationDevelopment B) =
    translationDevelopment (pointImage π B)

def normalizedTranslateLabel
    (B : Set C7) (π δ : Equiv.Perm C7) : Prop :=
  δ 0 = 0 ∧
    ∀ t : C7,
      pointImage π (translateSet B t) =
        translateSet (pointImage π B) (δ t)

def scalarLabel (δ : Equiv.Perm C7) : Prop :=
  ∃ a : C7ˣ, ∀ t : C7, δ t = (a : C7) * t

def normalizedLabels : Set (Equiv.Perm C7) :=
  {δ | ∃ B : Set C7, ∃ π : Equiv.Perm C7,
    2 ≤ B.ncard ∧ B.ncard ≤ 5 ∧
      developmentPreserved B π ∧
      normalizedTranslateLabel B π δ}

def scalarLabels : Set (Equiv.Perm C7) :=
  {δ | δ ∈ normalizedLabels ∧ scalarLabel δ}

def nonlinearLabels : Set (Equiv.Perm C7) :=
  {δ | δ ∈ normalizedLabels ∧ ¬ scalarLabel δ}

/-- Claim 30060: the normalized label carrier has exactly the six scalar and
84 nonlinear maps, for a total of ninety. -/
def claim30060 : Prop :=
  Set.ncard normalizedLabels = 90 ∧
    Set.ncard scalarLabels = 6 ∧
      Set.ncard nonlinearLabels = 84 ∧
        normalizedLabels = scalarLabels ∪ nonlinearLabels ∧
          Disjoint (scalarLabels : Set (Equiv.Perm C7)) nonlinearLabels

/-- Claim 30061: affine/scalar rigidity fails, with the exact nonlinear count. -/
def claim30061 : Prop :=
  Set.ncard nonlinearLabels = 84 ∧
    ¬(∀ δ : Equiv.Perm C7, δ ∈ normalizedLabels → scalarLabel δ)

end

end MathlibPlus.Open.ResearchFormalization.R1132NormalizedLabelCensus30060
