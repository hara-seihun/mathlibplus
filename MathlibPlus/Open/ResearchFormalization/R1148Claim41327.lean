import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1148Claim41327

noncomputable section

abbrev C7 := ZMod 7

/-- Translation of a subset of the additive cyclic group `C₇`. -/
def translateSet (B : Set C7) (t : C7) : Set C7 :=
  {x | ∃ b ∈ B, x = b + t}

/-- The complete translation development of a subset. -/
def translationDevelopment (B : Set C7) : Set (Set C7) :=
  {C | ∃ t : C7, C = translateSet B t}

/-- Pointwise image of a subset under a point permutation. -/
def pointImage (π : Equiv.Perm C7) (B : Set C7) : Set C7 :=
  π '' B

/-- The normalized label relation for a development-preserving point
permutation. -/
def normalizedDevelopmentLabel
    (B : Set C7) (π δ : Equiv.Perm C7) : Prop :=
  δ 0 = 0 ∧
    ∀ t : C7,
      pointImage π (translateSet B t) =
        translateSet (pointImage π B) (δ t)

/-- The 112 source subsets of sizes two through five. -/
def admissibleSubsets : Set (Set C7) :=
  {B | 2 ≤ B.ncard ∧ B.ncard ≤ 5}

/-- Scalar normalized labels. -/
def scalarLabel (δ : Equiv.Perm C7) : Prop :=
  ∃ a : C7ˣ, ∀ t : C7, δ t = (a : C7) * t

/-- All normalized labels in the complete development census. -/
def normalizedLabels : Set (Equiv.Perm C7) :=
  {δ | ∃ B : Set C7, B ∈ admissibleSubsets ∧
    ∃ π : Equiv.Perm C7, normalizedDevelopmentLabel B π δ}

def nonlinearLabels : Set (Equiv.Perm C7) :=
  {δ | δ ∈ normalizedLabels ∧ ¬ scalarLabel δ}

/-- Subsets supported by a point permutation in the development census. -/
def supportedSubsets (π : Equiv.Perm C7) : Set (Set C7) :=
  {B | B ∈ admissibleSubsets ∧
    ∃ δ : Equiv.Perm C7, normalizedDevelopmentLabel B π δ}

/-- The nonaffine point permutations that support at least one counted
translation development. -/
def affinePoint (π : Equiv.Perm C7) : Prop :=
  ∃ (a : C7ˣ) (b : C7), ∀ x : C7, π x = (a : C7) * x + b

def nonaffinePointPermutations : Set (Equiv.Perm C7) :=
  {π | ¬ affinePoint π ∧ (supportedSubsets π).Nonempty}

/-- The size-three support lines of a supported point permutation. -/
def supportedTriples (π : Equiv.Perm C7) : Set (Set C7) :=
  {B | B ∈ supportedSubsets π ∧ B.ncard = 3}

/-- The labels induced by all supported subsets of a point permutation. -/
def pointLabels (π : Equiv.Perm C7) : Set (Equiv.Perm C7) :=
  {δ | ∃ B ∈ supportedSubsets π,
    normalizedDevelopmentLabel B π δ}

/-- The two cyclic Fano line systems in `C₇`. -/
def fanoA : Set (Set C7) :=
  translationDevelopment ({0, 1, 3} : Set C7)

def fanoB : Set (Set C7) :=
  translationDevelopment ({0, 2, 3} : Set C7)

/-- Complements of all lines in one cyclic Fano system. -/
def lineComplementFamily (F : Set (Set C7)) : Set (Set C7) :=
  {C | ∃ L ∈ F, C = Lᶜ}

/-- The image of a line system under a point permutation. -/
def imageLineSystem
    (π : Equiv.Perm C7) (F : Set (Set C7)) : Set (Set C7) :=
  {G | ∃ L ∈ F, G = π '' L}

/-- Source-system and ordered source/target classes. -/
def sourceSystemClass (F : Set (Set C7)) : Set (Equiv.Perm C7) :=
  {π | π ∈ nonaffinePointPermutations ∧ supportedTriples π = F}

def orderedSystemClass
    (F G : Set (Set C7)) : Set (Equiv.Perm C7) :=
  {π | π ∈ nonaffinePointPermutations ∧ supportedTriples π = F ∧
    imageLineSystem π F = G}

/-- Point-permutation/normalized-label incidences in the nonaffine branch. -/
def nonaffineLabelIncidences :
    Set (Equiv.Perm C7 × Equiv.Perm C7) :=
  {p | p.1 ∈ nonaffinePointPermutations ∧ p.2 ∈ pointLabels p.1}

/-- Claim 41327: the exact nonaffine support, two cyclic-Fano systems,
source/target classes, and nonlinear-label incidence census. -/
def claim41327 : Prop :=
  Fintype.card (Equiv.Perm C7) = 5040 ∧
    Set.ncard fanoA = 7 ∧ Set.ncard fanoB = 7 ∧ fanoA ≠ fanoB ∧
      (∀ F : Set (Set C7), F = fanoA ∨ F = fanoB →
        Set.ncard F = 7 ∧ ∀ L ∈ F, L.ncard = 3) ∧
        (∀ F : Set (Set C7), F = fanoA ∨ F = fanoB →
          Set.ncard (lineComplementFamily F) = 7 ∧
            ∀ C ∈ lineComplementFamily F, C.ncard = 4) ∧
          Set.ncard nonaffinePointPermutations = 588 ∧
            Set.ncard normalizedLabels = 90 ∧
              Set.ncard nonlinearLabels = 84 ∧
                (∀ π ∈ nonaffinePointPermutations,
                  Set.ncard (supportedSubsets π) = 14 ∧
                    Set.ncard (supportedTriples π) = 7 ∧
                      (∃ F G : Set (Set C7),
                        (F = fanoA ∨ F = fanoB) ∧
                          (G = fanoA ∨ G = fanoB) ∧
                            supportedTriples π = F ∧
                              imageLineSystem π F = G ∧
                                supportedSubsets π =
                                  F ∪ lineComplementFamily F) ∧
                      (∀ B ∈ supportedSubsets π,
                        ∀ δ : Equiv.Perm C7,
                          normalizedDevelopmentLabel B π δ →
                            ¬ scalarLabel δ) ∧
                      Set.ncard (pointLabels π) = 7 ∧
                        ∀ δ ∈ pointLabels π, δ ∈ nonlinearLabels) ∧
              Set.ncard (sourceSystemClass fanoA) = 294 ∧
                Set.ncard (sourceSystemClass fanoB) = 294 ∧
                  (∀ F G : Set (Set C7),
                    (F = fanoA ∨ F = fanoB) →
                      (G = fanoA ∨ G = fanoB) →
                        Set.ncard (orderedSystemClass F G) = 147) ∧
                    Set.ncard nonaffineLabelIncidences = 4116 ∧
                      ∀ δ ∈ nonlinearLabels,
                        Set.ncard
                            {π | (π, δ) ∈ nonaffineLabelIncidences} = 49

end

end MathlibPlus.Open.ResearchFormalization.R1148Claim41327
