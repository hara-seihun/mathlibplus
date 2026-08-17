import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1148Claim41326

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

/-- A normalized label permutation for a development isomorphism. -/
def normalizedDevelopmentLabel
    (B : Set C7) (π δ : Equiv.Perm C7) : Prop :=
  δ 0 = 0 ∧
    ∀ t : C7,
      pointImage π (translateSet B t) =
        translateSet (pointImage π B) (δ t)

/-- The 112 subsets whose sizes lie between two and five. -/
def admissibleSubsets : Set (Set C7) :=
  {B | 2 ≤ B.ncard ∧ B.ncard ≤ 5}

/-- A counted translation-development isomorphism instance is a source
subset/permutation pair admitting its normalized induced label. -/
def developmentIsomorphismInstances :
    Set (Set C7 × Equiv.Perm C7) :=
  {i | i.1 ∈ admissibleSubsets ∧
    ∃ δ : Equiv.Perm C7, normalizedDevelopmentLabel i.1 i.2 δ}

/-- The affine image of a subset under `x ↦ a*x+b`. -/
def affineImage (a : C7ˣ) (b : C7) (B : Set C7) : Set C7 :=
  {x | ∃ y ∈ B, x = (a : C7) * y + b}

/-- Scalar normalized label maps. -/
def scalarLabel (δ : Equiv.Perm C7) : Prop :=
  ∃ a : C7ˣ, ∀ t : C7, δ t = (a : C7) * t

/-- All normalized labels occurring in the counted developments. -/
def normalizedLabels : Set (Equiv.Perm C7) :=
  {δ | ∃ B : Set C7, B ∈ admissibleSubsets ∧
    ∃ π : Equiv.Perm C7, normalizedDevelopmentLabel B π δ}

/-- The scalar and nonlinear parts of the normalized-label census. -/
def scalarLabels : Set (Equiv.Perm C7) :=
  {δ | δ ∈ normalizedLabels ∧ scalarLabel δ}

def nonlinearLabels : Set (Equiv.Perm C7) :=
  {δ | δ ∈ normalizedLabels ∧ ¬ scalarLabel δ}

/-- The seven-offset signature of a normalized label. -/
def offsetSignature (δ : Equiv.Perm C7) (v : C7) : C7 → C7 :=
  fun w => δ (v + 2 • w) - δ v

/-- Claim 41326: the exact `C₇` translation-development census, affine
subset-image conclusion, normalized-label counts, and nonlinear signature
injectivity. -/
def claim41326 : Prop :=
  Fintype.card (Equiv.Perm C7) = 5040 ∧
    Set.ncard admissibleSubsets = 112 ∧
      Set.ncard developmentIsomorphismInstances = 12936 ∧
        (∀ (B : Set C7) (π : Equiv.Perm C7),
          (B, π) ∈ developmentIsomorphismInstances →
            ∃ (a : C7ˣ) (b : C7), affineImage a b B = pointImage π B) ∧
          Set.ncard normalizedLabels = 90 ∧
            Set.ncard scalarLabels = 6 ∧
              Set.ncard nonlinearLabels = 84 ∧
                ∀ δ ∈ nonlinearLabels,
                  Function.Injective (offsetSignature δ)

end

end MathlibPlus.Open.ResearchFormalization.R1148Claim41326
