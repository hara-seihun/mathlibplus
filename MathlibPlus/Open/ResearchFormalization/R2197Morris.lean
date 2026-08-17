import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R2197Morris

noncomputable section

abbrev F3 := ZMod 3
abbrev MorrisBase := Fin 3 → F3
abbrev MorrisFiber := Fin 5 → F3
abbrev MorrisAmbient := MorrisBase × MorrisFiber

/-- The five-coordinate Morris correction fixed by the admitted period-rigidity
statement. -/
def morrisCorrection (w : MorrisBase) : MorrisFiber :=
  ![w 0 * (w 1) ^ 2,
    w 0 * (w 2) ^ 2,
    (w 1) ^ 2 * w 2,
    w 1 * (w 2) ^ 2,
    w 0 * w 1 * w 2]

/-- The displayed Morris shear and its explicit inverse. -/
def morrisShear (x : MorrisAmbient) : MorrisAmbient :=
  (x.1, x.2 + morrisCorrection x.1)

def morrisShearInv (x : MorrisAmbient) : MorrisAmbient :=
  (x.1, x.2 - morrisCorrection x.1)

/-- Translation by an ambient vector. -/
def morrisTranslation (v : MorrisAmbient) : MorrisAmbient → MorrisAmbient :=
  fun x => x + v

/-- A conjugate translation `q⁻¹ τ_v q`, written using the explicit inverse of
 the displayed shear. -/
def morrisConjugatedTranslation (v : MorrisAmbient) :
    MorrisAmbient → MorrisAmbient :=
  fun x => morrisShearInv (morrisShear x + v)

def morrisNaturalTranslationGroup : Set (MorrisAmbient → MorrisAmbient) :=
  Set.range morrisTranslation

def morrisConjugatedTranslationGroup : Set (MorrisAmbient → MorrisAmbient) :=
  Set.range morrisConjugatedTranslation

/-- The vertical fibre subspace in `W × V`. -/
def morrisVertical : Submodule F3 MorrisAmbient :=
  (LinearMap.fst F3 MorrisBase MorrisFiber).ker

/-- The translations whose vectors lie on a specified ambient subspace. -/
def morrisLineTranslations (L : Submodule F3 MorrisAmbient) :
    Set (MorrisAmbient → MorrisAmbient) :=
  {f | ∃ v : L, f = morrisTranslation (v : MorrisAmbient)}

/-- Being common to the natural translation maps and to the conjugated
translation maps. -/
def morrisCommonTranslationLine (L : Submodule F3 MorrisAmbient) : Prop :=
  ∀ f, f ∈ morrisLineTranslations L →
    f ∈ morrisNaturalTranslationGroup ∧
      f ∈ morrisConjugatedTranslationGroup

/-- Claim 43228: among one-dimensional ambient subspaces, the actual common
translation lines are exactly the vertical ones, and their census is 121. -/
def claim43228 : Prop :=
  (∀ L : Submodule F3 MorrisAmbient,
    Module.finrank F3 L = 1 →
      (morrisCommonTranslationLine L ↔ L ≤ morrisVertical)) ∧
  Set.ncard {L : Submodule F3 MorrisAmbient |
    Module.finrank F3 L = 1 ∧ morrisCommonTranslationLine L} = 121

/-- The correction induced in the quotient by a vertical line. -/
def morrisQuotientCorrection
    (L : Submodule F3 MorrisFiber) (w : MorrisBase) : MorrisFiber ⧸ L :=
  Submodule.Quotient.mk (morrisCorrection w)

/-- The finite-difference generators at `b` used for the quotient derivative
span. -/
def morrisDifference
    (L : Submodule F3 MorrisFiber) (a b : MorrisBase) : MorrisFiber ⧸ L :=
  morrisQuotientCorrection L (a + b) -
    morrisQuotientCorrection L a - morrisQuotientCorrection L b

def morrisDifferenceSpan
    (L : Submodule F3 MorrisFiber) (b : MorrisBase) :
    Submodule F3 (MorrisFiber ⧸ L) :=
  Submodule.span F3 (Set.range (fun a : MorrisBase => morrisDifference L a b))

/-- Claim 43229: every one-dimensional vertical quotient in the displayed
Morris witness has the stated linear shadow. -/
def claim43229 : Prop :=
  Set.ncard {L : Submodule F3 MorrisFiber | Module.finrank F3 L = 1} = 121 ∧
    ∀ L : Submodule F3 MorrisFiber,
      Module.finrank F3 L = 1 →
        ∃ shadow : MorrisBase →ₗ[F3] (MorrisFiber ⧸ L),
          ∀ b : MorrisBase,
            shadow b - morrisQuotientCorrection L b ∈ morrisDifferenceSpan L b

/-- A functional level set and the image of that level set under the Morris
shear. -/
def morrisFunctionalLevel
    (φ : MorrisAmbient →ₗ[F3] F3) (r : F3) : Set MorrisAmbient :=
  {x | φ x = r}

def morrisFunctionalImage
    (φ : MorrisAmbient →ₗ[F3] F3) (r : F3) : Set MorrisAmbient :=
  morrisShear '' morrisFunctionalLevel φ r

/-- Restriction of an ambient functional to the fibre factor. -/
def morrisFibreRestriction
    (φ : MorrisAmbient →ₗ[F3] F3) : MorrisFiber →ₗ[F3] F3 :=
  φ.comp (LinearMap.inr F3 MorrisBase MorrisFiber)

/-- The dimension of the affine span of a displayed image. -/
def morrisAffineSpanDimension (S : Set MorrisAmbient) : ℕ :=
  Module.finrank F3 (AffineSubspace.direction (affineSpan F3 S))

def morrisRankSevenHyperplanes : Set (Set MorrisAmbient) :=
  {H | ∃ φ : MorrisAmbient →ₗ[F3] F3,
    φ ≠ 0 ∧ morrisFibreRestriction φ = 0 ∧
      ∃ r : F3, H = morrisFunctionalLevel φ r}

def morrisRankEightHyperplanes : Set (Set MorrisAmbient) :=
  {H | ∃ φ : MorrisAmbient →ₗ[F3] F3,
    φ ≠ 0 ∧ morrisFibreRestriction φ ≠ 0 ∧
      ∃ r : F3, H = morrisFunctionalLevel φ r}

/-- The projective base-normal directions, represented without choices of a
nonzero normal. -/
def morrisProjectiveBaseNormals : Set (Submodule F3 (MorrisBase →ₗ[F3] F3)) :=
  {P | Module.finrank F3 P = 1}

/-- Claim 43230: nonvertical levels have full affine-span dimension, vertical
levels have rank seven and are fixed by the shear, and the resulting affine
census has the stated exact counts. -/
def claim43230 : Prop :=
  (∀ φ : MorrisAmbient →ₗ[F3] F3, φ ≠ 0 →
    (morrisFibreRestriction φ ≠ 0 →
      ∀ r : F3, morrisAffineSpanDimension (morrisFunctionalImage φ r) = 8) ∧
    (morrisFibreRestriction φ = 0 →
      ∀ r : F3,
        morrisAffineSpanDimension (morrisFunctionalImage φ r) = 7 ∧
          morrisFunctionalImage φ r = morrisFunctionalLevel φ r)) ∧
  Set.ncard morrisRankSevenHyperplanes = 39 ∧
  Set.ncard morrisRankEightHyperplanes = 9801 ∧
  Set.ncard morrisProjectiveBaseNormals = 13 ∧
  Fintype.card F3 = 3 ∧
  (∀ H : Set MorrisAmbient, H ∈ morrisRankSevenHyperplanes →
    morrisShear '' H = H)

end
end MathlibPlus.Open.ResearchFormalization.R2197Morris
