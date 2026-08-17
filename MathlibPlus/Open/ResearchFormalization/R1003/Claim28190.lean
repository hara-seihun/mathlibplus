import MathlibPlus.Open.ResearchFormalization.R1003Claim28182
import MathlibPlus.Open.ResearchFormalization.R1003Claim28185
import MathlibPlus.Open.ResearchFormalization.R1003Claim28186

namespace MathlibPlus.Open.ResearchFormalization.R1003.Claim28190

noncomputable section

abbrev HCoordinate :=
  MathlibPlus.Open.ResearchFormalization.R1003.Claim28186.HCoordinate
abbrev GCoordinate :=
  MathlibPlus.Open.ResearchFormalization.R1003.Claim28186.GCoordinate
abbrev OmegaH :=
  MathlibPlus.Open.ResearchFormalization.R1003.Claim28186.OmegaH
abbrev Omega :=
  MathlibPlus.Open.ResearchFormalization.R1003.Claim28186.Omega

def zeroProfile : HCoordinate → ZMod 7 :=
  fun _ => 0

def normalizedSupportAtMostOne (t : HCoordinate → ZMod 7) : Prop :=
  t MathlibPlus.Open.ResearchFormalization.R1003.Claim28186.hOne = 0 ∧
    (t = zeroProfile ∨
      MathlibPlus.Open.ResearchFormalization.R1003.Claim28186.nonzeroNormalizedOneSupport t)

def profileCount : Prop :=
  Nat.card {t : HCoordinate → ZMod 7 // normalizedSupportAtMostOne t} = 235

def pairImage {X : Type*} (e : X → X) (R : Set (X × X)) : Set (X × X) :=
  Set.image (fun p : X × X => (e p.1, e p.2)) R

def directedOrbitals : Set (Set (OmegaH × OmegaH)) :=
  {O | ∃ u v : OmegaH, u ≠ v ∧
    O = MathlibPlus.Open.ResearchFormalization.R1003.Claim28186.directedOrbital
      MathlibPlus.Open.ResearchFormalization.R1003.Claim28186.baseGeneratedPair u v}

def baseCoordinateAlpha (g : GCoordinate) : GCoordinate :=
  (g.1, (g.2.1, 3 * g.2.2))

def baseAlphaPointMap (p : OmegaH) : OmegaH :=
  let i := p.1
  let r := (-1 : ZMod 5) ^ i.val * p.2
  let i' := 3 * i
  (MathlibPlus.Open.ResearchFormalization.R1003.Claim28186.basePermutation i',
    (-1 : ZMod 5) ^ i'.val * r)

def alphaPointMap (t : HCoordinate → ZMod 7) (p : Omega) : Omega :=
  let i := p.2.1
  let r := (-1 : ZMod 5) ^ i.val * p.2.2
  let i' := 3 * i
  (p.1 + t (r, i'),
    (MathlibPlus.Open.ResearchFormalization.R1003.Claim28186.basePermutation i',
      (-1 : ZMod 5) ^ i'.val * r))

def alphaHasCorrectLiftedLabelingDirection
    (t : HCoordinate → ZMod 7) : Prop :=
  ∀ g : GCoordinate,
    alphaPointMap t
        (MathlibPlus.Open.ResearchFormalization.R1003.Claim28186.lambda1 g) =
      MathlibPlus.Open.ResearchFormalization.R1003.Claim28186.lambda2 t
        (baseCoordinateAlpha g)

def alphaTransportsEveryPairedOrbital
    (t : HCoordinate → ZMod 7) : Prop :=
  ∀ O : Set (Omega × Omega),
    O ∈ MathlibPlus.Open.ResearchFormalization.R1003.Claim28186.pairedOrbitals
      (MathlibPlus.Open.ResearchFormalization.R1003.Claim28186.generatedPair t) →
      pairImage (alphaPointMap t) O = O

def alphaTransportsEveryPairedFusion
    (t : HCoordinate → ZMod 7) : Prop :=
  ∀ J : Set (Set (Omega × Omega)),
    J ⊆ MathlibPlus.Open.ResearchFormalization.R1003.Claim28186.pairedOrbitals
      (MathlibPlus.Open.ResearchFormalization.R1003.Claim28186.generatedPair t) →
      pairImage (alphaPointMap t) (⋃ O ∈ J, O) = ⋃ O ∈ J, O

def standardBaseDirectedNonconjugacy : Prop :=
  ¬ ∃ τ : Equiv.Perm OmegaH,
      (∀ O : Set (OmegaH × OmegaH), O ∈ directedOrbitals →
        pairImage τ O = O) ∧
      (∀ p : Equiv.Perm OmegaH,
        p ∈ MathlibPlus.Open.ResearchFormalization.R1003.Claim28186.baseP ↔
          τ * p * τ⁻¹ ∈
            MathlibPlus.Open.ResearchFormalization.R1003.Claim28186.baseQ)

def zeroProfileData : Prop :=
  Set.ncard
      (MathlibPlus.Open.ResearchFormalization.R1003.Claim28186.pairedOrbitals
        (MathlibPlus.Open.ResearchFormalization.R1003.Claim28186.generatedPair
          zeroProfile)) = 105 ∧
    alphaHasCorrectLiftedLabelingDirection zeroProfile ∧
    alphaTransportsEveryPairedOrbital zeroProfile ∧
    alphaTransportsEveryPairedFusion zeroProfile

def nonzeroProfileData : Prop :=
  ∀ t : HCoordinate → ZMod 7,
    MathlibPlus.Open.ResearchFormalization.R1003.Claim28186.nonzeroNormalizedOneSupport t →
      alphaHasCorrectLiftedLabelingDirection t ∧
      MathlibPlus.Open.ResearchFormalization.R1003.Claim28186.exact18PairedOrbitalDecomposition t ∧
      alphaTransportsEveryPairedOrbital t ∧
      alphaTransportsEveryPairedFusion t

/-- Claim 28190: for the actual lifted regular pair and its generated action,
translation closure saturates every nonidentity fibre, while the displayed
cubing automorphism transports the complete paired-orbital algebra for all 235
normalized support-at-most-one profiles. -/
def oneFiberTranslationCannotRetainDirectedOrientationDefect_claim28190 : Prop :=
  standardBaseDirectedNonconjugacy ∧
    profileCount ∧
    MathlibPlus.Open.ResearchFormalization.R1003.Claim28182.universalCubingAutomorphism ∧
    MathlibPlus.Open.ResearchFormalization.R1003.Claim28185.rootFixedTranslationSaturation ∧
    zeroProfileData ∧
    nonzeroProfileData

end

end MathlibPlus.Open.ResearchFormalization.R1003.Claim28190
