import MathlibPlus.Open.ResearchFormalization.R0992Claim28032

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0992Claim28025

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R0992Claim28032
open MathlibPlus.Open.Research.OrbitalCriteria

private def normalizesGroup
    (q : Equiv.Perm E) (G : Subgroup (Equiv.Perm E)) : Prop :=
  ∀ h : Equiv.Perm E,
    h ∈ (G : Set (Equiv.Perm E)) ↔
      q⁻¹ * h * q ∈ (G : Set (Equiv.Perm E))

private abbrev MonomialDirection :=
  Fin 3 × (Fin 3 × (Fin 3 × {e : F3 // e ≠ 0}))

private def monomialTable
    (u v ξ : Fin 3) (ε : F3) : Plane → Fibre :=
  fun x j =>
    if j = ξ then ε * (x 0) ^ u.val * (x 1) ^ v.val else 0

private def monomialTableOf (d : MonomialDirection) : Plane → Fibre :=
  monomialTable d.1 d.2.1 d.2.2.1 d.2.2.2.1

private def monomialTransporter (d : MonomialDirection) : Equiv.Perm E :=
  transporter (monomialTableOf d)

private def monomialGroup (d : MonomialDirection) :
    Subgroup (Equiv.Perm E) :=
  generatedGroup (monomialTransporter d)

private def pairConjugatedBy
    (K : Set (Equiv.Perm E)) (q : Equiv.Perm E) : Prop :=
  ∃ c : Equiv.Perm E,
    c ∈ K ∧
      Set.image (fun h : Equiv.Perm E => c⁻¹ * h * c)
        (translationGroup : Set (Equiv.Perm E)) =
        transportedTranslations q

private noncomputable def exactTwoClosure
    (d : MonomialDirection) : Set (Equiv.Perm E) :=
  twoClosureOf (monomialGroup d : Set (Equiv.Perm E))

private def directTransporterCriterion (d : MonomialDirection) : Prop :=
  let q := monomialTransporter d
  let G := monomialGroup d
  normalizesGroup q G ∧
    fixesStabilizerOrbits q (G : Set (Equiv.Perm E)) 0

private def transporterInTwoClosure (d : MonomialDirection) : Prop :=
  monomialTransporter d ∈ exactTwoClosure d

private def transporterOutsideTwoClosure (d : MonomialDirection) : Prop :=
  monomialTransporter d ∉ exactTwoClosure d

private def alternateClosureConjugator (d : MonomialDirection) : Prop :=
  pairConjugatedBy (exactTwoClosure d) (monomialTransporter d)

private noncomputable def directDirections :
    Finset MonomialDirection :=
  letI := Classical.decEq MonomialDirection
  letI := Classical.propDecidable
  (Finset.univ : Finset MonomialDirection).filter
    directTransporterCriterion

private noncomputable def residualDirections :
    Finset MonomialDirection :=
  letI := Classical.decEq MonomialDirection
  letI := Classical.propDecidable
  (Finset.univ : Finset MonomialDirection).filter
    (fun d => ¬ directTransporterCriterion d)

private def exceptionalMonomialDirection
    (d : MonomialDirection) : Prop :=
  (d.1 = 0 ∧ d.2.1 = 0 ∧ d.2.2.1 = 0) ∨
    (d.1 = 1 ∧ d.2.1 = 0 ∧ d.2.2.1 = 0) ∨
      (d.1 = 0 ∧ d.2.1 = 0 ∧ d.2.2.1 = 1) ∨
        (d.1 = 0 ∧ d.2.1 = 0 ∧ d.2.2.1 = 2)

private noncomputable def exceptionalDirections :
    Finset MonomialDirection :=
  letI := Classical.decEq MonomialDirection
  letI := Classical.propDecidable
  (Finset.univ : Finset MonomialDirection).filter
    exceptionalMonomialDirection

private noncomputable def closureCard
    (d : MonomialDirection) : ℕ :=
  letI := Classical.decEq (Equiv.Perm E)
  letI := Classical.propDecidable
  (Finset.univ.filter
    (fun c : Equiv.Perm E => c ∈ exactTwoClosure d)).card

private def closureIdempotent (d : MonomialDirection) : Prop :=
  twoClosureOf (exactTwoClosure d) = exactTwoClosure d

private noncomputable def closureOrderNineDirections :
    Finset MonomialDirection :=
  letI := Classical.decEq MonomialDirection
  letI := Classical.propDecidable
  residualDirections.filter (fun d => closureCard d = 3 ^ 9)

private noncomputable def closureOrderElevenDirections :
    Finset MonomialDirection :=
  letI := Classical.decEq MonomialDirection
  letI := Classical.propDecidable
  residualDirections.filter (fun d => closureCard d = 3 ^ 11)

private noncomputable def closureOrderThirtyFiveDirections :
    Finset MonomialDirection :=
  letI := Classical.decEq MonomialDirection
  letI := Classical.propDecidable
  residualDirections.filter (fun d => closureCard d = 3 ^ 35)

private noncomputable def transporterInClosureDirections :
    Finset MonomialDirection :=
  letI := Classical.decEq MonomialDirection
  letI := Classical.propDecidable
  residualDirections.filter transporterInTwoClosure

/-- Claim 28025: the exact 54-direction monomial split, including the
    normalizer/suborbit certificates, exceptional closure sizes, and alternate
    conjugators for the eight scalar multiples of `a`, `ia`, `b`, and `c`. -/
def monomialClosureSplit_claim28025 : Prop :=
  (Finset.univ : Finset MonomialDirection).card = 54 ∧
    (∀ d : MonomialDirection,
      ¬ pairConjugatedBy
        (monomialGroup d : Set (Equiv.Perm E))
        (monomialTransporter d)) ∧
      directDirections.card = 16 ∧
        (∀ d ∈ directDirections, transporterInTwoClosure d) ∧
        residualDirections.card = 38 ∧
          (∀ d ∈ residualDirections, closureIdempotent d ∧
            pairConjugatedBy (exactTwoClosure d) (monomialTransporter d) ∧
              (closureCard d = 3 ^ 9 ∨ closureCard d = 3 ^ 11 ∨
                closureCard d = 3 ^ 35)) ∧
            (∀ d ∈ exceptionalDirections, d ∈ residualDirections) ∧
            closureOrderNineDirections.card = 6 ∧
              closureOrderElevenDirections.card = 4 ∧
                closureOrderThirtyFiveDirections.card = 28 ∧
                  transporterInClosureDirections.card = 30 ∧
                    exceptionalDirections.card = 8 ∧
                      (∀ d ∈ exceptionalDirections,
                        transporterOutsideTwoClosure d ∧
                          alternateClosureConjugator d)

end

end MathlibPlus.Open.ResearchFormalization.R0992Claim28025
