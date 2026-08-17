import MathlibPlus.Open.Research.OrbitalCriteria

namespace MathlibPlus.Open.ResearchFormalization.R0992Claim28032

noncomputable section
open scoped BigOperators

abbrev F3 := ZMod 3
abbrev Plane := Fin 2 → F3
abbrev Fibre := Fin 3 → F3
abbrev E := F3 × (Plane × Fibre)

def quadraticQ (x : Plane) : Fibre :=
  ![x 0 * (x 0 - 1), ((2 : F3) * x 0 - 1) * x 1, (x 1) ^ 2]

def coefficientDot (F : Plane → Fibre) (x : Plane) (u : Fibre) : F3 :=
  ∑ i : Fin 3, F x i * u i

def baseTransport : (Plane × Fibre) ≃ (Plane × Fibre) :=
  (Equiv.sigmaEquivProd Plane Fibre).symm.trans
    ((Equiv.sigmaCongrRight
        (fun x : Plane => Equiv.addRight (quadraticQ x))).trans
      (Equiv.sigmaEquivProd Plane Fibre))

def fibreShear (F : Plane → Fibre) :
    ((Plane × Fibre) × F3) ≃ ((Plane × Fibre) × F3) :=
  (Equiv.sigmaEquivProd (Plane × Fibre) F3).symm.trans
    ((Equiv.sigmaCongrRight
        (fun b : Plane × Fibre =>
          Equiv.addRight (coefficientDot F b.1 b.2))).trans
      (Equiv.sigmaEquivProd (Plane × Fibre) F3))

def transporter (F : Plane → Fibre) : Equiv.Perm E :=
  (Equiv.prodComm F3 (Plane × Fibre)).trans
    ((fibreShear F).trans
      ((Equiv.prodCongr baseTransport (Equiv.refl F3)).trans
        (Equiv.prodComm (Plane × Fibre) F3)))

def standardTranslation (v : E) : Equiv.Perm E :=
  Equiv.addRight v

def standardTranslations : Set (Equiv.Perm E) :=
  Set.range standardTranslation

def translationGroup : Subgroup (Equiv.Perm E) :=
  Subgroup.closure standardTranslations

def transportedTranslation (q t : Equiv.Perm E) : Equiv.Perm E :=
  q⁻¹ * t * q

def transportedTranslations (q : Equiv.Perm E) : Set (Equiv.Perm E) :=
  Set.image (fun t => transportedTranslation q t)
    (translationGroup : Set (Equiv.Perm E))

def generatedGroup (q : Equiv.Perm E) : Subgroup (Equiv.Perm E) :=
  Subgroup.closure
    ((translationGroup : Set (Equiv.Perm E)) ∪ transportedTranslations q)

def returnTranslation (q t : Equiv.Perm E) : Equiv.Perm E :=
  standardTranslation (-(transportedTranslation q t 0))

def correctedTranslation (q t : Equiv.Perm E) : Equiv.Perm E :=
  returnTranslation q t * transportedTranslation q t

def pointStabilizerSet (G : Subgroup (Equiv.Perm E)) (α : E) :
    Set (Equiv.Perm E) :=
  {g | g ∈ (G : Set (Equiv.Perm E)) ∧ g α = α}

def basisVector : Fin 6 → E :=
  ![
    (0, (Pi.single 0 1, 0)),
    (0, (Pi.single 1 1, 0)),
    (1, (0, 0)),
    (0, (0, Pi.single 0 1)),
    (0, (0, Pi.single 1 1)),
    (0, (0, Pi.single 2 1))
  ]

def correctedBasisTranslations (q : Equiv.Perm E) : Set (Equiv.Perm E) :=
  Set.range (fun i : Fin 6 =>
    correctedTranslation q (standardTranslation (basisVector i)))

def correctedBasisGroup (q : Equiv.Perm E) : Subgroup (Equiv.Perm E) :=
  Subgroup.closure (correctedBasisTranslations q)

/-- The zero-return translation is composed on the left, so Lean's function
composition applies the transported translation first. -/
def correctedTransportedTranslationsStabilizerSubgroup_claim28032 : Prop :=
  ∀ F : Plane → Fibre,
    let q := transporter F
    let T := translationGroup
    let G := generatedGroup q
    (∀ t : Equiv.Perm E, t ∈ standardTranslations →
      let u := transportedTranslation q t
      let r := returnTranslation q t
      (∃! r' : Equiv.Perm E,
        r' ∈ (T : Set (Equiv.Perm E)) ∧ r' (u 0) = 0) ∧
        r ∈ (T : Set (Equiv.Perm E)) ∧
        r (u 0) = 0 ∧
        r * u ∈ pointStabilizerSet G 0) ∧
    (correctedBasisGroup q : Set (Equiv.Perm E)) ⊆
      pointStabilizerSet G 0 ∧
    (∀ p : Equiv.Perm E,
      MathlibPlus.Open.Research.OrbitalCriteria.fixesStabilizerOrbits p
        (correctedBasisGroup q : Set (Equiv.Perm E)) 0 →
      MathlibPlus.Open.Research.OrbitalCriteria.fixesStabilizerOrbits p
        (G : Set (Equiv.Perm E)) 0)

end
end MathlibPlus.Open.ResearchFormalization.R0992Claim28032
