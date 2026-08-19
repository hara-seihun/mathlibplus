import MathlibPlus.GroupTheory.TwoClosure

namespace MathlibPlus.Open.ResearchFormalization.R1429

noncomputable section

open MathlibPlus.GroupTheory.TwoClosure

/-- The image in the ambient permutation group of a subgroup of a
permutation subgroup. -/
def ambientImage {Ω : Type*}
    (G : Subgroup (Equiv.Perm Ω)) (H : Subgroup G) :
    Subgroup (Equiv.Perm Ω) :=
  Subgroup.map G.subtype H

/-- Conjugation of an ambient image by the displayed permutation. -/
def ambientConjugate {Ω : Type*}
    (G : Subgroup (Equiv.Perm Ω)) (H : Subgroup G)
    (h : Equiv.Perm Ω) : Subgroup (Equiv.Perm Ω) :=
  Subgroup.map (MulAut.conj h).toMonoidHom (ambientImage G H)

/-- Claim 37156: a central subgroup orbit is fixed pointwise by every
point-fixing element of the ordered two-closure. -/
def centralOrbitFixedByTwoClosure_claim37156 : Prop :=
  ∀ {Ω : Type*} [Fintype Ω]
    (G : Subgroup (Equiv.Perm Ω)) (ω : Ω) (D : Subgroup G),
    D ≤ Subgroup.center G →
      ∀ c : Equiv.Perm Ω, inTwoClosure G c → c ω = ω →
        ∀ z ∈ MulAction.orbit D ω, c z = z

/-- Claim 37158: when two regular copies contain a common central subgroup,
every normalized two-closure conjugator fixing the base point fixes the
common central orbit pointwise. -/
def normalizedConjugatorFixesCentralOrbit_claim37158 : Prop :=
  ∀ {Ω : Type*} [Fintype Ω]
    (G : Subgroup (Equiv.Perm Ω)) (ω : Ω)
    (R T D : Subgroup G),
    (∀ a b : Ω, ∃! r : R, ((r : G) : Equiv.Perm Ω) a = b) →
      (∀ a b : Ω, ∃! t : T, ((t : G) : Equiv.Perm Ω) a = b) →
        D ≤ R ∧ D ≤ T ∧ D ≤ Subgroup.center G →
          ∀ h : Equiv.Perm Ω,
            inTwoClosure G h → h ω = ω →
              ambientConjugate G R h = ambientImage G T →
                ∀ z ∈ MulAction.orbit D ω, h z = z

end

end MathlibPlus.Open.ResearchFormalization.R1429
