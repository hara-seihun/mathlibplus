import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.Profile410

private abbrev Ω := ZMod 4 × ZMod 7
private abbrev Profile := ZMod 4 → (ZMod 7)ˣ

private def next4 (i : ZMod 4) : ZMod 4 :=
  i + 1

private def ratio (v : Profile) (i : ZMod 4) : (ZMod 7)ˣ :=
  v (next4 i) / v i

private def fiberwise (F : ZMod 4 → Equiv.Perm (ZMod 7)) : Equiv.Perm Ω :=
  let e := Equiv.sigmaEquivProd (ZMod 4) (ZMod 7)
  (e.symm.trans (Equiv.sigmaCongrRight F)).trans e

private def pPerm : Equiv.Perm Ω :=
  Equiv.prodCongr (Equiv.refl (ZMod 4)) (Equiv.addRight 1)

private def sPerm : Equiv.Perm Ω :=
  Equiv.prodCongr (Equiv.addRight 1) (Equiv.refl (ZMod 7))

private def qPerm (v : Profile) : Equiv.Perm Ω :=
  fiberwise (fun i => Equiv.addRight (v i : ZMod 7))

private def tPerm (v : Profile) : Equiv.Perm Ω :=
  (fiberwise (fun i => Units.mulRight (ratio v i))).trans sPerm

private def standardGroup : Subgroup (Equiv.Perm Ω) :=
  Subgroup.closure ({pPerm * sPerm} : Set (Equiv.Perm Ω))

private def profileGroup (v : Profile) : Subgroup (Equiv.Perm Ω) :=
  Subgroup.closure ({qPerm v * tPerm v} : Set (Equiv.Perm Ω))

private def regularOn (R : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ x y : Ω, ∃! g : R, g.1 x = y

private def generatedGroup (v : Profile) : Subgroup (Equiv.Perm Ω) :=
  Subgroup.closure ((standardGroup : Set (Equiv.Perm Ω)) ∪
    (profileGroup v : Set (Equiv.Perm Ω)))

private def conjugateInsideGenerated (v : Profile) : Prop :=
  ∃ g : generatedGroup v,
    Subgroup.map (MulAut.conj (g.1)⁻¹).toMonoidHom standardGroup =
      profileGroup v

private def normalizedProfile (v : Profile) : Prop :=
  v 0 = 1

private def scaled (c : (ZMod 7)ˣ) (v : Profile) : Profile :=
  fun i => c * v i

private def quadraticResidues : Set (ZMod 7) :=
  {1, 2, 4}

private def allQuadratic (v : Profile) : Prop :=
  ∀ i, (v i : ZMod 7) ∈ quadraticResidues

private def squareProduct (v : Profile) : Prop :=
  (∏ i : ZMod 4, (v i : ZMod 7)) ∈ quadraticResidues

/-- The standard and full-support profile copies are regular cyclic groups of
    order 28 on the explicit Z/4×F₇ carrier. -/
def claim41092 : Prop :=
  ∀ v : Profile,
    regularOn standardGroup ∧ regularOn (profileGroup v) ∧
      Nat.card standardGroup = 28 ∧ Nat.card (profileGroup v) = 28

/-- Projective scaling leaves the profile group unchanged, and normalized
    full-support profiles are exactly the 6³ representatives. -/
def claim41093 : Prop :=
  (∀ (c : (ZMod 7)ˣ) (v : Profile),
    profileGroup (scaled c v) = profileGroup v) ∧
  (∀ v : Profile, ∃! w : Profile,
    normalizedProfile w ∧ ∃ c : (ZMod 7)ˣ, w = scaled c v) ∧
  Nat.card {v : Profile // normalizedProfile v} = 6 ^ 3

/-- In a normalized profile, generated-group conjugacy is exactly the
    coordinatewise quadratic-residue condition. -/
def claim41095 : Prop :=
  ∀ v : Profile, normalizedProfile v →
    (conjugateInsideGenerated v ↔ allQuadratic v)

/-- The normalized profile counts retain generated-group conjugacy rather
    than replacing it by the residue predicate. -/
def claim41097 : Prop :=
  Nat.card {v : Profile // normalizedProfile v} = 216 ∧
    Nat.card {v : {v : Profile // normalizedProfile v} //
      conjugateInsideGenerated v.1} = 27 ∧
    Nat.card {v : {v : Profile // normalizedProfile v} //
      ¬conjugateInsideGenerated v.1} = 189 ∧
    Nat.card {v : {v : Profile // normalizedProfile v} //
      squareProduct v.1 ∧ ¬conjugateInsideGenerated v.1} = 81 ∧
    ∃ v : Profile,
      normalizedProfile v ∧ squareProduct v ∧ ¬conjugateInsideGenerated v

end MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.Profile410
