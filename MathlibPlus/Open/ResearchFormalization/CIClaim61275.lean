import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.CIClaim61275

noncomputable section

/-- Equality of conjugated subgroup images in a quotient, expressed without
choosing quotient representatives: corresponding elements differ by K. -/
def quotientImagesConjugate
    {G : Type*} [Group G]
    (K R T : Subgroup G) (a : G) : Prop :=
  (∀ r : G, r ∈ R →
    ∃ t : G, t ∈ T ∧ (a⁻¹ * r * a)⁻¹ * t ∈ K) ∧
  (∀ t : G, t ∈ T →
    ∃ r : G, r ∈ R ∧ (a⁻¹ * r * a)⁻¹ * t ∈ K)

def transporterSet
    {G : Type*} [Group G]
    (R T : Subgroup G) : Set G :=
  {a | ∀ r : G, r ∈ R ↔ a⁻¹ * r * a ∈ T}

def correctionFiber
    {G : Type*} [Group G]
    (K R T : Subgroup G) (a : G) : Set G :=
  {k | k ∈ K ∧ a * k ∈ transporterSet R T}

abbrev KleinFour := Multiplicative (ZMod 2 × ZMod 2)

def kleinElement (x y : ZMod 2) : KleinFour :=
  Multiplicative.ofAdd (x, y)

def kleinSubgroup (x y : ZMod 2) : Subgroup KleinFour :=
  AddSubgroup.toSubgroup
    (AddSubgroup.closure ({(x, y)} : Set (ZMod 2 × ZMod 2)))

def K₁ : Subgroup KleinFour := kleinSubgroup 1 0
def R₁ : Subgroup KleinFour := kleinSubgroup 0 1
def T₁ : Subgroup KleinFour := kleinSubgroup 1 1

def dihedralK : Subgroup (DihedralGroup 4) :=
  Subgroup.closure ({DihedralGroup.r (2 : ZMod 4)} : Set (DihedralGroup 4))

def dihedralR : Subgroup (DihedralGroup 4) :=
  Subgroup.closure ({DihedralGroup.sr (0 : ZMod 4)} : Set (DihedralGroup 4))

def dihedralT : Subgroup (DihedralGroup 4) :=
  Subgroup.closure
    ({DihedralGroup.r (2 : ZMod 4) * DihedralGroup.sr (0 : ZMod 4)} :
      Set (DihedralGroup 4))

def dihedralQuotientRepresentatives : Finset (DihedralGroup 4) :=
  {1, DihedralGroup.r (1 : ZMod 4), DihedralGroup.sr (0 : ZMod 4),
    DihedralGroup.r (1 : ZMod 4) * DihedralGroup.sr (0 : ZMod 4)}

/-- The two explicit quotient-fibre counterexamples: equality of quotient
images with empty correction fibres in C2^2, and four quotient transporters
with correction sizes 0,0,2,2 in D8. -/
def quotientFibreBoundaryControls_claim61275 : Prop :=
  (∀ a : KleinFour, quotientImagesConjugate K₁ R₁ T₁ a) ∧
    Set.ncard (transporterSet R₁ T₁) = 0 ∧
    (∀ a : KleinFour, correctionFiber K₁ R₁ T₁ a = ∅) ∧
    (∀ a : DihedralGroup 4,
      a ∈ (dihedralQuotientRepresentatives : Set (DihedralGroup 4)) →
        quotientImagesConjugate dihedralK dihedralR dihedralT a) ∧
    dihedralQuotientRepresentatives.card = 4 ∧
    Set.ncard (transporterSet dihedralR dihedralT) = 4 ∧
    (dihedralQuotientRepresentatives.val.map
        (fun a => Set.ncard (correctionFiber dihedralK dihedralR dihedralT a))) =
      ({0, 0, 2, 2} : Multiset ℕ)

end

end MathlibPlus.Open.ResearchFormalization.CIClaim61275
