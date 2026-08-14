import Mathlib

namespace MathlibPlus.Open.Research

namespace AGL4Batch

abbrev Scalar := ZMod 2
abbrev Point := Fin 4 → Scalar
abbrev GL4 := Point ≃ₗ[Scalar] Point
abbrev AGL4 := Point ≃ᵃ[Scalar] Point

/-- The affine realization of a linear automorphism fixing the origin. -/
def linearAffine (g : GL4) : AGL4 :=
  AffineEquiv.mk g.toEquiv g (by
    intro p v
    change g (v + p) = g v + g p
    exact g.map_add v p)

/-- The literal subgroup of translations in the fixed affine action. -/
def translationSubgroup : Subgroup AGL4 :=
  Subgroup.closure (Set.range (fun b : Point => AffineEquiv.vaddConst Scalar b))

/-- Regularity of the action on the sixteen affine points. -/
def regularAffineAction (E : Subgroup AGL4) : Prop :=
  ∀ x y : Point, ∃! e : E, (e : AGL4) x = y

/-- Isomorphism with the additive elementary abelian group of rank four. -/
def elementaryAbelianFour (E : Subgroup AGL4) : Prop :=
  Nonempty (E ≃* Multiplicative Point)

/-- Claim 37511: a literal regular elementary-abelian subgroup before any quotient by conjugacy. -/
def claim37511 (E : Subgroup AGL4) : Prop :=
  elementaryAbelianFour E ∧ regularAffineAction E

/-- The finite set of literal regular subgroups in the fixed natural action. -/
def literalRegularSubgroups : Set (Subgroup AGL4) :=
  {E | claim37511 E}

def conjugationHom (g : AGL4) : AGL4 →* AGL4 :=
  { toFun := fun h => g * h * g⁻¹
    map_one' := by simp
    map_mul' := by
      intro x y
      simp [mul_assoc] }

def conjugateSubgroup (g : GL4) (E : Subgroup AGL4) : Subgroup AGL4 :=
  E.map (conjugationHom (linearAffine g))

def subgroupOrbit (E : Subgroup AGL4) : Set (Subgroup AGL4) :=
  {F | ∃ g : GL4, conjugateSubgroup g E = F}

/-- Claim 37512. -/
noncomputable def claim37512 : Prop :=
  Set.Finite literalRegularSubgroups ∧
    Set.ncard literalRegularSubgroups = 106 ∧
    ∃ N : Subgroup AGL4,
      N ∈ literalRegularSubgroups ∧
      N ≠ translationSubgroup ∧
      Set.Finite (subgroupOrbit translationSubgroup) ∧
      subgroupOrbit translationSubgroup = ({translationSubgroup} : Set (Subgroup AGL4)) ∧
      Set.Finite (subgroupOrbit N) ∧
      Set.ncard (subgroupOrbit N) = 105 ∧
      Disjoint (subgroupOrbit translationSubgroup) (subgroupOrbit N) ∧
      literalRegularSubgroups = subgroupOrbit translationSubgroup ∪ subgroupOrbit N

def RegularGroup := {E : Subgroup AGL4 // E ∈ literalRegularSubgroups}

def rawPairMap : Sym2 RegularGroup → Sym2 (Subgroup AGL4) :=
  Sym2.lift ⟨
    (fun E F => Sym2.mk E.1 F.1),
    (by
      intro E F
      exact (Sym2.eq_iff).2 (Or.inr ⟨rfl, rfl⟩))⟩

noncomputable def pairIntersectionOrder : Sym2 RegularGroup → ℕ :=
  Sym2.lift ⟨
    (fun E F => Nat.card (↥(E.1 ⊓ F.1))),
    (by
      intro E F
      simp [inf_comm])⟩

def intersectionStratum (n : ℕ) : Set (Sym2 RegularGroup) :=
  {p | pairIntersectionOrder p = n}

noncomputable def exactIntersectionStratifiedPairCounts : Prop :=
  Set.Finite (Set.univ : Set (Sym2 RegularGroup)) ∧
    Set.ncard literalRegularSubgroups = 106 ∧
    Set.ncard (intersectionStratum 1) = 2520 ∧
    Set.ncard (intersectionStratum 2) = 2520 ∧
    Set.ncard (intersectionStratum 4) = 525 ∧
    Set.ncard (intersectionStratum 16) = 106 ∧
    ∀ p : Sym2 RegularGroup,
      pairIntersectionOrder p = 1 ∨
        pairIntersectionOrder p = 2 ∨
          pairIntersectionOrder p = 4 ∨ pairIntersectionOrder p = 16

/-- The unordered pair obtained by conjugating both entries simultaneously. -/
def conjugatedRawPair (g : GL4) (p : Sym2 RegularGroup) : Sym2 (Subgroup AGL4) :=
  Sym2.lift ⟨
    (fun E F =>
      Sym2.mk (conjugateSubgroup g E.1) (conjugateSubgroup g F.1)),
    (by
      intro E F
      exact (Sym2.eq_iff).2 (Or.inr ⟨rfl, rfl⟩))⟩ p

def pairOrbit (p : Sym2 RegularGroup) : Set (Sym2 RegularGroup) :=
  {q | ∃ g : GL4, rawPairMap q = conjugatedRawPair g p}

def pairStabilizer (p : Sym2 RegularGroup) : Set GL4 :=
  {g | conjugatedRawPair g p = rawPairMap p}

noncomputable def orbitEntry (p : Sym2 RegularGroup) (S : Set (Sym2 RegularGroup))
    (orbitSize stabilizerSize : ℕ) : Prop :=
  p ∈ S ∧
    Set.ncard (pairOrbit p) = orbitSize ∧
    Set.ncard (pairStabilizer p) = stabilizerSize ∧
    orbitSize * stabilizerSize = Nat.card GL4 ∧
    orbitSize ∣ Nat.card GL4

/-- Claim 37515. -/
noncomputable def claim37515 : Prop :=
  Set.ncard literalRegularSubgroups = 106 ∧
    exactIntersectionStratifiedPairCounts

/-- Claim 37516. -/
noncomputable def claim37516 : Prop :=
  Nat.card GL4 = 20160 ∧
    ∃ p₁ : Sym2 RegularGroup,
      orbitEntry p₁ (intersectionStratum 1) 2520 8 ∧
      pairOrbit p₁ = intersectionStratum 1 ∧
    ∃ p₂₁ p₂₂ : Sym2 RegularGroup,
      orbitEntry p₂₁ (intersectionStratum 2) 1260 16 ∧
      orbitEntry p₂₂ (intersectionStratum 2) 1260 16 ∧
      Disjoint (pairOrbit p₂₁) (pairOrbit p₂₂) ∧
      intersectionStratum 2 = pairOrbit p₂₁ ∪ pairOrbit p₂₂ ∧
    ∃ p₄₁ p₄₂ p₄₃ : Sym2 RegularGroup,
      orbitEntry p₄₁ (intersectionStratum 4) 105 192 ∧
      orbitEntry p₄₂ (intersectionStratum 4) 315 64 ∧
      orbitEntry p₄₃ (intersectionStratum 4) 105 192 ∧
      Disjoint (pairOrbit p₄₁) (pairOrbit p₄₂) ∧
      Disjoint (pairOrbit p₄₁) (pairOrbit p₄₃) ∧
      Disjoint (pairOrbit p₄₂) (pairOrbit p₄₃) ∧
      intersectionStratum 4 = pairOrbit p₄₁ ∪ pairOrbit p₄₂ ∪ pairOrbit p₄₃ ∧
    ∃ p₁₆₁ p₁₆₂ : Sym2 RegularGroup,
      orbitEntry p₁₆₁ (intersectionStratum 16) 1 20160 ∧
      orbitEntry p₁₆₂ (intersectionStratum 16) 105 192 ∧
      Disjoint (pairOrbit p₁₆₁) (pairOrbit p₁₆₂) ∧
      intersectionStratum 16 = pairOrbit p₁₆₁ ∪ pairOrbit p₁₆₂

/-- Claim 37517. -/
noncomputable def claim37517 : Prop :=
  Set.ncard (intersectionStratum 1) = 2520 ∧
    ∀ p q : Sym2 RegularGroup,
      p ∈ intersectionStratum 1 →
      q ∈ intersectionStratum 1 →
      q ∈ pairOrbit p ∧
      Set.ncard (pairStabilizer p) = 8

end AGL4Batch

end MathlibPlus.Open.Research
