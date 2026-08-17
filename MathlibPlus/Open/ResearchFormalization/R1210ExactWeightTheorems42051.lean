import MathlibPlus.Open.ResearchFormalization.R1210SmallProfiles

namespace MathlibPlus.Open.ResearchFormalization.R1210ExactWeightTheorems42051

open MathlibPlus.Open.ResearchFormalization.C7AffineSectionTransporter
open MathlibPlus.Open.ResearchFormalization.R1210SmallProfiles

open scoped BigOperators

noncomputable section

abbrev A7 := C7Vector

/-- The block `B + 2y` in the translation development. -/
def translatedBlock (B : Finset A7) (y : A7) : Finset A7 :=
  B.image (fun b => b + 2 • y)

/-- Incidence relation on the two 49-vertex sides of the translation
 development. -/
def developmentAdj (B : Finset A7) (p q : A7 × Bool) : Prop :=
  (p.2 = false ∧ q.2 = true ∧ q.1 - 2 • p.1 ∈ B) ∨
    (p.2 = true ∧ q.2 = false ∧ p.1 - 2 • q.1 ∈ B)

/-- The side-preserving vertex map determined by the two side permutations. -/
def sideMap (ψ₀ ψ₁ : Equiv.Perm A7) (p : A7 × Bool) : A7 × Bool :=
  if p.2 then (ψ₁ p.1, true) else (ψ₀ p.1, false)

/-- Side-preserving isomorphism of the concrete two-sided development. -/
def sidePreservingDevelopmentIso
    (B C : Finset A7) (ψ₀ ψ₁ : Equiv.Perm A7) : Prop :=
  ∀ p q,
    developmentAdj B p q ↔
      developmentAdj C (sideMap ψ₀ ψ₁ p) (sideMap ψ₀ ψ₁ q)

/-- The development type relation on the exact finite subset carrier. -/
def developmentEquivalent (B C : Finset A7) : Prop :=
  ∃ ψ₀ ψ₁ : Equiv.Perm A7,
    sidePreservingDevelopmentIso B C ψ₀ ψ₁

/-- Affine equivalence under `GL(2,7)` followed by a translation. -/
def affineEquivalent (B C : Finset A7) : Prop :=
  ∃ L : A7 ≃ₗ[ZMod 7] A7, ∃ c : A7,
    C = affineImage L c B

abbrev WeightedSubset (k : ℕ) := {B : Finset A7 // B.card = k}

def affineWeightedRelation (k : ℕ)
    (B C : WeightedSubset k) : Prop :=
  affineEquivalent B.1 C.1

def developmentWeightedRelation (k : ℕ)
    (B C : WeightedSubset k) : Prop :=
  developmentEquivalent B.1 C.1

abbrev AffineType (k : ℕ) := Quot (affineWeightedRelation k)
abbrev DevelopmentType (k : ℕ) := Quot (developmentWeightedRelation k)

/-- The exact number of subsets at a fixed weight. -/
noncomputable def subsetCount (k : ℕ) : ℕ :=
  Nat.card (WeightedSubset k)

/-- The number of affine subset orbits, formed from the literal affine
relation on the weighted finite-subset carrier. -/
noncomputable def affineOrbitCount (k : ℕ) : ℕ :=
  Nat.card (AffineType k)

/-- The number of side-coloured development types, formed from the literal
side-preserving development relation. -/
noncomputable def developmentTypeCount (k : ℕ) : ℕ :=
  Nat.card (DevelopmentType k)

/-- A development type collision is a development type containing two
weighted subsets that are not affine-equivalent. -/
def developmentCollisionType (k : ℕ) (q : DevelopmentType k) : Prop :=
  ∃ B C : WeightedSubset k,
    Quot.mk (developmentWeightedRelation k) B = q ∧
      Quot.mk (developmentWeightedRelation k) C = q ∧
        ¬ affineEquivalent B.1 C.1

/-- The exact number of development types containing a non-affine collision. -/
noncomputable def developmentCollisionCount (k : ℕ) : ℕ :=
  Nat.card {q : DevelopmentType k // developmentCollisionType k q}

/-- The atlas row carrier, retaining every displayed count and its explicit
zero-collision assertion. -/
def exactAtlasRow
    (k subsets affineTypes developmentTypes collisions : ℕ) : Prop :=
  subsetCount k = subsets ∧
    affineOrbitCount k = affineTypes ∧
      developmentTypeCount k = developmentTypes ∧
        developmentCollisionCount k = collisions

/-- Exact ordinary-CI harmlessness for a fixed first nonidentity section
weight, on the reviewed normalized empty/complete-kernel profile carrier. -/
def ordinaryCIHarmlessAt (k : ℕ) : Prop :=
  ∀ (K B C : Finset A7)
    (ψ : Fin 3 → A7 → A7),
    normalizedProfile K B C ψ →
      B.card = k →
        ∃ (L : A7 ≃ₗ[ZMod 7] A7) (c : A7),
          C = affineImage L c B ∧
            extensionAutomorphism (sectionTransport L c) ∧
              (profileConnectionSet K B).image (sectionTransport L c) =
                profileConnectionSet K C

/-- The exact row for weights 8 and 41. -/
def record8 : Prop :=
  exactAtlasRow 8 450978066 4758 4758 0 ∧
    ordinaryCIHarmlessAt 8 ∧ ordinaryCIHarmlessAt 41

/-- The exact row for weights 9 and 40. -/
def record9 : Prop :=
  exactAtlasRow 9 2054455634 21225 21225 0 ∧
    ordinaryCIHarmlessAt 9 ∧ ordinaryCIHarmlessAt 40

/-- The exact row for weights 10 and 39. -/
def record10 : Prop :=
  exactAtlasRow 10 8217822536 84050 84050 0 ∧
    ordinaryCIHarmlessAt 10 ∧ ordinaryCIHarmlessAt 39

/-- The exact row for weights 11 and 38. -/
def record11 : Prop :=
  exactAtlasRow 11 29135916264 296557 296557 0 ∧
    ordinaryCIHarmlessAt 11 ∧ ordinaryCIHarmlessAt 38

/-- The exact row for weights 12 and 37. -/
def record12 : Prop :=
  exactAtlasRow 12 92263734836 937022 937022 0 ∧
    ordinaryCIHarmlessAt 12 ∧ ordinaryCIHarmlessAt 37

/-- The exact row for weights 13 and 36. -/
def record13 : Prop :=
  exactAtlasRow 13 262596783764 2663422 2663422 0 ∧
    ordinaryCIHarmlessAt 13 ∧ ordinaryCIHarmlessAt 36

/-- Claim 42051: each displayed paired section-size theorem retains the
ordinary-CI conclusion, the exact subset/orbit/development counts, and the
literal zero-collision count. -/
def claim42051 : Prop :=
  record8 ∧ record9 ∧ record10 ∧ record11 ∧ record12 ∧ record13

end

end MathlibPlus.Open.ResearchFormalization.R1210ExactWeightTheorems42051
