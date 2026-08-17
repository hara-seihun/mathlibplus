import MathlibPlus.Open.Research.OrbitalCriteria

namespace MathlibPlus.Open.ResearchFormalization.R1181Suborbit

section SimpleSocle

variable {Ω : Type}

/-- Points moved by at least one element of a permutation subgroup. -/
def supportOf (H : Subgroup (Equiv.Perm Ω)) : Set Ω :=
  {x | ∃ h : H, (h : Equiv.Perm Ω) x ≠ x}

/-- Normality of a subgroup inside a permutation subgroup. -/
def normalIn (M G : Subgroup (Equiv.Perm Ω)) : Prop :=
  M ≤ G ∧
    ∀ g : G, ∀ m : M,
      (g : Equiv.Perm Ω) * (m : Equiv.Perm Ω) *
          (g : Equiv.Perm Ω)⁻¹ ∈ M

/-- Nonabelian simplicity for a permutation subgroup. -/
def nonabelianSimpleFactor (T : Subgroup (Equiv.Perm Ω)) : Prop :=
  Nontrivial T ∧
    (¬ ∀ x y : T, x * y = y * x) ∧
      ∀ N : Subgroup T,
        (∀ g : T, ∀ n : N, g * (n : T) * g⁻¹ ∈ N) →
          N = ⊥ ∨ N = ⊤

/-- Internal direct-product data for a finite displayed family of factors. -/
def internalDirectProduct
    (M : Subgroup (Equiv.Perm Ω))
    {r : ℕ} (T : Fin r → Subgroup (Equiv.Perm Ω)) : Prop :=
  (∀ i, T i ≤ M) ∧
    M = ⨆ i, T i ∧
      (∀ i j, i ≠ j → Disjoint (T i) (T j)) ∧
        (∀ i j, i ≠ j →
          ∀ x : Equiv.Perm Ω, x ∈ T i →
            ∀ y : Equiv.Perm Ω, y ∈ T j → Commute x y)

/-- A partition of the point set into nonempty pairwise disjoint blocks. -/
def blockPartition (P : Set (Set Ω)) : Prop :=
  (∀ B, B ∈ P → B.Nonempty) ∧
    (⋃₀ P) = Set.univ ∧
      (∀ ⦃B₁⦄, B₁ ∈ P → ∀ ⦃B₂⦄, B₂ ∈ P →
        B₁ ≠ B₂ → Disjoint B₁ B₂)

/-- A finite family of block-parts partitioning the block partition. -/
def blockPartPartition {r : ℕ}
    (C : Fin r → Set (Set Ω)) (P : Set (Set Ω)) : Prop :=
  (∀ i, C i ⊆ P) ∧
    (⋃ i, C i) = P ∧
      (∀ i j, i ≠ j → Disjoint (C i) (C j))

/-- Transitivity on a specified set. -/
def transitiveOn (H : Subgroup (Equiv.Perm Ω)) (S : Set Ω) : Prop :=
  ∀ ⦃x y : Ω⦄, x ∈ S → y ∈ S →
    ∃ h : H, (h : Equiv.Perm Ω) x = y

/-- Preservation of a block partition. -/
def preservesBlocks (G : Subgroup (Equiv.Perm Ω)) (P : Set (Set Ω)) : Prop :=
  ∀ g : G, ∀ B : Set Ω, B ∈ P →
    ∃ B' : Set Ω, B' ∈ P ∧ (g : Equiv.Perm Ω) '' B = B'

/-- The finite disjoint-support simple-socle setup used by Claims 31929--31930. -/
def disjointSupportSimpleSocleSetup
    {r : ℕ}
    (G M : Subgroup (Equiv.Perm Ω))
    (T : Fin r → Subgroup (Equiv.Perm Ω))
    (P : Set (Set Ω)) (C : Fin r → Set (Set Ω)) : Prop :=
  blockPartition P ∧
    transitiveOn G Set.univ ∧
      preservesBlocks G P ∧
        normalIn M G ∧
          internalDirectProduct M T ∧
            (∀ i, nonabelianSimpleFactor (T i)) ∧
              blockPartPartition C P ∧
                (∀ i, supportOf (T i) = ⋃₀ (C i)) ∧
                  (∀ i, ∀ h : T i, ∀ x,
                    x ∉ supportOf (T i) → (h : Equiv.Perm Ω) x = x) ∧
                    (∀ i, ∀ B, B ∈ C i →
                      ∀ h : T i, (h : Equiv.Perm Ω) '' B = B) ∧
                      (∀ i, ∀ B, B ∈ C i → transitiveOn (T i) B)

/-- An orbit of a point stabilizer. -/
def pointStabilizerOrbit
    (G : Subgroup (Equiv.Perm Ω)) (α x : Ω) : Set Ω :=
  {y | ∃ g : G, (g : Equiv.Perm Ω) α = α ∧
    (g : Equiv.Perm Ω) x = y}

/-- A quotient block orbit under the block stabilizer of `B₀`. -/
def quotientBlockOrbit
    (G : Subgroup (Equiv.Perm Ω)) (_P : Set (Set Ω))
    (B₀ B : Set Ω) : Set (Set Ω) :=
  {B' | ∃ g : G, (g : Equiv.Perm Ω) '' B₀ = B₀ ∧
    (g : Equiv.Perm Ω) '' B = B'}

/-- The family of quotient block orbits. -/
def quotientBlockOrbitFamily
    (G : Subgroup (Equiv.Perm Ω)) (P : Set (Set Ω))
    (B₀ : Set Ω) : Set (Set (Set Ω)) :=
  {O | ∃ B, B ∈ P ∧ O = quotientBlockOrbit G P B₀ B}

/-- The union of the blocks in a quotient orbit. -/
def unionOfBlocks (O : Set (Set Ω)) : Set Ω :=
  {x | ∃ B, B ∈ O ∧ x ∈ B}

/-- The section part over a quotient block orbit. -/
def fixedSectionOver (f : Set Ω → Ω) (O : Set (Set Ω)) : Set Ω :=
  {x | ∃ B, B ∈ O ∧ x = f B}

/-- The complementary part over a quotient block orbit. -/
def complementarySectionOver (f : Set Ω → Ω) (O : Set (Set Ω)) : Set Ω :=
  {x | ∃ B, B ∈ O ∧ x ∈ B \ {f B}}

/-- The complete family of point-stabilizer suborbits. -/
def pointStabilizerOrbits
    (G : Subgroup (Equiv.Perm Ω)) (α : Ω) : Set (Set Ω) :=
  {S | ∃ x, S = pointStabilizerOrbit G α x}

/-- The unique factor supported on the block-part containing `B₀`. -/
def uniqueFactorAt {r : ℕ}
    (C : Fin r → Set (Set Ω)) (i₀ : Fin r) (B₀ : Set Ω) : Prop :=
  B₀ ∈ C i₀ ∧ ∀ i, B₀ ∈ C i → i = i₀

/-- The fixed-section and exact two-orbit hypothesis. -/
def fixedSectionCondition
    (C₀ : Set (Set Ω)) (B₀ : Set Ω) (α : Ω)
    (T₀ : Subgroup (Equiv.Perm Ω))
    (f : Set Ω → Ω) (F : Set Ω) : Prop :=
  α ∈ B₀ ∧
    B₀ ∈ C₀ ∧
      f B₀ = α ∧
        (∀ B, B ∈ C₀ →
          f B ∈ B ∧
            (B \ {f B}).Nonempty ∧
              pointStabilizerOrbit T₀ α (f B) = {f B} ∧
                (∀ x, x ∈ B →
                  x = f B ∨
                    pointStabilizerOrbit T₀ α x = B \ {f B})) ∧
          F = {x | ∃ B, B ∈ C₀ ∧ x = f B}

/-- Image of a family of blocks under a permutation. -/
def blockImage (q : Equiv.Perm Ω) (O : Set (Set Ω)) : Set (Set Ω) :=
  {B' | ∃ B, B ∈ O ∧ q '' B = B'}

/-- Claim 31929: the three displayed families are exactly all point suborbits. -/
def claim31929 {r : ℕ}
    (G M : Subgroup (Equiv.Perm Ω))
    (T : Fin r → Subgroup (Equiv.Perm Ω))
    (P : Set (Set Ω)) (C : Fin r → Set (Set Ω))
    (i₀ : Fin r) (B₀ : Set Ω) (α : Ω)
    (f : Set Ω → Ω) (F : Set Ω) : Prop :=
  (disjointSupportSimpleSocleSetup G M T P C ∧
    uniqueFactorAt C i₀ B₀ ∧
      fixedSectionCondition (C i₀) B₀ α (T i₀) f F) →
    pointStabilizerOrbits G α =
      ({S | ∃ O, O ∈ quotientBlockOrbitFamily G P B₀ ∧
          O ⊆ C i₀ ∧ S = fixedSectionOver f O} ∪
        {S | ∃ O, O ∈ quotientBlockOrbitFamily G P B₀ ∧
          O ⊆ C i₀ ∧ S = complementarySectionOver f O} ∪
        {S | ∃ O, O ∈ quotientBlockOrbitFamily G P B₀ ∧
          Disjoint O (C i₀) ∧ S = unionOfBlocks O})

/-- Claim 31930: a quotient-orbit-fixing transporter preserves every point suborbit. -/
def claim31930 {r : ℕ}
    (G M : Subgroup (Equiv.Perm Ω))
    (T : Fin r → Subgroup (Equiv.Perm Ω))
    (P : Set (Set Ω)) (C : Fin r → Set (Set Ω))
    (i₀ : Fin r) (B₀ : Set Ω) (α : Ω)
    (f : Set Ω → Ω) (F : Set Ω)
    (q : Equiv.Perm Ω) : Prop :=
  (disjointSupportSimpleSocleSetup G M T P C ∧
    uniqueFactorAt C i₀ B₀ ∧
      fixedSectionCondition (C i₀) B₀ α (T i₀) f F ∧
        q α = α ∧
          blockImage q P = P ∧
            blockImage q (C i₀) = C i₀ ∧
              q '' F = F ∧
                (∀ O, O ∈ quotientBlockOrbitFamily G P B₀ →
                  blockImage q O = O)) →
    ∀ S, S ∈ pointStabilizerOrbits G α → q '' S = S

end SimpleSocle

section TwoClosure

variable {Ω : Type}

/-- Claim 31931: the point-suborbit criterion puts the generated-conjugate
transporter in the two-closure. -/
def claim31931 : Prop :=
  ∀ (H : Subgroup (Equiv.Perm Ω)) (q : Equiv.Perm Ω) (α : Ω),
    MathlibPlus.Open.Research.OrbitalCriteria.transitiveSet
      (H : Set (Equiv.Perm Ω)) →
    q α = α →
    let G : Subgroup (Equiv.Perm Ω) :=
      Subgroup.closure
        ((H : Set (Equiv.Perm Ω)) ∪
          MathlibPlus.Open.Research.OrbitalCriteria.conjugateSet q
            (H : Set (Equiv.Perm Ω)))
    MathlibPlus.Open.Research.OrbitalCriteria.fixesStabilizerOrbits q
        (G : Set (Equiv.Perm Ω)) α →
      q ∈ MathlibPlus.Open.Research.OrbitalCriteria.twoClosureOf
        (G : Set (Equiv.Perm Ω))

end TwoClosure

end MathlibPlus.Open.ResearchFormalization.R1181Suborbit
