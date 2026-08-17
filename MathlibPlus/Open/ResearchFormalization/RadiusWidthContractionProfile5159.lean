import MathlibPlus.Open.ResearchFormalization.KernelSupportSurvivalD0084

namespace MathlibPlus.Open.ResearchFormalization

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The exact finite block certificate whose arity is minimized in the
radius-width contraction. -/
def radiusWidthCertificate5159
    {𝔽 R V B : Type*} [Field 𝔽] [Fintype R] [Fintype V] [Fintype B]
    (M : Matrix R V 𝔽) (rowBlock : R → B) (core : Finset V)
    (r : Nat) (columns : Finset V) (v : V) (blocks : Finset B) : Prop :=
  blocks ⊆ radiusBlockBall M rowBlock core r v ∧
    ∃ c : R → 𝔽,
      (∀ i, i ∉ rowsInBlocks rowBlock blocks → c i = 0) ∧
        (∀ u, u ∈ columns →
          u ∈ radiusColumnBall M rowBlock core r v →
            (∑ i : R, c i * M i u) = if u = v then 1 else 0)

/-- The `WithTop ℕ` minimum of the block-certificate cardinalities, with top
when no certificate exists. -/
noncomputable def radiusWidthArity5159
    {𝔽 R V B : Type*} [Field 𝔽] [Fintype R] [Fintype V] [Fintype B]
    (M : Matrix R V 𝔽) (rowBlock : R → B) (core : Finset V)
    (r : Nat) (columns : Finset V) (v : V) : WithTop Nat :=
  let P : Nat → Prop := fun n =>
    ∃ blocks : Finset B,
      radiusWidthCertificate5159 M rowBlock core r columns v blocks ∧
        blocks.card = n
  if h : ∃ n, P n then (Nat.find h : WithTop Nat) else ⊤

/-- Finite-arity exposure, expressed by the exact minimum certificate arity. -/
def radiusWidthArityExposed5159
    {𝔽 R V B : Type*} [Field 𝔽] [Fintype R] [Fintype V] [Fintype B]
    (M : Matrix R V 𝔽) (rowBlock : R → B) (core : Finset V)
    (r k : Nat) (columns : Finset V) (v : V) : Prop :=
  columns ⊆ core ∧ v ∈ columns ∧
    radiusWidthArity5159 M rowBlock core r columns v ≤ (k : WithTop Nat)

/-- One simultaneous finite-arity peeling round. -/
def radiusWidthArityPeelRound5159
    {𝔽 R V B : Type*} [Field 𝔽] [Fintype R] [Fintype V] [Fintype B]
    (M : Matrix R V 𝔽) (rowBlock : R → B) (core : Finset V)
    (r k : Nat) (columns : Finset V) : Finset V :=
  columns.filter (fun v =>
    ¬ radiusWidthArityExposed5159 M rowBlock core r k columns v)

/-- A finite iteration of the arity-constrained radius peeling. -/
def iterateRadiusWidthArityPeeling5159
    {𝔽 R V B : Type*} [Field 𝔽] [Fintype R] [Fintype V] [Fintype B]
    (M : Matrix R V 𝔽) (rowBlock : R → B) (core : Finset V)
    (r k : Nat) : Nat → Finset V → Finset V
  | 0, columns => columns
  | n + 1, columns =>
      iterateRadiusWidthArityPeeling5159 M rowBlock core r k n
        (radiusWidthArityPeelRound5159 M rowBlock core r k columns)

/-- The finite-arity terminal carrier `Core_(r,k)`. -/
def radiusWidthCore5159
    {𝔽 R V B : Type*} [Field 𝔽] [Fintype R] [Fintype V] [Fintype B]
    (M : Matrix R V 𝔽) (rowBlock : R → B) (r k : Nat) : Finset V :=
  iterateRadiusWidthArityPeeling5159 M rowBlock (atomicCore M rowBlock) r k
    (Fintype.card V + 1) (atomicCore M rowBlock)

/-- Width exposure with the explicit unrestricted-radius branch at infinity. -/
def radiusWidthExposedTop5159
    {𝔽 R V B : Type*} [Field 𝔽] [Fintype R] [Fintype V] [Fintype B]
    (M : Matrix R V 𝔽) (rowBlock : R → B) (core : Finset V)
    (r : Nat) (k : WithTop Nat) (columns : Finset V) (v : V) : Prop :=
  match k with
  | ⊤ => radiusExposed M rowBlock core r columns v
  | (n : Nat) => radiusWidthArityExposed5159 M rowBlock core r n columns v

/-- The radius-width core at a finite width or at unrestricted width. -/
def radiusWidthCoreTop5159
    {𝔽 R V B : Type*} [Field 𝔽] [Fintype R] [Fintype V] [Fintype B]
    (M : Matrix R V 𝔽) (rowBlock : R → B)
    (r : Nat) (k : WithTop Nat) : Finset V :=
  match k with
  | ⊤ => radiusCore M rowBlock r
  | (n : Nat) => radiusWidthCore5159 M rowBlock r n

/-- A stalled set for the same finite-width or unrestricted-width exposure. -/
def radiusWidthStalledTop5159
    {𝔽 R V B : Type*} [Field 𝔽] [Fintype R] [Fintype V] [Fintype B]
    (M : Matrix R V 𝔽) (rowBlock : R → B) (core : Finset V)
    (r : Nat) (k : WithTop Nat) (columns : Finset V) : Prop :=
  columns ⊆ core ∧
    ∀ v, v ∈ columns →
      ¬ radiusWidthExposedTop5159 M rowBlock core r k columns v

/-- Radius-width contraction profile: the arity-constrained process has a
canonical largest stalled terminal set, is decreasing in radius and width,
and its explicit infinity branch is the unrestricted radius core. -/
def claim5159_radiusWidthContractionProfile : Prop :=
  ∀ (𝔽 R V B : Type*) [Field 𝔽] [Fintype R] [Fintype V] [Fintype B]
    (M : Matrix R V 𝔽) (rowBlock : R → B),
    (∀ (r : Nat) (k : WithTop Nat), 1 ≤ r → 1 ≤ k →
      radiusWidthStalledTop5159 M rowBlock (atomicCore M rowBlock) r k
        (radiusWidthCoreTop5159 M rowBlock r k)) ∧
    (∀ (r : Nat) (k : WithTop Nat) (S : Finset V),
      1 ≤ r → 1 ≤ k →
      radiusWidthStalledTop5159 M rowBlock (atomicCore M rowBlock) r k S →
        S ⊆ radiusWidthCoreTop5159 M rowBlock r k) ∧
    (∀ (r₁ r₂ : Nat) (k : WithTop Nat),
      1 ≤ r₁ → r₁ ≤ r₂ → 1 ≤ k →
        radiusWidthCoreTop5159 M rowBlock r₂ k ⊆
          radiusWidthCoreTop5159 M rowBlock r₁ k) ∧
    (∀ (r : Nat) (k₁ k₂ : WithTop Nat),
      1 ≤ r → 1 ≤ k₁ → k₁ ≤ k₂ →
        radiusWidthCoreTop5159 M rowBlock r k₂ ⊆
          radiusWidthCoreTop5159 M rowBlock r k₁) ∧
    (∀ r : Nat, 1 ≤ r →
      radiusWidthCoreTop5159 M rowBlock r ⊤ = radiusCore M rowBlock r)

end

end MathlibPlus.Open.ResearchFormalization
