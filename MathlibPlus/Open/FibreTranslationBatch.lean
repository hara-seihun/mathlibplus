import Mathlib

namespace MathlibPlus.Open.FibreTranslation

universe u v

/-- An element of the semidirect product of fibre shifts by base permutations. -/
structure FibreTranslationElement (A : Type u) (B : Type v) where
  shift : B → A
  base : B ≃ B

namespace FibreTranslationElement

variable {A : Type u} {B : Type v} [AddGroup A]

def one : FibreTranslationElement A B :=
  { shift := 0
    base := Equiv.refl B }

def mul (γ δ : FibreTranslationElement A B) : FibreTranslationElement A B :=
  { shift := fun b => δ.shift b + γ.shift (δ.base b)
    base := δ.base.trans γ.base }

def inv (γ : FibreTranslationElement A B) : FibreTranslationElement A B :=
  { shift := fun b => -γ.shift (γ.base.symm b)
    base := γ.base.symm }

/-- The action associated to a shift and its projected base permutation. -/
def act (γ : FibreTranslationElement A B) (x : A × B) : A × B :=
  (x.1 + γ.shift x.2, γ.base x.2)

end FibreTranslationElement

/-- A subgroup of the fibre-translation semidirect product, with its operation
written explicitly so that no ambient semidirect-product convention is hidden. -/
structure FibreTranslationSubgroup (A : Type u) (B : Type v) [AddGroup A] where
  carrier : Set (FibreTranslationElement A B)
  one_mem : FibreTranslationElement.one (A := A) (B := B) ∈ carrier
  mul_mem : ∀ {γ δ}, γ ∈ carrier → δ ∈ carrier →
    FibreTranslationElement.mul γ δ ∈ carrier
  inv_mem : ∀ {γ}, γ ∈ carrier → FibreTranslationElement.inv γ ∈ carrier

/-- The projected subgroup of base permutations. -/
def projectedBase {A : Type u} {B : Type v} [AddGroup A]
    (K : FibreTranslationSubgroup A B) : Set (B ≃ B) :=
  {σ | ∃ γ, γ ∈ K.carrier ∧ γ.base = σ}

/-- Closure conditions for a set of permutations, with the composition order
used by `FibreTranslationElement.mul`. -/
def IsProjectedPermutationSubgroup {B : Type v} (P : Set (B ≃ B)) : Prop :=
  Equiv.refl B ∈ P ∧
    (∀ σ τ, σ ∈ P → τ ∈ P → τ.trans σ ∈ P) ∧
    (∀ σ, σ ∈ P → σ.symm ∈ P)

/-- The projected orbit/component of a basepoint. -/
def projectedComponent {A : Type u} {B : Type v} [AddGroup A]
    (K : FibreTranslationSubgroup A B) (b₀ : B) : Set B :=
  {b | ∃ γ, γ ∈ K.carrier ∧ γ.base b₀ = b}

/-- The orbit of a point under the fibre-translation subgroup. -/
def fibreOrbit {A : Type u} {B : Type v} [AddGroup A]
    (K : FibreTranslationSubgroup A B) (x : A × B) : Set (A × B) :=
  {y | ∃ γ, γ ∈ K.carrier ∧ FibreTranslationElement.act γ x = y}

/-- Chosen component basepoint, holonomy subgroup, transports, and voltage
potential.  The fields constrain the choices to the component and to the
stabilizer voltages appearing in the claim. -/
structure FibreComponentData (A : Type u) (B : Type v) [AddCommGroup A]
    (K : FibreTranslationSubgroup A B) where
  basepoint : B
  carrier : Set B
  carrier_eq : carrier = projectedComponent K basepoint
  holonomy : AddSubgroup A
  holonomy_eq : ∀ h : A,
    h ∈ holonomy ↔
      ∃ γ, γ ∈ K.carrier ∧ γ.base basepoint = basepoint ∧
        γ.shift basepoint = h
  transport : B → FibreTranslationElement A B
  transport_mem : ∀ b, b ∈ carrier → transport b ∈ K.carrier
  transport_base : ∀ b, b ∈ carrier → (transport b).base basepoint = b
  potential : B → A
  potential_eq : ∀ b, b ∈ carrier → potential b = (transport b).shift basepoint

/-- The predicted orbit above a component for a fibre coset representative. -/
def fibreCosetOrbit {A : Type u} {B : Type v} [AddCommGroup A]
    {K : FibreTranslationSubgroup A B} (C : FibreComponentData A B K)
    (r : A) : Set (A × B) :=
  {x | ∃ b h, b ∈ C.carrier ∧ h ∈ C.holonomy ∧
    x = (r + C.potential b + h, b)}

/-- An affine-fibre candidate of the form in Record 4. -/
def affineFibreAct {A : Type u} {B : Type v} [AddCommGroup A]
    (u : A ≃+ A) (s : B → A) (qbar : B ≃ B) (x : A × B) : A × B :=
  (u x.1 + s x.2, qbar x.2)

/-- Setwise preservation of all point-stabilizer orbits. -/
def preservesAllFibreOrbits {A : Type u} {B : Type v} [AddCommGroup A]
    (K : FibreTranslationSubgroup A B) (u : A ≃+ A) (s : B → A)
    (qbar : B ≃ B) : Prop :=
  ∀ x, affineFibreAct u s qbar '' fibreOrbit K x = fibreOrbit K x

/-- The four componentwise conditions in the affine-fibre criterion. -/
def affineFibreOrbitFixationConditions {A : Type u} {B : Type v} [AddCommGroup A]
    {K : FibreTranslationSubgroup A B} (C : FibreComponentData A B K)
    (u : A ≃+ A) (s : B → A) (qbar : B ≃ B) : Prop :=
  qbar '' C.carrier = C.carrier ∧
    u '' (C.holonomy : Set A) = (C.holonomy : Set A) ∧
    (∀ a : A, u a - a ∈ C.holonomy) ∧
    (∀ b, b ∈ C.carrier →
      s b + u (C.potential b) - C.potential (qbar b) ∈ C.holonomy)

/-- Record 2's assertion that transport voltages are well-defined modulo the
component holonomy subgroup. -/
def componentPotentialWellDefined {A : Type u} {B : Type v} [AddCommGroup A]
    {K : FibreTranslationSubgroup A B} (C : FibreComponentData A B K) : Prop :=
  ∀ b, b ∈ C.carrier →
    ∀ γ δ, γ ∈ K.carrier → δ ∈ K.carrier →
      γ.base C.basepoint = b → δ.base C.basepoint = b →
      γ.shift C.basepoint - δ.shift C.basepoint ∈ C.holonomy

/-- Record 2's path choice and holonomy construction. -/
def componentHolonomyPotential {A : Type u} {B : Type v} [AddCommGroup A]
    (K : FibreTranslationSubgroup A B) (C : FibreComponentData A B K) : Prop :=
  C.carrier = projectedComponent K C.basepoint ∧
    (∀ b, b ∈ C.carrier → C.potential b =
      (C.transport b).shift C.basepoint) ∧
    componentPotentialWellDefined C

/-- Record 3's exact orbit-coset classification, including path and closed-path
realization clauses. -/
def exactOrbitCosetClassification {A : Type u} {B : Type v} [AddCommGroup A]
    (K : FibreTranslationSubgroup A B) (C : FibreComponentData A B K) : Prop :=
  (∀ r : A, fibreOrbit K (r, C.basepoint) = fibreCosetOrbit C r) ∧
    (∀ r r' : A,
      fibreOrbit K (r, C.basepoint) = fibreOrbit K (r', C.basepoint) ↔
        r - r' ∈ C.holonomy) ∧
    (∀ b, b ∈ C.carrier → ∀ γ, γ ∈ K.carrier →
      γ.base C.basepoint = b →
      γ.shift C.basepoint - C.potential b ∈ C.holonomy) ∧
    (∀ h, h ∈ C.holonomy → ∃ γ, γ ∈ K.carrier ∧
      γ.base C.basepoint = C.basepoint ∧ γ.shift C.basepoint = h)

/-- Claim 36212: the common fibre is finite abelian, while every subgroup
 element has a base-dependent translation action and the projected image is a
 permutation subgroup. -/
def claim36212 : Prop :=
  ∀ (A : Type u) (B : Type v) [AddCommGroup A] [Fintype A] [Fintype B]
    (K : FibreTranslationSubgroup A B),
    IsProjectedPermutationSubgroup (projectedBase K) ∧
      (∀ γ, γ ∈ K.carrier → ∀ a b,
        FibreTranslationElement.act γ (a, b) =
          (a + γ.shift b, γ.base b))

/-- Claim 36213: chosen component transports define the holonomy subgroup and a
potential whose path choices differ only by holonomy. -/
def claim36213 : Prop :=
  ∀ (A : Type u) (B : Type v) [AddCommGroup A] [Fintype A] [Fintype B]
    (K : FibreTranslationSubgroup A B) (C : FibreComponentData A B K),
    componentHolonomyPotential K C

/-- Claim 36214: the K-orbits above a projected component are precisely the
holonomy cosets, with all path voltages and all closed-path differences present.
-/
def claim36214 : Prop :=
  ∀ (A : Type u) (B : Type v) [AddCommGroup A] [Fintype A] [Fintype B]
    (K : FibreTranslationSubgroup A B) (C : FibreComponentData A B K),
    exactOrbitCosetClassification K C

/-- Claim 36215: an affine-fibre candidate fixes every K-orbit setwise exactly
when the four stated conditions hold on every projected component. -/
def claim36215 : Prop :=
  ∀ (A : Type u) (B : Type v) [AddCommGroup A] [Fintype A] [Fintype B]
    (K : FibreTranslationSubgroup A B) (u : A ≃+ A) (s : B → A)
    (qbar : B ≃ B),
    preservesAllFibreOrbits K u s qbar ↔
      ∀ C : FibreComponentData A B K,
        affineFibreOrbitFixationConditions C u s qbar

/-- Claim 36216: changing two path choices changes the Record 4 congruence by
u(h_b)-h_qbar(b), which remains in the holonomy subgroup. -/
def claim36216 : Prop :=
  ∀ (A : Type u) (B : Type v) [AddCommGroup A] [Fintype A] [Fintype B]
    (K : FibreTranslationSubgroup A B) (C : FibreComponentData A B K)
    (u : A ≃+ A) (s : B → A) (qbar : B ≃ B)
    (t t' : B → A),
    qbar '' C.carrier = C.carrier →
    u '' (C.holonomy : Set A) = (C.holonomy : Set A) →
    (∀ b, b ∈ C.carrier →
      (∃ γ, γ ∈ K.carrier ∧ γ.base C.basepoint = b ∧
        t b = γ.shift C.basepoint) ∧
      (∃ γ, γ ∈ K.carrier ∧ γ.base C.basepoint = b ∧
        t' b = γ.shift C.basepoint)) →
    (∀ b, b ∈ C.carrier → t' b - t b ∈ C.holonomy) ∧
    (∀ b, b ∈ C.carrier →
      (s b + u (t' b) - t' (qbar b)) -
          (s b + u (t b) - t (qbar b)) =
        u (t' b - t b) - (t' (qbar b) - t (qbar b))) ∧
    (∀ b, b ∈ C.carrier →
      u (t' b - t b) - (t' (qbar b) - t (qbar b)) ∈ C.holonomy)

/-- Conditions 2--4 of Record 4, excluding the independent component
alignment condition. -/
def fibreOnlyConditions {A : Type u} {B : Type v} [AddCommGroup A]
    {K : FibreTranslationSubgroup A B} (C : FibreComponentData A B K)
    (u : A ≃+ A) (s : B → A) (qbar : B ≃ B) : Prop :=
  u '' (C.holonomy : Set A) = (C.holonomy : Set A) ∧
    (∀ a : A, u a - a ∈ C.holonomy) ∧
    (∀ b, b ∈ C.carrier →
      s b + u (C.potential b) - C.potential (qbar b) ∈ C.holonomy)

/-- The linear-relation form of the quiet-space solvability condition. -/
def quietLinearSolvability (𝔽 : Type u) (V : Type v) (ι : Type*)
    [Field 𝔽] [AddCommGroup V] [Module 𝔽 V] [Fintype ι]
    (points : ι → V) (rhs : ι → 𝔽) : Prop :=
  (∃ L : V →ₗ[𝔽] 𝔽, ∀ i, L (points i) = rhs i) ↔
    ∀ coeff : ι → 𝔽,
      (∑ i, coeff i • points i = 0) →
        ∑ i, coeff i * rhs i = 0

/-- Claim 36217: prime fibres have only quiet and saturated holonomy, with the
corresponding fibre conditions and the linear-relation solvability test. -/
def claim36217 : Prop :=
  (∀ (p : ℕ) [Fact p.Prime],
    ∀ H : AddSubgroup (ZMod p), H = ⊥ ∨ H = ⊤) ∧
  (∀ (p : ℕ) [Fact p.Prime] (B : Type v) [Fintype B]
      (K : FibreTranslationSubgroup (ZMod p) B)
      (C : FibreComponentData (ZMod p) B K),
    C.holonomy = ⊤ →
      ∀ (u : ZMod p ≃+ ZMod p) (s : B → ZMod p) (qbar : B ≃ B),
        fibreOnlyConditions C u s qbar) ∧
  (∀ (p : ℕ) [Fact p.Prime] (B : Type v) [Fintype B]
      (K : FibreTranslationSubgroup (ZMod p) B)
      (C : FibreComponentData (ZMod p) B K),
    C.holonomy = ⊥ →
      ∀ (u : ZMod p ≃+ ZMod p) (s : B → ZMod p) (qbar : B ≃ B),
        fibreOnlyConditions C u s qbar ↔
          (u = AddEquiv.refl (ZMod p) ∧
            ∀ b, b ∈ C.carrier →
              s b + C.potential b - C.potential (qbar b) = 0)) ∧
  (∀ (p : ℕ) [Fact p.Prime] (V : Type v)
      [AddCommGroup V] [Module (ZMod p) V] (ι : Type*) [Fintype ι]
      (points : ι → V) (rhs : ι → ZMod p),
    quietLinearSolvability (ZMod p) V ι points rhs)

/-- The intermediate subgroup generated by 2 in the additive C4 fibre. -/
def c4IntermediateHolonomy : AddSubgroup (ZMod 4) :=
  AddSubgroup.closure ({(2 : ZMod 4)} : Set (ZMod 4))

/-- Claim 36218: in C4 the proper C2 holonomy is a real parity congruence;
identity quotient alignment can still have a failed fibre lift. -/
def claim36218 : Prop :=
  let H := c4IntermediateHolonomy
  H ≠ (⊥ : AddSubgroup (ZMod 4)) ∧
    H ≠ (⊤ : AddSubgroup (ZMod 4)) ∧
    (∀ x : ZMod 4, x ∈ H ↔ x = 0 ∨ x = 2) ∧
    (AddEquiv.refl (ZMod 4)) '' (H : Set (ZMod 4)) = (H : Set (ZMod 4)) ∧
    (∀ a : ZMod 4, AddEquiv.refl (ZMod 4) a - a ∈ H) ∧
    ¬((1 : ZMod 4) ∈ H)

end MathlibPlus.Open.FibreTranslation
