import Mathlib
import MathlibPlus.Open.GraphTheory.R0943

namespace MathlibPlus.Open.ResearchFormalization.R1536

open MathlibPlus.Open.GraphTheory.R0943

noncomputable section

abbrev V4 := Fin 2 → ZMod 2
abbrev D := Multiplicative V4
abbrev Q8 := QuaternionGroup 2
abbrev ProductCarrier (A : Type*) := A × D

/-- The literal characteristic four-point factor in the product carrier. -/
def literalDFactorCarrier {A : Type*} [Group A] : Set (ProductCarrier A) :=
  {x | x.1 = 1}

def literalDFactorPermutation {A : Type*} [Group A] :
    Subgroup (Equiv.Perm (ProductCarrier A)) :=
  Subgroup.closure
    {p | ∃ d : D,
      p = leftTranslation ((1 : A), d)}

def dBlock {A : Type*} [Group A]
    (a : A) : Set (ProductCarrier A) :=
  {x | x.1 = a}

/-- Stability of the literal D factor under automorphisms of a regular copy. -/
def subgroupAutStable {Ω : Type*}
    (H K : Subgroup (Equiv.Perm Ω)) : Prop :=
  K ≤ H ∧
    ∀ φ : H ≃* H, ∀ h : H,
      ((h : Equiv.Perm Ω) ∈ K ↔
        ((φ h : H) : Equiv.Perm Ω) ∈ K)

/-- Preservation of the common four-point D-block partition. -/
def preservesDBlocks {A : Type*} [Group A]
    (H : Subgroup (Equiv.Perm (ProductCarrier A))) : Prop :=
  ∀ h : H, ∀ a : A, ∃ b : A,
    Set.image (h : Equiv.Perm (ProductCarrier A)) (dBlock a) = dBlock b

/-- The full-V4 synchronization premise: the two regular copies contain the
same characteristic literal D factor and preserve its four-point blocks. -/
def fullV4Synchronization {A : Type*} [Group A]
    (U V : Subgroup (Equiv.Perm (ProductCarrier A))) : Prop :=
  literalDFactorPermutation ≤ U ∧
    literalDFactorPermutation ≤ V ∧
    subgroupAutStable U literalDFactorPermutation ∧
    subgroupAutStable V literalDFactorPermutation ∧
    preservesDBlocks U ∧
    preservesDBlocks V

/-- Identity-free inverse-closed connection sets on the actual A-times-D
carrier. -/
def ordinaryInverseClosed {G : Type*} [Group G] (S : Set G) : Prop :=
  ∀ g : G, g ∈ S ↔ g⁻¹ ∈ S

def ordinaryIdentityFree {G : Type*} [Group G] (S : Set G) : Prop :=
  (1 : G) ∉ S

def ordinaryCayleyPresentation
    {G : Type*} [Group G]
    (S T : Set G) (f : Equiv.Perm G) : Prop :=
  ∀ x y : G, x⁻¹ * y ∈ S ↔ (f x)⁻¹ * f y ∈ T

def identityFiberSection {A : Type*} [Group A]
    (S : Set (ProductCarrier A)) : Set D :=
  {d | (1, d) ∈ S}

def quotientSection {A : Type*} [Group A]
    (S : Set (ProductCarrier A)) (a : A) : Set D :=
  {d | (a, d) ∈ S}

/-- The loopless quotient weight is zero on the identity block regardless of
its internal section; all nonidentity sections retain their actual size. -/
def looplessQuotientWeight {A : Type*} [Fintype A] [DecidableEq A] [Group A]
    (S : Set (ProductCarrier A)) (a : A) : ℕ :=
  if a = 1 then 0 else Nat.card {d : D // d ∈ quotientSection S a}

def looplessSectionData {A : Type*} [Fintype A] [DecidableEq A] [Group A]
    (S : Set (ProductCarrier A)) : Prop :=
  ordinaryIdentityFree S ∧
    ordinaryInverseClosed S ∧
    (∀ a : A, a ≠ 1 → looplessQuotientWeight S a ≤ 4) ∧
    (∀ a : A, a ≠ 1 →
      looplessQuotientWeight S a = looplessQuotientWeight S (a⁻¹))

/-- The actual Cayley-presentation witness, including its two regular copies,
literal characteristic D factor, and quotient action. -/
def actualQuotientImagePresentation
    {A : Type*} [Group A]
    (S T : Set (ProductCarrier A))
    (U V : Subgroup (Equiv.Perm (ProductCarrier A)))
    (f : Equiv.Perm (ProductCarrier A)) (α : A ≃* A) : Prop :=
  f (1 : ProductCarrier A) = 1 ∧
    Set.image f S = T ∧
    (∀ x y : ProductCarrier A,
      x⁻¹ * y ∈ S ↔ (f x)⁻¹ * f y ∈ T) ∧
    (∀ g : Equiv.Perm (ProductCarrier A),
      g ∈ V ↔ ∃ u : Equiv.Perm (ProductCarrier A), u ∈ U ∧
        g = f * u * f⁻¹) ∧
    Set.image f (literalDFactorCarrier) = literalDFactorCarrier ∧
    (∀ a : A, ∀ d : D, (f (a, d)).1 = α a)

/-- The quotient automorphism lifted while keeping the characteristic D
coordinate unchanged. -/
def liftedQuotientAutomorphism {A : Type*} [Group A]
    (α : A ≃* A) : Equiv.Perm (ProductCarrier A) :=
  Equiv.prodCongr α.toEquiv (Equiv.refl D)

/-- Every permutation of the four-point V4 fibre is recorded in affine form. -/
def affineV4Permutation (p : Equiv.Perm D) : Prop :=
  ∃ linear : V4 ≃+ V4, ∃ shift : V4,
    ∀ d : D,
      Multiplicative.toAdd (p d) =
        linear (Multiplicative.toAdd d) + shift

/-- The normalized identity-base affine residual on the actual A-times-D
carrier, with its identity D-fibre fixed pointwise. -/
def normalizedResidual
    {A : Type*} [Group A]
    (π : Q8 →* D)
    (f : Equiv.Perm (ProductCarrier A))
    (α : A ≃* A)
    (r : Equiv.Perm (ProductCarrier A)) : Prop :=
  r = (liftedQuotientAutomorphism α)⁻¹ * f ∧
    (∀ a : A, ∀ d : D, (r (a, d)).1 = a) ∧
    (∀ d : D, r (1, d) = (1, d)) ∧
    (∀ q : Q8, r (1, π q) = (1, π q)) ∧
    ∃ p : A → Equiv.Perm D,
      p 1 = Equiv.refl D ∧
      (∀ a : A, affineV4Permutation (p a)) ∧
      (∀ a : A, ∀ d : D, r (a, d) = (a, p a d))

/-- The preimage of an actual A-times-D connection set through the common
quaternion central-pair quotient. -/
def quaternionConnectionSet {A : Type*} [Group A]
    (π : Q8 →* D) (S : Set (ProductCarrier A)) :
    Set (A × Q8) :=
  {x | (x.1, π x.2) ∈ S}

/-- A pair lift above the residual, with connection-set and Cayley-presentation
compatibility rather than an arbitrary set-theoretic permutation. -/
def quaternionPairLift
    {A : Type*} [Group A]
    (π : Q8 →* D)
    (r : Equiv.Perm (ProductCarrier A))
    (S : Set (ProductCarrier A)) : Prop :=
  ∃ lift : Equiv.Perm (A × Q8),
    (∀ a : A, ∀ q : Q8,
      (lift (a, q)).1 = (r (a, π q)).1 ∧
        π (lift (a, q)).2 = (r (a, π q)).2) ∧
    Set.image lift (quaternionConnectionSet π S) = quaternionConnectionSet π S ∧
    ordinaryCayleyPresentation
      (quaternionConnectionSet π S) (quaternionConnectionSet π S) lift

/-- Regularity of a permutation subgroup on the actual finite product carrier. -/
def regularCopy {Ω : Type*} [Fintype Ω]
    (H : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ x y : Ω, ∃! h : H, (h : Equiv.Perm Ω) x = y

/-- Claim 39028: after the actual-map/full-V4 synchronization, the
identity-base affine residual fixes every derivative-invariant connection set,
including the internal identity fibre; the target is the lifted quotient image,
and the residual lift through quaternion central pairs is presentation-
compatible. -/
def claim39028 : Prop :=
  ∀ {A : Type*} [Fintype A] [DecidableEq A] [CommGroup A],
    Odd (Fintype.card A) →
    ∀ (π : Q8 →* D),
      quaternionProjectionData π →
      ∀ (S T : Set (ProductCarrier A))
        (U V : Subgroup (Equiv.Perm (ProductCarrier A)))
        (f : Equiv.Perm (ProductCarrier A)) (α : A ≃* A),
        regularCopy U →
        regularCopy V →
        looplessSectionData S →
        looplessSectionData T →
        fullV4Synchronization U V →
        actualQuotientImagePresentation S T U V f α →
        ∃ r : Equiv.Perm (ProductCarrier A),
          normalizedResidual π f α r ∧
            derivativeInvariantSet r S ∧
            (∀ E : Set (ProductCarrier A),
              derivativeInvariantSet r E → Set.image r E = E) ∧
            Set.image r S = S ∧
            Set.image f S = T ∧
            T = Set.image (liftedQuotientAutomorphism α) S ∧
            (∀ d : D, (1, d) ∈ S ↔ (1, d) ∈ T) ∧
            quaternionPairLift π r S

end

end MathlibPlus.Open.ResearchFormalization.R1536
