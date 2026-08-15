import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatch_01a003d5

open scoped BigOperators

/-- The coordinate vector indexed by `s`. -/
def coordinateVector {F S : Type*} [Field F] [DecidableEq S] (s : S) : S → F :=
  Pi.single s 1

/-- An explicit monomial presentation of a surjective coordinate quotient. -/
def MonomialCoordinatePresentation
    {F S Q K : Type*} [Field F] [AddCommGroup Q] [Module F Q]
    [DecidableEq S] (π : (S → F) →ₗ[F] Q) (E : Module.Basis K F Q) : Prop :=
  Function.Surjective π ∧
    ∀ s : S,
      π (coordinateVector s) = 0 ∨
        ∃ (η : F) (k : K),
          η ≠ 0 ∧ π (coordinateVector s) = η • E k

/-- Claim 5719: a monomial quotient colors coordinates by basis lines and records gains. -/
def monomialQuotientGainColoringClaim
    {F S Q : Type*} [Field F] [AddCommGroup Q] [Module F Q]
    [DecidableEq S] (π : (S → F) →ₗ[F] Q) : Prop :=
  ∃ (K : Type*) (E : Module.Basis K F Q), MonomialCoordinatePresentation π E

/-- The relations supplied by zero coordinates and by two coordinates on one basis line. -/
def monomialRelationGenerators
    {F S Q K : Type*} [Field F] [AddCommGroup Q] [Module F Q]
    [DecidableEq S] (π : (S → F) →ₗ[F] Q) (E : Module.Basis K F Q) : Set (S → F) :=
  {v | ∃ s : S, v = coordinateVector s ∧ π (coordinateVector s) = 0} ∪
    {v |
      ∃ (s t : S) (ηs ηt : F) (k : K),
        ηs ≠ 0 ∧ ηt ≠ 0 ∧
          π (coordinateVector s) = ηs • E k ∧
          π (coordinateVector t) = ηt • E k ∧
          v = ηt • coordinateVector s - ηs • coordinateVector t}

/-- Claim 5720: these singleton and scalar-weighted dipole relations generate the kernel. -/
def kernelsOfMonomialCoordinateQuotientsClaim
    {F S Q K : Type*} [Field F] [AddCommGroup Q] [Module F Q]
    [Fintype S] [Fintype K] [DecidableEq S]
    (π : (S → F) →ₗ[F] Q) (E : Module.Basis K F Q) : Prop :=
  MonomialCoordinatePresentation π E →
    LinearMap.ker π = Submodule.span F (monomialRelationGenerators π E)

/-- Claim 5721: certification is exactly the kernel sandwich, with the induced factorization. -/
def certifiedProjectiveColoringClaim
    {F S Q K : Type*} [Field F] [AddCommGroup Q] [Module F Q]
    [Fintype S] [Fintype K] [DecidableEq S]
    (R D₀ : Submodule F (S → F))
    (π : (S → F) →ₗ[F] Q) (E : Module.Basis K F Q) : Prop :=
  D₀ ≤ R ∧
    MonomialCoordinatePresentation π E ∧
    D₀ ≤ LinearMap.ker π ∧
    LinearMap.ker π ≤ R ∧
    ∃ φ : ((S → F) ⧸ D₀) →ₗ[F] Q,
      φ.comp (Submodule.mkQ D₀) = π

/-- The aggregate column of a color in a gain-colored rank-`d` block. -/
def gainWeightedAggregate
    {F S K d : Type*} [Field F] [Fintype S] [DecidableEq K]
    (v : S → (d → F)) (κ : S → K) (η : S → F) (k : K) : d → F :=
  ∑ s : S, if κ s = k then η s • v s else 0

/-- Claim 5722: gain coloring aggregates each color and carries row functionals accordingly. -/
def gainWeightedBlockAggregationClaim
    {F S K d Q : Type*} [Field F] [AddCommGroup Q] [Module F Q]
    [Fintype S] [Fintype K] [DecidableEq K]
    (v : S → (d → F)) (κ : S → K) (η : S → F)
    (E : Module.Basis K F Q) : Prop :=
  ∀ f : (d → F) →ₗ[F] F,
    (∑ s : S, f (η s • v s) • E (κ s)) =
      ∑ k : K, f (gainWeightedAggregate v κ η k) • E k

/-- Claim 5734: the coordinate presentation is monomial when each coordinate has one basis-line image. -/
def monomialCoordinatePresentationClaim
    {F S Q : Type*} [Field F] [AddCommGroup Q] [Module F Q]
    [DecidableEq S] (π : (S → F) →ₗ[F] Q) : Prop :=
  ∃ (K : Type*) (E : Module.Basis K F Q), MonomialCoordinatePresentation π E

/-- Claim 5737: an irreducible triad is a minimal three-term relation on nonparallel lines. -/
def irreducibleTriadClaim
    {F I V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (E : I → V) (i j k : I) : Prop :=
  i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
    E i ≠ 0 ∧ E j ≠ 0 ∧ E k ≠ 0 ∧
    (¬ ∃ a0 : F, a0 ≠ 0 ∧ E i = a0 • E j) ∧
    (¬ ∃ a0 : F, a0 ≠ 0 ∧ E i = a0 • E k) ∧
    (¬ ∃ a0 : F, a0 ≠ 0 ∧ E j = a0 • E k) ∧
    (∃ (a b c : F),
      a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧
        a • E i + b • E j + c • E k = 0) ∧
    (∀ x y : F, x • E i + y • E j = 0 → x = 0 ∧ y = 0) ∧
    (∀ x y : F, x • E i + y • E k = 0 → x = 0 ∧ y = 0) ∧
    (∀ x y : F, x • E j + y • E k = 0 → x = 0 ∧ y = 0) ∧
    (∀ x : F, x • E i = 0 → x = 0) ∧
    (∀ x : F, x • E j = 0 → x = 0) ∧
    (∀ x : F, x • E k = 0 → x = 0)

/-- Column rank of the submatrix selected by a finite set of columns. -/
noncomputable def columnRank
    {F E R : Type*} [Field F] [Fintype E] [Fintype R] [DecidableEq E]
    (L : Matrix R E F) (S : Finset E) : ℕ :=
  Module.finrank F
    (Submodule.span F {w : R → F | ∃ e, e ∈ S ∧ w = fun r => L r e})

/-- Claim 5104: the full-set row-count inequality can pass while a proper subset fails. -/
def totalRowCountNotSufficientClaim : Prop :=
  let L : Matrix (Fin 2) (Fin 4) ℚ :=
    fun r e => if e = 3 then (if r = 1 then 1 else 0) else (if r = 0 then 1 else 0)
  let S : Finset (Fin 4) := ({0, 1, 2} : Finset (Fin 4))
  2 * columnRank L Finset.univ ≥ Fintype.card (Fin 4) ∧
    S ⊂ (Finset.univ : Finset (Fin 4)) ∧
    S.Nonempty ∧
    0 < columnRank L S ∧
    S.card > 2 * columnRank L S ∧
    ¬ (∀ T : Finset (Fin 4), T ⊆ Finset.univ →
      T.card ≤ 2 * columnRank L T)

abbrev HeisenbergPoint (p : ℕ) := ZMod p × (ZMod p × ZMod p)
abbrev HeisenbergOmega (p : ℕ) := ZMod p × ZMod p

def heisenbergMul (p : ℕ) (x y : HeisenbergPoint p) : HeisenbergPoint p :=
  (x.1 + y.1,
    (x.2.1 + y.2.1, x.2.2 + y.2.2 + x.1 * y.2.1))

def heisenbergOne (p : ℕ) : HeisenbergPoint p := (0, (0, 0))

def heisenbergInv (p : ℕ) (x : HeisenbergPoint p) : HeisenbergPoint p :=
  (-x.1, (-x.2.1, -x.2.2 + x.1 * x.2.1))

def heisenbergPow (p : ℕ) (n : ℕ) (x : HeisenbergPoint p) : HeisenbergPoint p :=
  Nat.rec (heisenbergOne p) (fun _ z => heisenbergMul p z x) n

/-- Claim 5940: the displayed Heisenberg multiplication gives a group of order `p^3`. -/
def orderP3HeisenbergGroupClaim (p : ℕ) : Prop :=
  ∀ hp : p.Prime, Odd p →
    letI : NeZero p := ⟨Nat.ne_of_gt hp.pos⟩
    (∀ x y z : HeisenbergPoint p,
        heisenbergMul p (heisenbergMul p x y) z =
          heisenbergMul p x (heisenbergMul p y z)) ∧
      (∀ x : HeisenbergPoint p,
        heisenbergMul p (heisenbergOne p) x = x ∧
          heisenbergMul p x (heisenbergOne p) = x) ∧
      (∀ x : HeisenbergPoint p,
        heisenbergMul p (heisenbergInv p x) x = heisenbergOne p ∧
          heisenbergMul p x (heisenbergInv p x) = heisenbergOne p) ∧
      Fintype.card (HeisenbergPoint p) = p ^ 3

def heisenbergCoordinate (x : HeisenbergPoint p) : HeisenbergOmega p :=
  (x.2.1, x.2.2)

def heisenbergAction (p : ℕ) (g : HeisenbergPoint p) (ω : HeisenbergOmega p) :
    HeisenbergOmega p :=
  (ω.1 + g.2.1, ω.2 + g.2.2 + g.1 * ω.1)

/-- Claim 5941: right cosets of `U` are the `(b,c)` coordinates and left multiplication acts as stated. -/
def heisenbergCosetActionClaim (p : ℕ) : Prop :=
  ∀ hp : p.Prime, Odd p →
    letI : NeZero p := ⟨Nat.ne_of_gt hp.pos⟩
    Function.Surjective (heisenbergCoordinate (p := p)) ∧
      (∀ x y : HeisenbergPoint p,
        heisenbergCoordinate x = heisenbergCoordinate y ↔
          ∃ u : HeisenbergPoint p,
            u.2.1 = 0 ∧ u.2.2 = 0 ∧ y = heisenbergMul p x u) ∧
      (∀ g x : HeisenbergPoint p,
        heisenbergCoordinate (heisenbergMul p g x) =
          heisenbergAction p g (heisenbergCoordinate x))

def heisenbergEOne (p : ℕ) (x : HeisenbergPoint p) : Prop :=
  x.1 = x.2.1

def heisenbergEInf (p : ℕ) (x : HeisenbergPoint p) : Prop :=
  x.1 = 0

def heisenbergSubgroup (p : ℕ) (E : HeisenbergPoint p → Prop) : Prop :=
  E (heisenbergOne p) ∧
    (∀ x y, E x → E y → E (heisenbergMul p x y)) ∧
    (∀ x, E x → E (heisenbergInv p x))

noncomputable def heisenbergElementaryAbelian
    (p : ℕ) (E : HeisenbergPoint p → Prop) [NeZero p] : Prop :=
  letI : DecidablePred E := Classical.decPred E
  heisenbergSubgroup p E ∧
    (∀ x y, E x → E y → heisenbergMul p x y = heisenbergMul p y x) ∧
    (∀ x, E x → heisenbergPow p p x = heisenbergOne p) ∧
    Fintype.card {x : HeisenbergPoint p // E x} = p ^ 2

/-- Claim 5942: the two displayed subgroups are elementary abelian and regular on the cosets. -/
def twoRegularElementaryAbelianSubgroupsClaim (p : ℕ) : Prop :=
  ∀ hp : p.Prime, Odd p →
    letI : NeZero p := ⟨Nat.ne_of_gt hp.pos⟩
    heisenbergElementaryAbelian p (heisenbergEOne p) ∧
      heisenbergElementaryAbelian p (heisenbergEInf p) ∧
      (∀ ω ω' : HeisenbergOmega p,
        ∃! g : HeisenbergPoint p,
          heisenbergEOne p g ∧ heisenbergAction p g ω = ω') ∧
      (∀ ω ω' : HeisenbergOmega p,
        ∃! g : HeisenbergPoint p,
          heisenbergEInf p g ∧ heisenbergAction p g ω = ω')

def heisenbergOrbitalEq
    (p : ℕ) (ω₁ ω₂ ν₁ ν₂ : HeisenbergOmega p) : Prop :=
  ∃ g : HeisenbergPoint p,
    heisenbergAction p g ω₁ = ν₁ ∧ heisenbergAction p g ω₂ = ν₂

/-- Claim 5943: pair orbits are classified by the stated coordinate differences. -/
def orbitalClassificationOfCosetActionClaim (p : ℕ) : Prop :=
  ∀ hp : p.Prime, Odd p →
    ∀ ω₁ ω₂ ν₁ ν₂ : HeisenbergOmega p,
      heisenbergOrbitalEq p ω₁ ω₂ ν₁ ν₂ ↔
        (ω₂.1 - ω₁.1 = ν₂.1 - ν₁.1 ∧
          (ω₂.1 - ω₁.1 = 0 → ω₂.2 - ω₁.2 = ν₂.2 - ν₁.2))

def heisenbergShear {p : ℕ} [Fact p.Prime] (ω : HeisenbergOmega p) :
    HeisenbergOmega p :=
  (ω.1, ω.2 + (2 : ZMod p)⁻¹ * ω.1 ^ 2)

def heisenbergShearInv {p : ℕ} [Fact p.Prime] (ω : HeisenbergOmega p) :
    HeisenbergOmega p :=
  (ω.1, ω.2 - (2 : ZMod p)⁻¹ * ω.1 ^ 2)

/-- Claim 5944: the quadratic shear is an orbital-preserving permutation. -/
def quadraticShearPreservesEveryOrbitalClaim (p : ℕ) : Prop :=
  ∀ hp : p.Prime, Odd p →
    letI : Fact p.Prime := ⟨hp⟩
    Function.Bijective (heisenbergShear (p := p)) ∧
      (∀ ω : HeisenbergOmega p,
        heisenbergShearInv (p := p) (heisenbergShear (p := p) ω) = ω ∧
          heisenbergShear (p := p) (heisenbergShearInv (p := p) ω) = ω) ∧
      (∀ ω₁ ω₂ : HeisenbergOmega p,
        heisenbergOrbitalEq p ω₁ ω₂
          (heisenbergShear (p := p) ω₁)
          (heisenbergShear (p := p) ω₂))

def heisenbergConjugatesOnOmega
    (p : ℕ) (q qInv : HeisenbergOmega p → HeisenbergOmega p)
    (A B : HeisenbergPoint p → Prop) : Prop :=
  (∀ ω,
    qInv (q ω) = ω ∧ q (qInv ω) = ω) ∧
    (∀ h, A h →
      ∃ h', B h' ∧
        ∀ ω, qInv (heisenbergAction p h (q ω)) = heisenbergAction p h' ω) ∧
    (∀ h', B h' →
      ∃ h, A h ∧
        ∀ ω, q (heisenbergAction p h' (qInv ω)) = heisenbergAction p h ω)

/-- Claim 5945: the shear conjugates the first regular subgroup to the second. -/
def shearConjugatesTheRegularPairClaim (p : ℕ) : Prop :=
  ∀ hp : p.Prime, Odd p →
    letI : Fact p.Prime := ⟨hp⟩
    heisenbergConjugatesOnOmega p
      (heisenbergShear (p := p))
      (heisenbergShearInv (p := p))
      (heisenbergEOne p) (heisenbergEInf p)

def heisenbergNormalSubgroup
    (p : ℕ) (E : HeisenbergPoint p → Prop) : Prop :=
  heisenbergSubgroup p E ∧
    ∀ g h, E h →
      E (heisenbergMul p (heisenbergMul p g h) (heisenbergInv p g))

/-- Claim 5946: the two normal subgroups are distinct and not conjugate in the induced image. -/
def noConjugacyInActualHeisenbergImageClaim (p : ℕ) : Prop :=
  ∀ hp : p.Prime, Odd p →
    heisenbergNormalSubgroup p (heisenbergEOne p) ∧
      heisenbergNormalSubgroup p (heisenbergEInf p) ∧
      (∃ x : HeisenbergPoint p,
        heisenbergEOne p x ∧ ¬ heisenbergEInf p x) ∧
      ¬ ∃ g : HeisenbergPoint p,
        heisenbergConjugatesOnOmega p
          (fun ω => heisenbergAction p g ω)
          (fun ω => heisenbergAction p (heisenbergInv p g) ω)
          (heisenbergEOne p) (heisenbergEInf p)

/-- Claim 5966: the exact-incidence count for every root subset. -/
def orderedRootExactIncidenceTableClaim
    (r : ℕ) {A : Type*} [DecidableEq A]
    (outside : Finset A) (incidence : A → Finset (Fin r))
    (x : Finset (Fin r) → ℕ) : Prop :=
  ∀ S : Finset (Fin r),
    x S = (outside.filter (fun a => incidence a = S)).card

/-- The Boolean margin obtained by summing the exact-incidence table over supersets. -/
def rootBooleanMargin
    {r : ℕ} (x : Finset (Fin r) → ℕ) (T : Finset (Fin r)) : ℕ :=
  ∑ S : Finset (Fin r), if T ⊆ S then x S else 0

/-- Claim 5967: proper margins sum over supersets and the full margin is the full cell. -/
def properBooleanMarginsClaim
    (r : ℕ) (x m : Finset (Fin r) → ℕ) : Prop :=
  (∀ T : Finset (Fin r), T.Nonempty → T ⊂ Finset.univ →
    m T = rootBooleanMargin x T) ∧
    m Finset.univ = x Finset.univ

end MathlibPlus.Open.Research.FormalizationBatch_01a003d5
