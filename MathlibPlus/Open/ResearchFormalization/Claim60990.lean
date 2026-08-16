import Mathlib

noncomputable section
open Classical
open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization

/-! Concrete, non-callback semantics for ordinary Cayley CI statements. -/

def claim60990CayleyAdj {G : Type*} [Group G]
    (R : Set G) (x y : G) : Prop :=
  x ≠ y ∧ x⁻¹ * y ∈ R

def claim60990GraphIso {G : Type*} [Group G]
    (R T : Set G) : Prop :=
  ∃ f : G → G,
    Function.Bijective f ∧
      ∀ x y, claim60990CayleyAdj R x y ↔
        claim60990CayleyAdj T (f x) (f y)

def claim60990OrdinaryUndirectedCI {G : Type*} [Group G]
    (R : Set G) : Prop :=
  1 ∉ R ∧
    (∀ x, x ∈ R ↔ x⁻¹ ∈ R) ∧
    ∀ T : Set G,
    T ⊆ (Set.univ \ ({1} : Set G)) →
    (∀ x, x ∈ T ↔ x⁻¹ ∈ T) →
    claim60990GraphIso R T →
    ∃ α : G ≃* G, α '' R = T

def claim60990OrderedProduct {G : Type*} [Group G] {k : ℕ}
    (h : Fin k → G) : G :=
  (Finset.univ.toList.map h).prod

def claim60990InternalDirectSum {G : Type*} [Group G] {k : ℕ}
    (H : Fin k → Subgroup G) : Prop :=
  (∀ i, ∃ h : G, h ∈ H i ∧ h ≠ 1) ∧
    ∀ a : G,
      ∃! h : Fin k → G,
        (∀ i, h i ∈ H i) ∧ claim60990OrderedProduct h = a

def claim60990Multiplicity {G : Type*} [Group G] [Fintype G] {k : ℕ}
    (H : Fin k → Subgroup G) (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun i => Nat.card (H i) = n)).card

def claim60990DecompositionSet {G : Type*} [Group G] {k : ℕ}
    (A : Subgroup G) (H : Fin k → Subgroup A) : Set G :=
  ⋃ i, (fun a : A => (a : G)) '' ((H i : Set A) \ ({1} : Set A))

def claim60990Hypotheses {G : Type*} [Group G] [Fintype G]
    (A : Subgroup G) [Fintype A] {k : ℕ} (H : Fin k → Subgroup A) : Prop :=
  (∃ a : A, a ≠ 1) ∧
    (∀ a b : A, a * b = b * a) ∧
    claim60990InternalDirectSum H ∧
    (∀ n, 2 ≤ n →
      claim60990Multiplicity H n < Nat.minFac (Nat.card A)) ∧
    (∀ K : Fin k → Subgroup A,
      claim60990InternalDirectSum K →
      (∀ i, Nat.card (K i) = Nat.card (H i)) →
      ∃ α : A ≃* A, ∀ i, α '' (H i : Set A) = (K i : Set A)) ∧
    (∀ B : Subgroup G,
      Nat.card B = Nat.card A →
      ∃ β : G ≃* G, β '' (A : Set G) = (B : Set G)) ∧
    (∀ α : A ≃* A,
      ∃ β : G ≃* G,
        β '' (A : Set G) = (A : Set G) ∧
          ∀ a : A, β (a : G) = (α a : G))

def claim60990General : Prop :=
  ∀ (G : Type) [Group G] [Fintype G]
    (A : Subgroup G) [Fintype A] {k : ℕ} (H : Fin k → Subgroup A),
    claim60990Hypotheses A H →
      claim60990OrdinaryUndirectedCI (claim60990DecompositionSet A H) ∧
        claim60990OrdinaryUndirectedCI
          ((Set.univ \ ({1} : Set G)) \ claim60990DecompositionSet A H)

/-! The maintained elementary-vector-space cell, stated with its actual carrier. -/

def claim60990LinearDirectSum {p r k : ℕ}
    [Fact p.Prime]
    (U : Fin k → Submodule (ZMod p) (Fin r → ZMod p)) : Prop :=
  (∀ i, ∃ u : Fin r → ZMod p, u ∈ U i ∧ u ≠ 0) ∧
    ∀ v : Fin r → ZMod p,
      ∃! u : Fin k → (Fin r → ZMod p),
        (∀ i, u i ∈ U i) ∧ Finset.sum Finset.univ u = v

def claim60990LinearMultiplicity {p r k : ℕ}
    [Fact p.Prime]
    (U : Fin k → Submodule (ZMod p) (Fin r → ZMod p)) (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun i => Module.finrank (ZMod p) (U i) = n)).card

def claim60990AdditiveAdj {p r : ℕ} [Fact p.Prime]
    (R : Set (Fin r → ZMod p)) (x y : Fin r → ZMod p) : Prop :=
  x ≠ y ∧ y - x ∈ R

def claim60990AdditiveGraphIso {p r : ℕ} [Fact p.Prime]
    (R T : Set (Fin r → ZMod p)) : Prop :=
  ∃ f : (Fin r → ZMod p) → (Fin r → ZMod p),
    Function.Bijective f ∧
      ∀ x y, claim60990AdditiveAdj R x y ↔
        claim60990AdditiveAdj T (f x) (f y)

def claim60990AdditiveCI {p r : ℕ} [Fact p.Prime]
    (R : Set (Fin r → ZMod p)) : Prop :=
  0 ∉ R ∧
    (∀ x, x ∈ R ↔ -x ∈ R) ∧
    ∀ T : Set (Fin r → ZMod p),
    T ⊆ Set.univ \ ({0} : Set (Fin r → ZMod p)) →
    (∀ x, x ∈ T ↔ -x ∈ T) →
    claim60990AdditiveGraphIso R T →
    ∃ α : (Fin r → ZMod p) ≃+ (Fin r → ZMod p), α '' R = T

def claim60990LinearSet {p r k : ℕ} [Fact p.Prime]
    (U : Fin k → Submodule (ZMod p) (Fin r → ZMod p)) : Set (Fin r → ZMod p) :=
  ⋃ i, (U i : Set (Fin r → ZMod p)) \ ({0} : Set (Fin r → ZMod p))

def claim60990FieldConsequence : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    5 ≤ p →
    ∀ r, 6 ≤ r → r ≤ 2 * p + 2 →
    ∀ (k : ℕ) (U : Fin k → Submodule (ZMod p) (Fin r → ZMod p)),
      claim60990LinearDirectSum U →
      (∀ n, claim60990LinearMultiplicity U n < p) →
      claim60990AdditiveCI (claim60990LinearSet U) ∧
        claim60990AdditiveCI
          ((Set.univ \ ({0} : Set (Fin r → ZMod p))) \ claim60990LinearSet U)

abbrev claim60990PrimeIndex (P : Finset ℕ) := {p // p ∈ P}

abbrev claim60990ProductSpace (P : Finset ℕ)
    (V : claim60990PrimeIndex P → Type*) :=
  ∀ p, V p

def claim60990FamilyDirectSum {P : Finset ℕ}
    (V : claim60990PrimeIndex P → Type*)
    [∀ p : claim60990PrimeIndex P, AddCommGroup (V p)]
    [∀ p : claim60990PrimeIndex P, Module (ZMod p.1) (V p)]
    (d : claim60990PrimeIndex P → ℕ)
    (L : ∀ p : claim60990PrimeIndex P,
      Fin (d p) → Submodule (ZMod p.1) (V p)) : Prop :=
  ∀ p, (∀ j, ∃ v : V p, v ∈ L p j ∧ v ≠ 0) ∧
    ∀ v : V p,
      ∃! u : Fin (d p) → V p,
        (∀ j, u j ∈ L p j) ∧ Finset.sum Finset.univ u = v

def claim60990Theta {P : Finset ℕ}
    (V : claim60990PrimeIndex P → Type*)
    [∀ p : claim60990PrimeIndex P, AddCommGroup (V p)]
    [∀ p : claim60990PrimeIndex P, Module (ZMod p.1) (V p)]
    (ω : ∀ p : claim60990PrimeIndex P, ZMod p.1)
    (c : ZMod 3) (m : claim60990ProductSpace P V) :
    claim60990ProductSpace P V :=
  fun p => (ω p) ^ c.val • m p

def claim60990EMul {P : Finset ℕ}
    (V : claim60990PrimeIndex P → Type*)
    [∀ p : claim60990PrimeIndex P, AddCommGroup (V p)]
    [∀ p : claim60990PrimeIndex P, Module (ZMod p.1) (V p)]
    (ω : ∀ p : claim60990PrimeIndex P, ZMod p.1)
    (x y : claim60990ProductSpace P V × ZMod 3) :
    claim60990ProductSpace P V × ZMod 3 :=
  (x.1 + claim60990Theta V ω x.2 y.1, x.2 + y.2)

def claim60990EOne {P : Finset ℕ}
    (V : claim60990PrimeIndex P → Type*)
    [∀ p : claim60990PrimeIndex P, AddCommGroup (V p)] :
    claim60990ProductSpace P V × ZMod 3 :=
  (0, 0)

def claim60990EInv {P : Finset ℕ}
    (V : claim60990PrimeIndex P → Type*)
    [∀ p : claim60990PrimeIndex P, AddCommGroup (V p)]
    [∀ p : claim60990PrimeIndex P, Module (ZMod p.1) (V p)]
    (ω : ∀ p : claim60990PrimeIndex P, ZMod p.1)
    (x : claim60990ProductSpace P V × ZMod 3) :
    claim60990ProductSpace P V × ZMod 3 :=
  (-claim60990Theta V ω (-x.2) x.1, -x.2)

def claim60990EAdj {P : Finset ℕ}
    (V : claim60990PrimeIndex P → Type*)
    [∀ p : claim60990PrimeIndex P, AddCommGroup (V p)]
    [∀ p : claim60990PrimeIndex P, Module (ZMod p.1) (V p)]
    (ω : ∀ p : claim60990PrimeIndex P, ZMod p.1)
    (R : Set (claim60990ProductSpace P V × ZMod 3))
    (x y : claim60990ProductSpace P V × ZMod 3) : Prop :=
  x ≠ y ∧ claim60990EMul V ω (claim60990EInv V ω x) y ∈ R

def claim60990EGraphIso {P : Finset ℕ}
    (V : claim60990PrimeIndex P → Type*)
    [∀ p : claim60990PrimeIndex P, AddCommGroup (V p)]
    [∀ p : claim60990PrimeIndex P, Module (ZMod p.1) (V p)]
    (ω : ∀ p : claim60990PrimeIndex P, ZMod p.1)
    (R T : Set (claim60990ProductSpace P V × ZMod 3)) : Prop :=
  ∃ f : claim60990ProductSpace P V × ZMod 3 →
      claim60990ProductSpace P V × ZMod 3,
    Function.Bijective f ∧
      ∀ x y, claim60990EAdj V ω R x y ↔
        claim60990EAdj V ω T (f x) (f y)

def claim60990EOrdinaryUndirectedCI {P : Finset ℕ}
    (V : claim60990PrimeIndex P → Type*)
    [∀ p : claim60990PrimeIndex P, AddCommGroup (V p)]
    [∀ p : claim60990PrimeIndex P, Module (ZMod p.1) (V p)]
    (ω : ∀ p : claim60990PrimeIndex P, ZMod p.1)
    (R : Set (claim60990ProductSpace P V × ZMod 3)) : Prop :=
  claim60990EOne V ∉ R ∧
    (∀ x, x ∈ R ↔ claim60990EInv V ω x ∈ R) ∧
    ∀ T : Set (claim60990ProductSpace P V × ZMod 3),
      claim60990EOne V ∉ T →
      (∀ x, x ∈ T ↔ claim60990EInv V ω x ∈ T) →
      claim60990EGraphIso V ω R T →
      ∃ f : claim60990ProductSpace P V × ZMod 3 →
          claim60990ProductSpace P V × ZMod 3,
        Function.Bijective f ∧
          (∀ x y, f (claim60990EMul V ω x y) =
            claim60990EMul V ω (f x) (f y)) ∧
          f (claim60990EOne V) = claim60990EOne V ∧
          f '' R = T

def claim60990EmbeddedLine {P : Finset ℕ}
    (V : claim60990PrimeIndex P → Type*)
    [∀ p : claim60990PrimeIndex P, AddCommGroup (V p)]
    [∀ p : claim60990PrimeIndex P, Module (ZMod p.1) (V p)]
    (d : claim60990PrimeIndex P → ℕ)
    (L : ∀ p : claim60990PrimeIndex P,
      Fin (d p) → Submodule (ZMod p.1) (V p))
    (p : claim60990PrimeIndex P) (j : Fin (d p)) :
    Set (claim60990ProductSpace P V × ZMod 3) :=
  (fun v : V p =>
    (Function.update (fun q => (0 : V q)) p v, (0 : ZMod 3))) ''
      ((L p j : Set (V p)) \ ({0} : Set (V p)))

def claim60990SM {P : Finset ℕ}
    (V : claim60990PrimeIndex P → Type*)
    [∀ p : claim60990PrimeIndex P, AddCommGroup (V p)]
    [∀ p : claim60990PrimeIndex P, Module (ZMod p.1) (V p)]
    (d : claim60990PrimeIndex P → ℕ)
    (L : ∀ p : claim60990PrimeIndex P,
      Fin (d p) → Submodule (ZMod p.1) (V p)) :
    Set (claim60990ProductSpace P V × ZMod 3) :=
  ⋃ p, ⋃ j, claim60990EmbeddedLine V d L p j

def claim60990FamilyLineDecomposition {P : Finset ℕ}
    (V : claim60990PrimeIndex P → Type*)
    [∀ p : claim60990PrimeIndex P, AddCommGroup (V p)]
    [∀ p : claim60990PrimeIndex P, Module (ZMod p.1) (V p)]
    (d : claim60990PrimeIndex P → ℕ)
    (L : ∀ p : claim60990PrimeIndex P,
      Fin (d p) → Submodule (ZMod p.1) (V p)) : Prop :=
  (∀ p, 0 < d p ∧ d p ≤ 3 ∧
    Module.finrank (ZMod p.1) (V p) = d p) ∧
  ∀ p,
    (∀ j, Module.finrank (ZMod p.1) (L p j) = 1) ∧
      claim60990FamilyDirectSum V d L

def claim60990SemidirectConsequence : Prop :=
  ∀ (P : Finset ℕ)
    (V : claim60990PrimeIndex P → Type)
    [∀ p : claim60990PrimeIndex P, Fact p.1.Prime]
    [∀ p : claim60990PrimeIndex P, Fintype (V p)]
    [∀ p : claim60990PrimeIndex P, AddCommGroup (V p)]
    [∀ p : claim60990PrimeIndex P, Module (ZMod p.1) (V p)],
    ∀ (ω : ∀ p : claim60990PrimeIndex P, ZMod p.1),
      (∀ p, orderOf (ω p) = 3) →
      ∀ (d : claim60990PrimeIndex P → ℕ)
        (L : ∀ p : claim60990PrimeIndex P,
          Fin (d p) → Submodule (ZMod p.1) (V p)),
        claim60990FamilyLineDecomposition V d L →
        claim60990EOrdinaryUndirectedCI V ω (claim60990SM V d L) ∧
          claim60990EOrdinaryUndirectedCI V ω
            ((Set.univ \ ({claim60990EOne V} : Set
              (claim60990ProductSpace P V × ZMod 3))) \ claim60990SM V d L)

def claim60990 : Prop :=
  claim60990General ∧ claim60990FieldConsequence ∧ claim60990SemidirectConsequence

end MathlibPlus.Open.ResearchFormalization
