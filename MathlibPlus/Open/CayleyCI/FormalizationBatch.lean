import Mathlib

namespace MathlibPlus.Open.CayleyCI

universe uA uV

/-- An identity-free connection set. -/
def IdentityFree (G : Type*) [One G] (R : Set G) : Prop :=
  (1 : G) ∉ R

/-- Closure under inversion, the condition making a Cayley connection set undirected. -/
def InverseClosed (G : Type*) [Inv G] (R : Set G) : Prop :=
  ∀ ⦃x : G⦄, x ∈ R → x⁻¹ ∈ R

/-- Isomorphism of the ordinary simple right-Cayley graphs on one group carrier. -/
def RightCayleyGraphIsomorphic (G : Type*) [Group G]
    (R T : Set G) : Prop :=
  ∃ e : G ≃ G, ∀ x y : G,
    (x ≠ y ∧ x⁻¹ * y ∈ R) ↔
      (e x ≠ e y ∧ (e x)⁻¹ * e y ∈ T)

/-- The ordinary undirected CI property for one identity-free connection set. -/
def OrdinaryUndirectedCIConnectionSet (G : Type*) [Group G]
    (R : Set G) : Prop :=
  IdentityFree G R ∧
    InverseClosed G R ∧
      ∀ T : Set G,
        IdentityFree G T →
        InverseClosed G T →
        RightCayleyGraphIsomorphic G R T →
        ∃ α : G ≃* G, α '' R = T

/-- The ordinary undirected CI-group property. -/
def OrdinaryUndirectedCIGroup (G : Type*) [Group G] [Fintype G] : Prop :=
  ∀ R : Set G,
    IdentityFree G R →
    InverseClosed G R →
    OrdinaryUndirectedCIConnectionSet G R

/-- The complete-clique blow-up connection set from a set on the second factor. -/
def CompleteCliqueBlowUpSet {H Q : Type*} [Group H] [Group Q]
    (U : Set Q) : Set (H × Q) :=
  {g : H × Q | g.1 ≠ (1 : H) ∧ g.2 = (1 : Q)} ∪
    {g : H × Q | g.2 ∈ U}

/-- The identity-free complement of a connection set. -/
def IdentityFreeComplement {G : Type*} [One G] (R : Set G) : Set G :=
  {g : G | g ≠ (1 : G) ∧ g ∉ R}

/-- The subgroup-automorphism hypothesis used in the blow-up transfer. -/
def SameOrderSubgroupsAutomorphic (Q : Type*) [Group Q] [Fintype Q] : Prop :=
  ∀ L L' : Subgroup Q,
    Nat.card L = Nat.card L' →
    ∃ α : Q ≃* Q, α '' (L : Set Q) = (L' : Set Q)

/-- The presentation and finite size of the group denoted by Q₁₂ in the claim. -/
def PresentedQ12 (Q : Type*) [Group Q] [Fintype Q] (a b : Q) : Prop :=
  Fintype.card Q = 12 ∧
    a ^ 6 = 1 ∧
      b ^ 2 = a ^ 3 ∧
        b⁻¹ * a * b = a⁻¹ ∧
          ∀ x : Q, x ∈ Subgroup.closure ({a, b} : Set Q)

/-- The identity-free inverse-closed choices on a finite group. -/
def UndirectedChoices (G : Type*) [Group G] (U : Set G) : Prop :=
  IdentityFree G U ∧ InverseClosed G U

/-- Claim 61001: complete-clique blow-up transfer, including its Q₁₂ specialization. -/
def CompleteCliqueBlowUpTransferTheorem : Prop :=
  (∀ (H Q : Type*) [Group H] [Fintype H] [Group Q] [Fintype Q],
    Nat.Coprime (Fintype.card H) (Fintype.card Q) →
    OrdinaryUndirectedCIGroup Q →
    SameOrderSubgroupsAutomorphic Q →
    ∀ U : Set Q,
      UndirectedChoices Q U →
      let S := CompleteCliqueBlowUpSet U
      let Sdag := IdentityFreeComplement S
      OrdinaryUndirectedCIConnectionSet (H × Q) S ∧
        OrdinaryUndirectedCIConnectionSet (H × Q) Sdag) ∧
    (∀ (Q : Type*) [Group Q] [Fintype Q] (a b : Q),
      PresentedQ12 Q a b →
      Nat.card {U : Finset Q // UndirectedChoices Q (U : Set Q)} = 64 ∧
        ∀ (H : Type*) [Group H] [Fintype H],
          Nat.Coprime (Fintype.card H) 12 →
          ∀ U : Set Q,
            UndirectedChoices Q U →
            let S := CompleteCliqueBlowUpSet U
            let Sdag := IdentityFreeComplement S
            OrdinaryUndirectedCIConnectionSet (H × Q) S ∧
              OrdinaryUndirectedCIConnectionSet (H × Q) Sdag)

/-- The connection set on a subgroup, viewed as a set of the subgroup type. -/
def SubgroupConnectionSet {A : Type*} [Group A]
    (H : Subgroup A) (D : Set A) : Set H :=
  {x : H | (x : A) ∈ D}

/-- The right-Cayley adjacency relation for a subgroup factor. -/
def SubgroupCayleyAdjacency {A : Type*} [Group A]
    (H : Subgroup A) (D : Set A) (x y : H) : Prop :=
  x ≠ y ∧ (x : A)⁻¹ * (y : A) ∈ D

/-- Abstract graph isomorphism from a subgroup Cayley graph to a simple graph. -/
def SubgroupCayleyGraphIsomorphicTo {A : Type uA} [Group A]
    (H : Subgroup A) (D : Set A) {V : Type uV} [Fintype V]
    (Γ : SimpleGraph V) : Prop :=
  ∃ e : H ≃ V, ∀ x y : H,
    SubgroupCayleyAdjacency H D x y ↔ Γ.Adj (e x) (e y)

/-- Connectedness of a subgroup Cayley graph, expressed by generation. -/
def SubgroupCayleyConnected {A : Type*} [Group A]
    (H : Subgroup A) (D : Set A) : Prop :=
  Subgroup.closure (SubgroupConnectionSet H D) = ⊤

/-- Cartesian primeness of a nontrivial subgroup Cayley graph. -/
def SubgroupCayleyCartesianPrime {A : Type uA} [Group A]
    (H : Subgroup A) (D : Set A) : Prop :=
  ∀ (V W : Type uA) [Fintype V] [Fintype W],
    2 ≤ Fintype.card V →
    2 ≤ Fintype.card W →
    ∀ (Γ : SimpleGraph V) (Δ : SimpleGraph W),
      ¬ ∃ e : H ≃ (V × W), ∀ x y : H,
        SubgroupCayleyAdjacency H D x y ↔
          (((e x).1 = (e y).1 ∧ Δ.Adj (e x).2 (e y).2) ∨
            ((e x).2 = (e y).2 ∧ Γ.Adj (e x).1 (e y).1))

/-- A finite ordered product, used to state an internal direct-sum decomposition. -/
def OrderedProduct {M : Type*} [Monoid M] {k : Nat}
    (x : Fin k → M) : M :=
  (List.ofFn x).prod

/-- Internal direct-sum decomposition of a finite family of subgroups. -/
def InternalDirectSum {A : Type*} [Group A] {k : Nat}
    (H : Fin k → Subgroup A) : Prop :=
  ∀ a : A, ∃! x : Fin k → A,
    (∀ i : Fin k, x i ∈ H i) ∧ OrderedProduct x = a

/-- The simultaneous order-homogeneity condition on a displayed decomposition. -/
def OrderHomogeneousDecomposition {A : Type*} [Group A] {k : Nat}
    (H : Fin k → Subgroup A) : Prop :=
  ∀ K : Fin k → Subgroup A,
    InternalDirectSum K →
    (∀ i : Fin k, Nat.card (K i) = Nat.card (H i)) →
    ∃ δ : A ≃* A, ∀ i : Fin k, δ '' (H i : Set A) = (K i : Set A)

/-- Surjectivity of restriction from the stabilizer of A in Aut(G) to Aut(A). -/
def RestrictionToSubgroupSurjective {G : Type*} [Group G]
    (A : Subgroup G) : Prop :=
  ∀ β : A ≃* A, ∃ α : G ≃* G,
    α '' (A : Set G) = (A : Set G) ∧
      ∀ a : A, α (a : G) = (β a : G)

/-- The image in G of a set on the subgroup type A. -/
def SubgroupImageSet {G : Type*} [Group G]
    (A : Subgroup G) (S : Set A) : Set G :=
  (fun a : A => (a : G)) '' S

/-- Claim 61002: small-multiplicity Cartesian-prime component compression. -/
def SmallMultiplicityCartesianPrimeComponentCompressionTheorem : Prop :=
  ∀ (G : Type*) [Group G] [Fintype G] (A : Subgroup G),
    (∃ a : A, a ≠ 1) →
    (∀ a b : A, a * b = b * a) →
    ∀ k : Nat, 0 < k →
      ∀ H : Fin k → Subgroup A,
        InternalDirectSum H →
        (∀ i : Fin k, ∃ h : H i, h ≠ 1) →
        let ℓ := Nat.minFac (Nat.card A)
        ∀ D : Fin k → Set A,
          (∀ i : Fin k,
            D i ⊆ (H i : Set A) \ {1} ∧ InverseClosed A (D i)) →
          (∀ i : Fin k,
            SubgroupCayleyConnected (H i) (D i) ∧
              SubgroupCayleyCartesianPrime (H i) (D i)) →
          (∀ i : Fin k,
            OrdinaryUndirectedCIConnectionSet (H i)
              (SubgroupConnectionSet (H i) (D i))) →
          (∀ (V : Type*) [Fintype V] (Γ : SimpleGraph V),
            Nat.card {i : Fin k //
              SubgroupCayleyGraphIsomorphicTo (H i) (D i) Γ} < ℓ) →
          OrderHomogeneousDecomposition H →
          (∀ B : Subgroup G,
            Nat.card B = Nat.card A →
              ∃ α : G ≃* G, α '' (A : Set G) = (B : Set G)) →
          RestrictionToSubgroupSurjective A →
          let S : Set A := {a : A | ∃ i : Fin k, a ∈ D i}
          OrdinaryUndirectedCIConnectionSet G (SubgroupImageSet A S) ∧
            OrdinaryUndirectedCIConnectionSet G
              (IdentityFreeComplement (SubgroupImageSet A S))

/-- Additive identity-free inverse-closed connection sets. -/
def AddIdentityFreeInverseClosed (G : Type*) [AddGroup G]
    (R : Set G) : Prop :=
  (0 : G) ∉ R ∧ ∀ ⦃x : G⦄, x ∈ R → -x ∈ R

/-- Isomorphism of ordinary additive Cayley graphs. -/
def AddCayleyGraphIsomorphic (G : Type*) [AddCommGroup G]
    (R T : Set G) : Prop :=
  ∃ e : G ≃ G, ∀ x y : G,
    (x ≠ y ∧ y - x ∈ R) ↔
      (e x ≠ e y ∧ e y - e x ∈ T)

/-- The ordinary undirected additive CI property for one connection set. -/
def AddOrdinaryUndirectedCIConnectionSet (G : Type*) [AddCommGroup G]
    [Fintype G] (R : Set G) : Prop :=
  AddIdentityFreeInverseClosed G R ∧
    ∀ T : Set G,
      AddIdentityFreeInverseClosed G T →
      AddCayleyGraphIsomorphic G R T →
      ∃ α : G ≃+ G, α '' R = T

/-- The additive identity-free complement. -/
def AddIdentityFreeComplement {G : Type*} [Zero G] (R : Set G) : Set G :=
  {g : G | g ≠ (0 : G) ∧ g ∉ R}

/-- Claim 61003: the two-sided nongeneration sector and its exact count. -/
def TwoSidedNongenerationSectorAndExactCount : Prop :=
  let G := ZMod 4 × (Fin 3 → ZMod 3)
  (∀ S : Set G,
    AddIdentityFreeInverseClosed G S →
    (AddSubgroup.closure S < (⊤ : AddSubgroup G) ∨
      AddSubgroup.closure (AddIdentityFreeComplement S) < (⊤ : AddSubgroup G)) →
    AddOrdinaryUndirectedCIConnectionSet G S ∧
      AddOrdinaryUndirectedCIConnectionSet G (AddIdentityFreeComplement S)) ∧
    Nat.card {S : Finset G //
      AddIdentityFreeInverseClosed G (S : Set G)} = 2 ^ 54 ∧
    Nat.card {S : Finset G //
      AddIdentityFreeInverseClosed G (S : Set G) ∧
        AddSubgroup.closure (S : Set G) < (⊤ : AddSubgroup G)} =
      137616814 ∧
    (∀ S : Set G,
      AddIdentityFreeInverseClosed G S →
      ¬ (AddSubgroup.closure S < (⊤ : AddSubgroup G) ∧
        AddSubgroup.closure (AddIdentityFreeComplement S) <
          (⊤ : AddSubgroup G))) ∧
    2 * 137616814 = 275233628 ∧
    Nat.card {S : Finset G //
      AddIdentityFreeInverseClosed G (S : Set G) ∧
        (AddSubgroup.closure (S : Set G) < (⊤ : AddSubgroup G) ∨
          AddSubgroup.closure (AddIdentityFreeComplement (S : Set G)) <
            (⊤ : AddSubgroup G))} =
      275233628 ∧
    Nat.card {S : Finset G //
      AddIdentityFreeInverseClosed G (S : Set G) ∧
        AddSubgroup.closure (S : Set G) = (⊤ : AddSubgroup G) ∧
        AddSubgroup.closure (AddIdentityFreeComplement (S : Set G)) =
          (⊤ : AddSubgroup G)} =
      18014398234248356

end MathlibPlus.Open.CayleyCI
