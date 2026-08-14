import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

noncomputable section

/-- A permutation preserving the adjacency relation of a simple graph. -/
def preservesGraphAdjacency {α : Type*} (Γ : SimpleGraph α)
    (p : Equiv.Perm α) : Prop :=
  ∀ x y, Γ.Adj (p x) (p y) ↔ Γ.Adj x y

/-- Regularity of a permutation subgroup, stated by unique transport between points. -/
def isRegularPermutationSubgroup {α : Type*}
    (R : Subgroup (Equiv.Perm α)) : Prop :=
  ∀ x y : α, ∃! r : R, (r : Equiv.Perm α) x = y

/-- Conjugacy of permutation subgroups inside the full symmetric group. -/
def conjugatePermutationSubgroups {α : Type*}
    (R T : Subgroup (Equiv.Perm α)) : Prop :=
  ∃ p : Equiv.Perm α, ∀ s : Equiv.Perm α,
    s ∈ T ↔ ∃ r : Equiv.Perm α, r ∈ R ∧ s = p * r * p⁻¹

/-- Claim 30887: empty and complete graphs have symmetric automorphism group, and
abstractly isomorphic regular subgroups are conjugate there. -/
def claim30887 : Prop :=
  ∀ (α : Type*) [Fintype α] (Γ : SimpleGraph α),
    (Γ = (⊥ : SimpleGraph α) ∨ Γ = (⊤ : SimpleGraph α)) →
      (∀ p : Equiv.Perm α, preservesGraphAdjacency Γ p) ∧
      ∀ (R T : Subgroup (Equiv.Perm α)),
        isRegularPermutationSubgroup R →
        isRegularPermutationSubgroup T →
        Nonempty (R ≃* T) →
        conjugatePermutationSubgroups R T

/-- The alternating group on four points, represented as the even-permutation
subgroup of the symmetric group. -/
def A4Subgroup : Subgroup (Equiv.Perm (Fin 4)) :=
  (⊥ : Subgroup ℤˣ).comap (Equiv.Perm.sign)

abbrev A4 : Type := A4Subgroup
abbrev C7 : Type := Multiplicative (ZMod 7)
abbrev C11 : Type := Multiplicative (ZMod 11)
abbrev Group84 : Type := C7 × A4
abbrev Group132 : Type := C11 × A4

noncomputable instance : Fintype A4 := Fintype.ofFinite _

/-- A finite simple undirected Cayley graph, with its connection set made explicit. -/
def isUndirectedCayleyGraph {G : Type*} [Group G]
    (Γ : SimpleGraph G) : Prop :=
  ∃ S : Set G,
    (∀ s, s ∈ S → s⁻¹ ∈ S) ∧
    1 ∉ S ∧
    ∀ x y, Γ.Adj x y ↔ x⁻¹ * y ∈ S

/-- A regular copy of a group inside its permutation group. -/
def isRegularCopy {G : Type*} [Group G]
    (R : Subgroup (Equiv.Perm G)) : Prop :=
  isRegularPermutationSubgroup R ∧ Nonempty (R ≃* G)

/-- A permutation subgroup is transitive on ordered pairs of distinct points. -/
def isTwoTransitive {α : Type*}
    (X : Subgroup (Equiv.Perm α)) : Prop :=
  ∀ (x₁ x₂ y₁ y₂ : α), x₁ ≠ x₂ → y₁ ≠ y₂ →
    ∃ g : X, (g : Equiv.Perm α) x₁ = y₁ ∧ (g : Equiv.Perm α) x₂ = y₂

/-- Blocks and primitivity for a permutation subgroup. -/
def isBlock {α : Type*} (X : Subgroup (Equiv.Perm α)) (B : Set α) : Prop :=
  B.Nonempty ∧
    ∀ g : X,
      (g : Equiv.Perm α) '' B = B ∨
        Disjoint ((g : Equiv.Perm α) '' B) B

def isPrimitivePermutationSubgroup {α : Type*}
    (X : Subgroup (Equiv.Perm α)) : Prop :=
  (∀ x y : α, ∃ g : X, (g : Equiv.Perm α) x = y) ∧
    ∀ B : Set α, isBlock X B → B.Subsingleton ∨ B = Set.univ

def isGraphSubgroup {α : Type*} (Γ : SimpleGraph α)
    (R : Subgroup (Equiv.Perm α)) : Prop :=
  ∀ r : R, preservesGraphAdjacency Γ (r : Equiv.Perm α)

/-- Claim 30882: primitivity of the generated pair forces two-transitivity for
exactly the two groups in the packet. -/
def claim30882 : Prop :=
  ∀ (G : Type*) [Fintype G] [Group G],
    (Nonempty (G ≃* Group84) ∨ Nonempty (G ≃* Group132)) →
    ∀ (Γ : SimpleGraph G), isUndirectedCayleyGraph Γ →
      ∀ (R T : Subgroup (Equiv.Perm G)),
        isRegularCopy R → isRegularCopy T →
        isGraphSubgroup Γ R → isGraphSubgroup Γ T →
        isPrimitivePermutationSubgroup (R ⊔ T) →
        isTwoTransitive (R ⊔ T)

/-- Claim 30888: in the preceding setting, a primitive generated pair can only
occur for the empty or complete graph, where the copies are conjugate. -/
def claim30888 : Prop :=
  ∀ (G : Type*) [Fintype G] [Group G],
    (Nonempty (G ≃* Group84) ∨ Nonempty (G ≃* Group132)) →
    ∀ (Γ : SimpleGraph G), isUndirectedCayleyGraph Γ →
      ∀ (R T : Subgroup (Equiv.Perm G)),
        isRegularCopy R → isRegularCopy T →
        isGraphSubgroup Γ R → isGraphSubgroup Γ T →
        isPrimitivePermutationSubgroup (R ⊔ T) →
        (Γ = (⊥ : SimpleGraph G) ∨ Γ = (⊤ : SimpleGraph G)) ∧
        ∃ p : Equiv.Perm G,
          preservesGraphAdjacency Γ p ∧
          (∀ s : Equiv.Perm G,
            s ∈ T ↔ ∃ r : Equiv.Perm G, r ∈ R ∧ s = p * r * p⁻¹)

end

end MathlibPlus.Open.ResearchFormalization
