import Mathlib

namespace MathlibPlus.Open.Research.BatchQ0052

section CayleyRelations

variable {G : Type*} [Group G]

/-- The adjacency relation of an ordinary Cayley graph. -/
def cayleyAdjacency (S : Set G) (x y : G) : Prop :=
  x⁻¹ * y ∈ S

/-- Graph isomorphism for the Cayley adjacency relation. -/
def cayleyGraphIsomorphism (S T : Set G) : Prop :=
  ∃ f : Equiv.Perm G,
    ∀ x y : G, cayleyAdjacency S x y ↔ cayleyAdjacency T (f x) (f y)

def inverseClosed (S : Set G) : Prop :=
  ∀ ⦃x : G⦄, x ∈ S → x⁻¹ ∈ S

def identityFree (S : Set G) : Prop :=
  (1 : G) ∉ S

/-- The undirected CI property, stated through all inverse-closed connection sets. -/
def undirectedCIGroup
    (G : Type*) [Group G] [DecidableEq G] : Prop :=
  ∀ S T : Set G,
    inverseClosed S → identityFree S →
    inverseClosed T → identityFree T →
    cayleyGraphIsomorphism S T →
    ∃ α : G ≃* G, Set.image α S = T

variable {A : Type*} [AddGroup A]

def additiveCayleyAdjacency (S : Set A) (x y : A) : Prop :=
  y - x ∈ S

def additiveCayleyGraphIsomorphism (S T : Set A) : Prop :=
  ∃ f : Equiv.Perm A,
    ∀ x y : A,
      additiveCayleyAdjacency S x y ↔ additiveCayleyAdjacency T (f x) (f y)

def additiveInverseClosed (S : Set A) : Prop :=
  ∀ ⦃x : A⦄, x ∈ S → -x ∈ S

def additiveIdentityFree (S : Set A) : Prop :=
  (0 : A) ∉ S

end CayleyRelations

section CliquePartitions

/-- A concrete partition description of a disjoint union of equal cliques. -/
def isDisjointUnionOfCliques
    {V : Type*} [Fintype V] [DecidableEq V]
    (adj : V → V → Prop) (number size : ℕ) : Prop :=
  ∃ blocks : Finset (Finset V),
    blocks.card = number ∧
    (∀ B ∈ blocks, B.card = size) ∧
    (∀ B ∈ blocks, ∀ C ∈ blocks, B ≠ C →
      ∀ x : V, x ∈ B → x ∉ C) ∧
    (∀ x : V, ∃ B ∈ blocks, x ∈ B) ∧
    (∀ x y : V, adj x y ↔
      ∃ B ∈ blocks, x ∈ B ∧ y ∈ B ∧ x ≠ y)

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

noncomputable def subgroupIndex (H : Subgroup G) : ℕ :=
  Nat.card G / Nat.card H

/-- The subgroup-clique counterexample assertion. -/
def subgroupCliqueCIDefect : Prop :=
  ∀ H K : Subgroup G,
    Nat.card H = Nat.card K →
    (¬ ∃ α : G ≃* G,
      Set.image α (H : Set G) = (K : Set G)) →
    isDisjointUnionOfCliques
      (cayleyAdjacency ((H : Set G) \ ({1} : Set G)))
      (subgroupIndex H) (Nat.card H) ∧
    isDisjointUnionOfCliques
      (cayleyAdjacency ((K : Set G) \ ({1} : Set G)))
      (subgroupIndex K) (Nat.card K) ∧
    cayleyGraphIsomorphism
      ((H : Set G) \ ({1} : Set G))
      ((K : Set G) \ ({1} : Set G)) ∧
    (¬ ∃ α : G ≃* G,
      Set.image α ((H : Set G) \ ({1} : Set G)) =
        ((K : Set G) \ ({1} : Set G)))

end CliquePartitions

section DihedralClassification

def oddSquarefree (n : ℕ) : Prop :=
  (¬ 2 ∣ n) ∧ ∀ p : ℕ, Nat.Prime p → ¬ p ^ 2 ∣ n

/-- The ordinary dihedral CI classification, including the degenerate case. -/
def ordinaryDihedralCIClassification : Prop :=
  (∀ n : ℕ, 2 ≤ n →
    (undirectedCIGroup (DihedralGroup n) ↔
      n = 2 ∨ n = 9 ∨ oddSquarefree n)) ∧
  undirectedCIGroup (DihedralGroup 1)

end DihedralClassification

section CyclicResidueBlocks

/-- The two residue classes modulo `p` represented in `ZMod n`. -/
def residuePlusMinusOne (p n : ℕ) : Set (ZMod n) :=
  {z | (∃ a : ZMod n, z = 1 + (p : ZMod n) * a) ∨
    (∃ a : ZMod n, z = -1 + (p : ZMod n) * a)}

def pairOfMultiples (k n : ℕ) : Set (ZMod n) :=
  ({(k : ZMod n), -(k : ZMod n)} : Set (ZMod n))

/-- The prime-square and `C₂₇` cyclic residue-block defects. -/
def cyclicResidueBlockDefects : Prop :=
  (∀ p : ℕ, Nat.Prime p → 5 ≤ p →
    let A := ZMod (p ^ 2)
    let U : Set A := residuePlusMinusOne p (p ^ 2)
    let S : Set A := U ∪ pairOfMultiples p (p ^ 2)
    let T : Set A := U ∪ pairOfMultiples (2 * p) (p ^ 2)
    additiveInverseClosed S ∧
    additiveIdentityFree S ∧
    additiveInverseClosed T ∧
    additiveIdentityFree T ∧
    additiveCayleyGraphIsomorphism S T ∧
    (¬ ∃ α : A ≃+ A, Set.image α S = T)) ∧
  (let A := ZMod 27
   let U : Set A := residuePlusMinusOne 9 27
   let S : Set A := U ∪ pairOfMultiples 3 27
   let T : Set A := U ∪ pairOfMultiples 6 27
   additiveInverseClosed S ∧
   additiveIdentityFree S ∧
   additiveInverseClosed T ∧
   additiveIdentityFree T ∧
   additiveCayleyGraphIsomorphism S T ∧
   (¬ ∃ α : A ≃+ A, Set.image α S = T))

end CyclicResidueBlocks

end MathlibPlus.Open.Research.BatchQ0052
