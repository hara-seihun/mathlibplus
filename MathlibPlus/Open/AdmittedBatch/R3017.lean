import Mathlib

namespace MathlibPlus.Open.AdmittedBatch.R3017

abbrev Dihedral (n : ℕ) := DihedralGroup n

/-- The directed Cayley relation with connection set `S`. -/
def directedCayleyRelation {G : Type*} [Group G]
    (S : Set G) (x y : G) : Prop := x⁻¹ * y ∈ S

def relationLabeledIsomorphism {G : Type*} [Group G]
    {k : ℕ} (S T : Fin k → Set G) : Prop :=
  ∃ e : G ≃ G, ∀ (i : Fin k) (x y : G),
    directedCayleyRelation (S i) x y ↔
      directedCayleyRelation (T i) (e x) (e y)

def carriesConnectionSets {G : Type*} [Group G]
    {k : ℕ} (S T : Fin k → Set G) (a : G ≃* G) : Prop :=
  ∀ i : Fin k, a '' (S i) = T i

/-- The one-relation DCI hypothesis, including arbitrary overlaps and loops. -/
def oddSquarefreeDihedralDCI : Prop :=
  ∀ N : ℕ, N > 1 → Odd N → Squarefree N →
    ∀ S T : Set (Dihedral N),
      (∃ e : Dihedral N ≃ Dihedral N, ∀ x y,
        directedCayleyRelation S x y ↔
          directedCayleyRelation T (e x) (e y)) →
      ∃ a : Dihedral N ≃* Dihedral N, a '' S = T

/-- A loop-free connection set avoids the identity tag. -/
def loopFreeConnectionSet {G : Type*} [Group G] (S : Set G) : Prop :=
  (1 : G) ∉ S

def tagsAvoidIdentity {G : Type*} [Group G]
    {k : ℕ} (S : Fin k → Set G) : Prop :=
  ∀ i, loopFreeConnectionSet (S i)

/--
Prime-tag tuple lemma on odd square-free dihedral groups.  The sets are not
required to be disjoint, and may contain the identity; loop-free tagged
encodings are the separately named `tagsAvoidIdentity` case.
-/
def primeTagTupleLemma : Prop :=
  ∀ n k : ℕ, n > 1 → Odd n → Squarefree n →
    oddSquarefreeDihedralDCI →
    ∀ S T : Fin k → Set (Dihedral n),
      relationLabeledIsomorphism S T →
      ∃ a : Dihedral n ≃* Dihedral n, carriesConnectionSets S T a

end MathlibPlus.Open.AdmittedBatch.R3017
