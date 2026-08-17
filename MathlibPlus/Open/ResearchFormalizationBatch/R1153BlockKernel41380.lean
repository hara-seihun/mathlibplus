import MathlibPlus.Open.ResearchFormalization.R1275

open scoped Classical
noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R1153BlockKernel41380

open MathlibPlus.Open.ResearchFormalization

/-- A finite nontrivial block partition preserved by a permutation subgroup. -/
def blockSystem {G : Type*} [Fintype G] [DecidableEq G]
    (X : Subgroup (Equiv.Perm G)) (blocks : Finset (Finset G)) : Prop :=
  1 < blocks.card ∧
    (∀ B ∈ blocks,
      B.Nonempty ∧ 1 < B.card ∧ B.card < Fintype.card G) ∧
      (∀ x : G, ∃! B : Finset G, B ∈ blocks ∧ x ∈ B) ∧
        (∀ g : X, ∀ B ∈ blocks,
          ∃ C : Finset G, C ∈ blocks ∧
            Finset.image (g : Equiv.Perm G) B = C)

/-- The exact block-action-kernel predicate, kept separate from the subgroup
parameter so that no constructed proof-bearing subgroup is hidden. -/
def isBlockActionKernel {G : Type*} [Fintype G] [DecidableEq G]
    (X K : Subgroup (Equiv.Perm G)) (blocks : Finset (Finset G)) : Prop :=
  ∀ k : Equiv.Perm G,
    k ∈ K ↔ k ∈ X ∧ ∀ B ∈ blocks,
      Finset.image k B = B

def blockStabilizerSet {G : Type*} [Fintype G] [DecidableEq G]
    (R : Subgroup (Equiv.Perm G)) (B : Finset G) : Set (Equiv.Perm G) :=
  {r | r ∈ R ∧ Finset.image r B = B}

def copyKernelIntersection {G : Type*} [Fintype G]
    (R K : Subgroup (Equiv.Perm G)) : Set (Equiv.Perm G) :=
  {r | r ∈ R ∧ r ∈ K}

/-- Regularity of the copy-kernel intersection on each individual block. -/
def regularOnBlocks {G : Type*} [Fintype G] [DecidableEq G]
    (R K : Subgroup (Equiv.Perm G))
    (blocks : Finset (Finset G)) : Prop :=
  ∀ B ∈ blocks, ∀ x y : G,
    x ∈ B → y ∈ B →
      ∃! r : {p : Equiv.Perm G // p ∈ R ∧ p ∈ K},
        r.1 x = y

/-- The induced quotient action is transitive and has precisely the kernel
identified by `K`; this is the regularity criterion for the quotient copy. -/
def inducedQuotientRegular {G : Type*} [Fintype G] [DecidableEq G]
    (R K : Subgroup (Equiv.Perm G))
    (blocks : Finset (Finset G)) : Prop :=
  (∀ B C : Finset G, B ∈ blocks → C ∈ blocks →
    ∃ r : R, Finset.image (r : Equiv.Perm G) B = C) ∧
    (∀ r s : R,
      (∀ B ∈ blocks,
        Finset.image (r : Equiv.Perm G) B =
          Finset.image (s : Equiv.Perm G) B) →
        (r : Equiv.Perm G) * (s : Equiv.Perm G)⁻¹ ∈ K)

/-- Claim 41380: exact regular-copy block stabilizers, regularity on every
block, and regularity of both induced quotient copies. -/
def claim41380 : Prop :=
  ∀ (A : Type*) [Fintype A] [CommGroup A]
    (_hodd : Odd (Fintype.card A)),
    let G := A × QuaternionGroup 2
    ∀ (R T X K : Subgroup (Equiv.Perm G))
      (blocks : Finset (Finset G)),
      isRegularCopy R →
        isRegularCopy T →
          X = R ⊔ T →
            blockSystem X blocks →
              isBlockActionKernel X K blocks →
                (∀ B ∈ blocks,
                  blockStabilizerSet R B = copyKernelIntersection R K ∧
                    blockStabilizerSet T B = copyKernelIntersection T K) ∧
                  regularOnBlocks R K blocks ∧
                    regularOnBlocks T K blocks ∧
                      inducedQuotientRegular R K blocks ∧
                        inducedQuotientRegular T K blocks

end MathlibPlus.Open.ResearchFormalization.R1153BlockKernel41380
