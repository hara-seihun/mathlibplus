import MathlibPlus.Open.ResearchFormalizationBatch_01a003cb_d995_7564_b82d_d782ff7e0528

open scoped Classical
noncomputable section

namespace MathlibPlus.Open.Research.R1494NoTwoPointBlock37826

open MathlibPlus.Open.ResearchFormalizationBatch

abbrev Vertex (r : ℕ) := HyperplaneTriadGroup r

def graphAutomorphism {r : ℕ}
    (U : Submodule (ZMod 2) (BinaryVector r))
    (p : Equiv.Perm (Vertex r)) : Prop :=
  ∀ x y,
    (hyperplaneTriadCayleyGraph r U).Adj (p x) (p y) ↔
      (hyperplaneTriadCayleyGraph r U).Adj x y

def twoPointGraphBlockSystem (r : ℕ)
    (U : Submodule (ZMod 2) (BinaryVector r))
    (blocks : Set (Set (Vertex r))) : Prop :=
  (∀ B, B ∈ blocks → B.ncard = 2) ∧
    (∀ x : Vertex r, ∃! B : Set (Vertex r), B ∈ blocks ∧ x ∈ B) ∧
      (∀ p : Equiv.Perm (Vertex r), graphAutomorphism U p →
        ∀ B, B ∈ blocks → p '' B ∈ blocks)

/-- Claim 37826: the full automorphism group of the hyperplane-triad graph
preserves no two-point block system. -/
def claim37826 : Prop :=
  ∀ (r : ℕ) (U : Submodule (ZMod 2) (BinaryVector r)),
    3 ≤ r → isBinaryHyperplane r U →
      ¬ ∃ blocks : Set (Set (Vertex r)),
        twoPointGraphBlockSystem r U blocks

end MathlibPlus.Open.Research.R1494NoTwoPointBlock37826
