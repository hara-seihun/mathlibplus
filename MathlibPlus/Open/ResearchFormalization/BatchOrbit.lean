import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchOrbit

/-- The orbit of a point under a subgroup of permutations of a finite carrier. -/
noncomputable def subgroupOrbit {B : Type*} (H : Subgroup (Equiv.Perm B)) (x : B) : Set B :=
  {y | ∃ g : Equiv.Perm B, g ∈ H ∧ g x = y}

/-- A finite group whose cardinality is a power of the prime `r`. -/
def isFiniteRGroup {B : Type*} [Fintype B] (r : ℕ)
    (V : Subgroup (Equiv.Perm B)) : Prop :=
  ∃ k : ℕ, Nat.card V = r ^ k

/-- The set of orbit blocks of a subgroup on the carrier. -/
noncomputable def orbitPartition {B : Type*} (H : Subgroup (Equiv.Perm B)) : Set (Set B) :=
  {s | ∃ x : B, s = subgroupOrbit H x}

/--
Prime-square orbit squeeze (Claim 37069): an `r`-point subgroup orbit cannot
sit inside a larger orbit of a finite `r`-group on a block of size below `r²`;
the final clause records the stated coincidence of the two order-`r` orbit
partitions.
-/
def primeSquareOrbitSqueeze : Prop :=
  ∀ {B : Type*} [Fintype B] (r : ℕ)
    (V P Q : Subgroup (Equiv.Perm B)),
    Nat.Prime r →
    isFiniteRGroup r V →
    (P ≤ V →
      (∃ x : B, (subgroupOrbit P x).ncard = r) →
      Fintype.card B < r ^ 2 →
      ∀ x y : B,
        (subgroupOrbit P x).ncard = r →
        subgroupOrbit P x ⊆ subgroupOrbit V y →
        (subgroupOrbit V y).ncard = r ∧ subgroupOrbit V y = subgroupOrbit P x) ∧
    (P ≤ V → Q ≤ V →
      Nat.card P = r → Nat.card Q = r →
      (∀ x : B, (subgroupOrbit P x).ncard = r) →
      (∀ x : B, (subgroupOrbit Q x).ncard = r) →
      orbitPartition P = orbitPartition Q)

end MathlibPlus.Open.ResearchFormalization.BatchOrbit
