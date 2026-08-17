import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim31958

abbrev Q12 := QuaternionGroup 3
abbrev Q12p (p : ℕ) := QuaternionGroup (3 * p)
abbrev CayleyVertex (p : ℕ) := Q12p p

def inverseClosed {G : Type*} [Group G] (S : Set G) : Prop :=
  ∀ s, s ∈ S → s⁻¹ ∈ S

def cayleyAdj {G : Type*} [Group G] (S : Set G) (x y : G) : Prop :=
  x ≠ y ∧ x⁻¹ * y ∈ S

def cayleyGraph {G : Type*} [Group G] (S : Set G) : SimpleGraph G :=
  SimpleGraph.fromRel (cayleyAdj S)

def graphAutomorphism {V : Type*} (G : SimpleGraph V) (f : V → V) : Prop :=
  Function.Bijective f ∧ ∀ x y, G.Adj x y ↔ G.Adj (f x) (f y)

def subgroupGraphAutomorphism {V : Type*} (G : SimpleGraph V)
    (H : Subgroup (Equiv.Perm V)) : Prop :=
  ∀ h : H, graphAutomorphism G h.1

def regularPermutationSubgroup {V A : Type*} [Group A]
    (H : Subgroup (Equiv.Perm V)) : Prop :=
  Nonempty (H ≃* A) ∧ ∀ x y : V, ∃! h : H, h.1 x = y

def characteristicSubgroupInGroup {H : Type*} [Group H]
    (C : Subgroup H) : Prop :=
  ∀ φ : H ≃* H, ∀ c : H, c ∈ C ↔ φ c ∈ C

def subgroupOrbit {V : Type*} {H : Subgroup (Equiv.Perm V)}
    (C : Subgroup H) (x : V) : Set V :=
  {y | ∃ c : C, ((c.1 : H) : Equiv.Perm V) x = y}

def characteristicPrimeBlockSystem (p : ℕ)
    {V : Type*} (R : Subgroup (Equiv.Perm V))
    (blocks : Fin 12 → Set V) : Prop :=
  ∃ C : Subgroup R,
    Nat.card C = p ∧
      characteristicSubgroupInGroup C ∧
        (∀ i : Fin 12, (blocks i).Nonempty) ∧
          (∀ i : Fin 12, Set.ncard (blocks i) = p) ∧
            (∀ i : Fin 12, ∃ x : V,
              subgroupOrbit C x = blocks i) ∧
              (∀ x : V, ∃ i : Fin 12, x ∈ blocks i) ∧
                (∀ i j : Fin 12, i ≠ j → Disjoint (blocks i) (blocks j))

def blockActionCompatible {V : Type*}
    (R : Subgroup (Equiv.Perm V)) (blocks : Fin 12 → Set V)
    (q : R →* Equiv.Perm (Fin 12)) : Prop :=
  ∀ r : R, ∀ i : Fin 12,
    (r.1 : Equiv.Perm V) '' blocks i = blocks (q r i)

def q12RegularOn (R : Subgroup (Equiv.Perm (Fin 12))) : Prop :=
  regularPermutationSubgroup (A := Q12) R

def fourTriplePartition
    (qR : Subgroup (Equiv.Perm (Fin 12)))
    (qT : Subgroup (Equiv.Perm (Fin 12)))
    (parts : Fin 4 → Set (Fin 12)) : Prop :=
  (∀ j : Fin 4, (parts j).Nonempty ∧ Set.ncard (parts j) = 3) ∧
    (∀ j k : Fin 4, j ≠ k → Disjoint (parts j) (parts k)) ∧
      (∀ x : Fin 12, ∃ j : Fin 4, x ∈ parts j) ∧
        (∀ r : qR, ∀ j : Fin 4,
          ∃ k : Fin 4,
            (r.1 : Equiv.Perm (Fin 12)) '' parts j = parts k) ∧
          (∀ t : qT, ∀ j : Fin 4,
            ∃ k : Fin 4,
              (t.1 : Equiv.Perm (Fin 12)) '' parts j = parts k)

def pullbackBlock {V : Type*} (blocks : Fin 12 → Set V)
    (parts : Fin 4 → Set (Fin 12)) (j : Fin 4) : Set V :=
  {x | ∃ i : Fin 12, i ∈ parts j ∧ x ∈ blocks i}

def fourBlockPartitionOnVertex {V : Type*}
    (parts : Fin 4 → Set V) : Prop :=
  (∀ j : Fin 4, (parts j).Nonempty) ∧
    (∀ j k : Fin 4, j ≠ k → Disjoint (parts j) (parts k)) ∧
      (∀ x : V, ∃ j : Fin 4, x ∈ parts j)

def oddNatural (n : ℕ) : Prop :=
  ∃ k : ℕ, n = 2 * k + 1

def characteristicOddHall (p : ℕ) {R : Type*} [Group R]
    (K : Subgroup R) : Prop :=
  characteristicSubgroupInGroup K ∧
    oddNatural (Nat.card K) ∧
      Nat.Coprime (Nat.card K) (12 * p / Nat.card K)

def isBlockStabilizer {V : Type*}
    {R : Subgroup (Equiv.Perm V)}
    (K : Subgroup R) (B : Set V) : Prop :=
  ∀ r : R, r ∈ K ↔
    (r.1 : Equiv.Perm V) '' B = B

def uniqueThreePrimeHallBlockStabilizer
    (p : ℕ) {V : Type*} (R : Subgroup (Equiv.Perm V))
    (B : Set V) : Prop :=
  ∃ K : Subgroup R,
    Nat.card K = 3 * p ∧
      isBlockStabilizer K B ∧
        characteristicOddHall p K ∧
          ∀ L : Subgroup R,
            Nat.card L = 3 * p →
              characteristicOddHall p L → L = K

def normalBranchHallConclusion (p : ℕ)
    {V : Type*} (R : Subgroup (Equiv.Perm V))
    (blocks : Fin 12 → Set V) (parts : Fin 4 → Set (Fin 12)) : Prop :=
  ∀ j : Fin 4,
    Set.ncard (pullbackBlock blocks parts j) = 3 * p ∧
      uniqueThreePrimeHallBlockStabilizer p R
        (pullbackBlock blocks parts j)

/-- Claim 31958: in the normal quotient branch, four quotient triples pull
back to four common `3p` blocks, and each such block has the unique
characteristic odd Hall `C₃p` stabilizer in both regular copies. -/
def normalQuotientBranchGivesFourHallBlocks : Prop :=
  ∀ (p : ℕ),
    Nat.Prime p → 3 < p →
      (∀ q : ℕ, Nat.Prime q → q % 2 = 1 → q ∣ (12 * p) → q ≤ p) →
        ∀ S : Set (CayleyVertex p),
          inverseClosed S →
            ∀ R T : Subgroup (Equiv.Perm (CayleyVertex p)),
              regularPermutationSubgroup (A := Q12p p) R →
                regularPermutationSubgroup (A := Q12p p) T →
                  subgroupGraphAutomorphism (cayleyGraph S) R →
                    subgroupGraphAutomorphism (cayleyGraph S) T →
                      ∀ blocks : Fin 12 → Set (CayleyVertex p),
                        characteristicPrimeBlockSystem p R blocks →
                          characteristicPrimeBlockSystem p T blocks →
                            ∀ qR : R →* Equiv.Perm (Fin 12),
                              ∀ qT : T →* Equiv.Perm (Fin 12),
                                blockActionCompatible R blocks qR →
                                  blockActionCompatible T blocks qT →
                                    q12RegularOn (Subgroup.map qR ⊤) →
                                      q12RegularOn (Subgroup.map qT ⊤) →
                                        ∀ parts : Fin 4 → Set (Fin 12),
                                          fourTriplePartition
                                            (Subgroup.map qR ⊤)
                                            (Subgroup.map qT ⊤) parts →
                                            fourBlockPartitionOnVertex
                                              (pullbackBlock blocks parts) ∧
                                              normalBranchHallConclusion
                                                p R blocks parts ∧
                                                normalBranchHallConclusion
                                                  p T blocks parts

end MathlibPlus.Open.ResearchFormalization.Claim31958
