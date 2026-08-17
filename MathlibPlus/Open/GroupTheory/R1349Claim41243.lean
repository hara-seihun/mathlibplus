import MathlibPlus.Open.GroupTheory.CayleyCIBatch
import MathlibPlus.Open.GroupTheory.RegularBlockSubgroups

namespace MathlibPlus.Open.GroupTheory.R1349Claim41243

abbrev C7 := Multiplicative (ZMod 7)
abbrev Q12 := QuaternionGroup 3
abbrev G := C7 × Q12

def pureBlockSystem (B : Finset (Set G)) : Prop :=
  MathlibPlus.Open.finiteBlockSystem B ∧
    B.card = 7 ∧ ∀ U ∈ B, U.ncard = 12

def preservesBlockSystem
    (L : Subgroup (Equiv.Perm G)) (B : Finset (Set G)) : Prop :=
  ∀ h : Equiv.Perm G, h ∈ L → ∀ U ∈ B, h '' U ∈ B

def blockKernel
    (Y : Subgroup (Equiv.Perm G)) (B : Finset (Set G)) :
    Subgroup (Equiv.Perm G) :=
  { carrier := {p | p ∈ Y ∧ ∀ U ∈ B, p '' U = U}
    one_mem' := by
      constructor
      · exact Y.one_mem
      · intro U hU
        simp
    mul_mem' := by
      intro p q hp hq
      constructor
      · exact Y.mul_mem hp.1 hq.1
      · intro U hU
        calc
          (p * q : Equiv.Perm G) '' U = p '' (q '' U) := by
            simpa [Equiv.Perm.coe_mul] using
              (Set.image_image (p : G → G) (q : G → G) U).symm
          _ = p '' U := congrArg (fun V : Set G => p '' V) (hq.2 U hU)
          _ = U := hp.2 U hU
    inv_mem' := by
      intro p hp
      constructor
      · exact Y.inv_mem hp.1
      · intro U hU
        have h := congrArg (fun V : Set G => (p⁻¹ : Equiv.Perm G) '' V) (hp.2 U hU)
        simpa using h.symm }

def regularQ12OnBlock
    (H : Subgroup (Equiv.Perm G)) (U : Set G) : Prop :=
  Nonempty (H ≃* Q12) ∧
    (∀ h : H, (h : Equiv.Perm G) '' U = U) ∧
      ∀ x y : G, x ∈ U → y ∈ U →
        ∃! h : H, (h : Equiv.Perm G) x = y

def regularQ12OnEveryBlock
    (H : Subgroup (Equiv.Perm G)) (B : Finset (Set G)) : Prop :=
  ∀ U ∈ B, regularQ12OnBlock H U

def inducedRegularC7
    (L : Subgroup (Equiv.Perm G)) (B : Finset (Set G)) : Prop :=
  ∃ π : L →* Equiv.Perm (MathlibPlus.Open.blockType B),
    (∀ l : L, ∀ U : MathlibPlus.Open.blockType B,
      ((π l) U).1 = (l : Equiv.Perm G) '' U.1) ∧
      MathlibPlus.Open.regularSubgroupOnBlocks π.range ∧
        Nonempty (π.range ≃* C7)

def pairGeneratedGroup
    (R T : Subgroup (Equiv.Perm G)) : Subgroup (Equiv.Perm G) :=
  Subgroup.closure ((R : Set (Equiv.Perm G)) ∪ (T : Set (Equiv.Perm G)))

def pureQ12SevenBlockPair
    (S : Set G) (B : Finset (Set G))
    (R T : Subgroup (Equiv.Perm G)) : Prop :=
  pureBlockSystem B ∧
    MathlibPlus.Open.GroupTheory.CayleyCI.isRegularRSubgroup
      (MathlibPlus.Open.GroupTheory.CayleyCI.undirectedCayleyAdj S) R ∧
    MathlibPlus.Open.GroupTheory.CayleyCI.isRegularRSubgroup
      (MathlibPlus.Open.GroupTheory.CayleyCI.undirectedCayleyAdj S) T ∧
    preservesBlockSystem R B ∧
    preservesBlockSystem T B ∧
    inducedRegularC7 R B ∧
    inducedRegularC7 T B ∧
    let Y := pairGeneratedGroup R T
    let K := blockKernel Y B
    regularQ12OnEveryBlock (R ⊓ K) B ∧
      regularQ12OnEveryBlock (T ⊓ K) B

/-- Any two regular `C₇ × Q₁₂` copies satisfying the arbitrary common
seven-block pure-`Q₁₂` system are conjugate inside the graph automorphism
relation. -/
def claim41243 : Prop :=
  Fintype.card C7 = 7 ∧
    Fintype.card Q12 = 12 ∧
      Fintype.card G = 84 ∧
        ∀ S : Set G,
          (1 : G) ∉ S →
          MathlibPlus.Open.GroupTheory.CayleyCI.inverseClosed S →
          ∀ B : Finset (Set G),
            ∀ R T : Subgroup (Equiv.Perm G),
              pureQ12SevenBlockPair S B R T →
                MathlibPlus.Open.GroupTheory.CayleyCI.conjugateRegularCopies
                  (MathlibPlus.Open.GroupTheory.CayleyCI.undirectedCayleyAdj S) R T

end MathlibPlus.Open.GroupTheory.R1349Claim41243
