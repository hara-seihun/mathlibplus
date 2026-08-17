import MathlibPlus.Open.GroupTheory.R1349Claim41243

namespace MathlibPlus.Open.GroupTheory.R1349Claim41227

open MathlibPlus.Open.GroupTheory.R1349Claim41243
open MathlibPlus.Open.GroupTheory.CayleyCI

/-- An internal direct-product decomposition of a permutation subgroup. -/
def internalDirectProduct
    (N P R : Subgroup (Equiv.Perm G)) : Prop :=
  N ≤ R ∧
    P ≤ R ∧
      N ⊔ P = R ∧
        N ⊓ P = ⊥ ∧
          ∀ n : N, ∀ p : P,
            (n : Equiv.Perm G) * (p : Equiv.Perm G) =
              (p : Equiv.Perm G) * (n : Equiv.Perm G)

/-- A complement to the block kernel inside the generated permutation group. -/
def complementToKernel
    (P K Y : Subgroup (Equiv.Perm G)) : Prop :=
  P ≤ Y ∧ K ≤ Y ∧ P ⊔ K = Y ∧ P ⊓ K = ⊥

/-- The actual induced permutation subgroups on a common block system agree. -/
def sameInducedBlockSubgroup
    (P Q : Subgroup (Equiv.Perm G)) (B : Finset (Set G)) : Prop :=
  ∃ πP : P →* Equiv.Perm (MathlibPlus.Open.blockType B),
    ∃ πQ : Q →* Equiv.Perm (MathlibPlus.Open.blockType B),
      (∀ p : P, ∀ U : MathlibPlus.Open.blockType B,
        ((πP p) U).1 = (p : Equiv.Perm G) '' U.1) ∧
        (∀ q : Q, ∀ U : MathlibPlus.Open.blockType B,
          ((πQ q) U).1 = (q : Equiv.Perm G) '' U.1) ∧
          πP.range = πQ.range

/-- Membership in the graph automorphism group of the displayed undirected
Cayley graph. -/
def graphAutomorphism
    (S : Set G) (g : Equiv.Perm G) : Prop :=
  ∀ x y : G,
    undirectedCayleyAdj S x y ↔
      undirectedCayleyAdj S (g x) (g y)

/-- Setwise preservation of the displayed common block system by one
permutation. -/
def preservesBlocksByPermutation
    (g : Equiv.Perm G) (B : Finset (Set G)) : Prop :=
  ∀ U ∈ B, g '' U ∈ B

/-- Conjugation of a permutation subgroup by a permutation of the points. -/
def conjugateSubgroup
    (g : Equiv.Perm G) (T : Subgroup (Equiv.Perm G)) :
    Subgroup (Equiv.Perm G) :=
  T.map (MulAut.conj g).toMonoidHom

/-- Claim 41227: after an actual-image quotient alignment of the second copy,
the generated group has the stated kernel, direct-product, complement, and
common degree-seven induced-subgroup normal form. -/
def claim41227 : Prop :=
  ∀ (S : Set G) (B : Finset (Set G))
    (R T : Subgroup (Equiv.Perm G)),
    pureQ12SevenBlockPair S B R T →
      ∃ (g : Equiv.Perm G) (T' : Subgroup (Equiv.Perm G)),
        g ∈ pairGeneratedGroup R T ∧
          graphAutomorphism S g ∧
            preservesBlocksByPermutation g B ∧
              T' = conjugateSubgroup g T ∧
                pureQ12SevenBlockPair S B R T' ∧
                  sameInducedBlockSubgroup R T' B ∧
                    ∃ (N M P Q : Subgroup (Equiv.Perm G)),
                      let Y := pairGeneratedGroup R T'
                      let K := blockKernel Y B
                      N = R ⊓ K ∧
                        M = T' ⊓ K ∧
                          N ≤ K ∧
                            M ≤ K ∧
                              Nonempty (N ≃* Q12) ∧
                                Nonempty (M ≃* Q12) ∧
                                  internalDirectProduct N P R ∧
                                    internalDirectProduct M Q T' ∧
                                      Nonempty (P ≃* C7) ∧
                                        Nonempty (Q ≃* C7) ∧
                                          complementToKernel P K Y ∧
                                            complementToKernel Q K Y ∧
                                              ∃ hK :
                                                  (K.comap Y.subtype).Normal,
                                                let _ :
                                                    (K.comap Y.subtype).Normal := hK
                                                Nonempty
                                                    ((Y ⧸
                                                        (K.comap Y.subtype))
                                                      ≃* C7) ∧
                                                  sameInducedBlockSubgroup
                                                    P Q B

end MathlibPlus.Open.GroupTheory.R1349Claim41227
