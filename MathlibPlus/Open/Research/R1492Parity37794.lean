import Mathlib

open scoped Classical
noncomputable section

namespace MathlibPlus.Open.Research.R1492Parity37794

abbrev C28 := ZMod 28
abbrev C14Image := Set C28

def evenSubgroupImage : C14Image :=
  {x | ∃ y : C28, x = (2 : C28) * y}

def parityCharacter (x : C28) : (ZMod 3)ˣ :=
  if x ∈ evenSubgroupImage then 1 else -1

/-- Claim 37794: the even index-two subgroup is intrinsic in C28, and the
parity character into the automorphism group of C3 is invariant under every
automorphism. -/
def claim37794 : Prop :=
  Set.ncard evenSubgroupImage = 14 ∧
    (∀ K : AddSubgroup C28,
      Nat.card K = 14 → (K : Set C28) = evenSubgroupImage) ∧
      (∀ φ : C28 ≃+ C28,
        Set.image φ evenSubgroupImage = evenSubgroupImage ∧
          ∀ x : C28, parityCharacter (φ x) = parityCharacter x)

end MathlibPlus.Open.Research.R1492Parity37794
