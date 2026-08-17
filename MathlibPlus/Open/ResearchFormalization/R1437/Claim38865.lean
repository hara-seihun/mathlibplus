import MathlibPlus.Open.ResearchFormalizationBatch_01a0014d

namespace MathlibPlus.Open.ResearchFormalization.R1437

open MathlibPlus.Open.ResearchFormalizationBatch_01a0014d

/-- The degree-six product-action wreath carrier on `C₆²`. -/
def localProductWreath6 (u : Equiv.Perm C6Squared) : Prop :=
  (∃ α β : Equiv.Perm (ZMod 6),
    ∀ h : C6Squared, u h = (α h.1, β h.2)) ∨
  (∃ α β : Equiv.Perm (ZMod 6),
    ∀ h : C6Squared, u h = (β h.2, α h.1))

/-- Independent blockwise product-action permutations on the two outer blocks. -/
def independentBlockwiseTwoClosure : Set (Equiv.Perm (C6Squared × Bool)) :=
  {f | ∃ u v : Equiv.Perm C6Squared,
    localProductWreath6 u ∧ localProductWreath6 v ∧
      f = blockwisePermutation u v}

/-- The binary two-closure of the actual kernel acting on the two blocks. -/
def twoClosure (N : Subgroup (Equiv.Perm (C6Squared × Bool))) :
    Set (Equiv.Perm (C6Squared × Bool)) :=
  {f | ∀ a b : C6Squared × Bool, ∃ x : Equiv.Perm (C6Squared × Bool),
    x ∈ N ∧ x a = f a ∧ x b = f b}

/-- The aligned independent product case supplied by the minimum-block setup. -/
def independentProductSetup
    (N : Subgroup (Equiv.Perm (C6Squared × Bool))) : Prop :=
  (∀ g : C6Squared, blockAction g ∈ N) ∧
    (∀ n : N, ∀ h : C6Squared, ∀ b : Bool,
      ((n : Equiv.Perm (C6Squared × Bool)) (h, b)).2 = b) ∧
    (∀ f : Equiv.Perm (C6Squared × Bool),
      f ∈ independentBlockwiseTwoClosure → f ∈ twoClosure N)

/-- Claim 38865: after the two local `C₆²` factors have been aligned, every
centralizing involutory block swap is one of the 36 displayed shifts, and the
shifts are conjugate inside the actual binary two-closure. -/
def claim38865 : Prop :=
  Fintype.card C6Squared = 36 ∧
    (∀ (f : Equiv.Perm (C6Squared × Bool)),
      IsBlockSwap f → IsInvolution f → CentralizesBlockAction f →
        ∃! a : C6Squared,
          (∀ h : C6Squared, f (h, false) = (h + a, true)) ∧
          (∀ h : C6Squared, f (h, true) = (h - a, false))) ∧
    (∀ (N : Subgroup (Equiv.Perm (C6Squared × Bool))),
      independentProductSetup N →
        ∀ a : C6Squared,
          independentBlockwiseTwoClosure (secondBlockTranslation a) ∧
            CentralizesBlockAction (secondBlockTranslation a) ∧
            secondBlockTranslation a ∈ twoClosure N ∧
            (∀ x,
              secondBlockTranslation a (unshiftedBlockSwap
                ((secondBlockTranslation a).symm x)) = complementShift a x)) ∧
    (∀ a b : C6Squared, complementShift a = complementShift b ↔ a = b)

end MathlibPlus.Open.ResearchFormalization.R1437
