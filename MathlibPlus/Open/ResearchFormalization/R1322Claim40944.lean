import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1322

/-- The translation subgroup of the cyclic permutation action on `ZMod n`. -/
def translationSubgroup (n : ℕ) : Subgroup (Equiv.Perm (ZMod n)) :=
  Subgroup.closure
    (Set.range (fun a : ZMod n => Equiv.addRight a))

/-- The holomorph of the displayed translation copy, as its symmetric-group
normalizer. -/
def translationHolomorph (n : ℕ) : Subgroup (Equiv.Perm (ZMod n)) :=
  Subgroup.normalizer (translationSubgroup n : Set (Equiv.Perm (ZMod n)))

/-- Regularity of a permutation subgroup on its underlying point set. -/
def isRegularPermutationSubgroup {α : Type*}
    (H : Subgroup (Equiv.Perm α)) : Prop :=
  ∀ x y : α, ∃! h : H, (h : Equiv.Perm α) x = y

/-- The exact single-cycle assertion used for the `p²` affine permutation. -/
def isOneCycle {α : Type*} (n : ℕ) (d : Equiv.Perm α) : Prop :=
  ∀ x y : α, ∃! k : Fin n, (d ^ (k.1 : ℕ)) x = y

/-- Claim 40944: the explicit affine counterexample to square-free holomorph
uniqueness, with the holomorph, iterate, order, cycle, regular subgroup, and
non-translation conclusions all retained. -/
def claim40944 : Prop :=
  ∀ p : ℕ, Nat.Prime p → Odd p →
    let n := p ^ 2
    ∃ d : Equiv.Perm (ZMod n),
      (∀ x : ZMod n,
        d x = ((1 : ZMod n) + (p : ZMod n)) * x + 1) ∧
      d ∈ translationHolomorph n ∧
      (∀ x : ZMod n, (d ^ p) x = x + (p : ZMod n)) ∧
      orderOf d = n ∧
      isOneCycle n d ∧
      isRegularPermutationSubgroup
        (Subgroup.closure ({d} : Set (Equiv.Perm (ZMod n)))) ∧
      Subgroup.closure ({d} : Set (Equiv.Perm (ZMod n))) ≠
        translationSubgroup n

end MathlibPlus.Open.ResearchFormalization.R1322
