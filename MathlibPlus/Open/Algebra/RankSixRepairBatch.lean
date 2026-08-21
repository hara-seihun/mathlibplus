-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib

noncomputable section
open scoped BigOperators
open Set

namespace MathlibPlus.Open.RankSixBatch

abbrev rankSixD := Fin 2 → ZMod 3
abbrev rankSixB := Fin 4 → ZMod 3
abbrev rankSixV := rankSixD × rankSixB

def rankSixShift (b : rankSixB) : rankSixD :=
  fun i => if b 0 = 0 ∧ b 2 = 0 ∧ b 3 = 1 ∧ i = 1 then 1 else 0

def rankSixQFun : rankSixV → rankSixV :=
  fun p =>
    (p.1 + rankSixShift p.2,
      fun i => if i = 3 then p.2 i + (if p.2 2 = 2 then 1 else 0) else p.2 i)

def rankSixQ : rankSixV ≃ rankSixV :=
  Equiv.ofBijective rankSixQFun (by native_decide)

def rankSixTranslation (v : rankSixV) : Equiv.Perm rankSixV :=
  Equiv.addRight v

def rankSixNegation : Equiv.Perm rankSixV :=
  { toFun := fun v => -v
    invFun := fun v => -v
    left_inv := by intro v; simp
    right_inv := by intro v; simp }

def rankSixRegularCopy : Subgroup (Equiv.Perm rankSixV) :=
  Subgroup.closure (Set.range rankSixTranslation)

def rankSixConjugatedTranslation (v : rankSixV) : Equiv.Perm rankSixV :=
  (rankSixQ : Equiv.Perm rankSixV)⁻¹ * rankSixTranslation v * rankSixQ

def rankSixConjugatedCopy : Subgroup (Equiv.Perm rankSixV) :=
  Subgroup.closure (Set.range rankSixConjugatedTranslation)

def rankSixFullGroup : Subgroup (Equiv.Perm rankSixV) :=
  Subgroup.closure
    ((rankSixRegularCopy : Set (Equiv.Perm rankSixV)) ∪
      (rankSixConjugatedCopy : Set (Equiv.Perm rankSixV)) ∪ {rankSixNegation})

def rankSixLiteralCentralPlane : Subgroup (Equiv.Perm rankSixV) :=
  Subgroup.closure (Set.range (fun d : rankSixD => rankSixTranslation (d, 0)))

def rankSixZTranslation : Equiv.Perm rankSixV :=
  rankSixTranslation (0, fun i => if i = 0 then 1 else 0)

def permutationSubgroupRegular (K : Subgroup (Equiv.Perm rankSixV)) : Prop :=
  ∀ x y : rankSixV, ∃! g : K, (g : Equiv.Perm rankSixV) x = y

def elementaryAbelianRankSix (K : Subgroup (Equiv.Perm rankSixV)) : Prop := by
  classical
  letI := Fintype.ofFinite K
  exact
    Fintype.card K = 3 ^ 6 ∧
      (∀ g h : K, g * h = h * g) ∧
      (∀ g : K, g ^ 3 = 1)

def rankSixRegularPairWitness : Prop :=
  rankSixQ.toFun = rankSixQFun ∧
  elementaryAbelianRankSix rankSixRegularCopy ∧
  elementaryAbelianRankSix rankSixConjugatedCopy ∧
  permutationSubgroupRegular rankSixRegularCopy ∧
  permutationSubgroupRegular rankSixConjugatedCopy ∧
  rankSixLiteralCentralPlane ≤ rankSixRegularCopy ∧
  rankSixLiteralCentralPlane ≤ rankSixConjugatedCopy ∧
  rankSixZTranslation ∈ rankSixRegularCopy ∧
  rankSixZTranslation ∈ rankSixConjugatedCopy ∧
  rankSixRegularCopy ≤ rankSixFullGroup ∧
  rankSixConjugatedCopy ≤ rankSixFullGroup ∧
  rankSixNegation ∈ rankSixFullGroup

end MathlibPlus.Open.RankSixBatch
