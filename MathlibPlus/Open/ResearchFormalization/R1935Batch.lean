import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1935

open scoped BigOperators

abbrev F := ZMod 7
abbrev V := Fin 3 → F

def dot (n v : V) : F := ∑ i, n i * v i

def levelPartition (n : V) : Set (Set V) :=
  {B | ∃ a : F, B = {v | dot n v = a}}

def cosetPartition (W : Submodule F V) : Set (Set V) :=
  {B | ∃ v : V, B = {x | x - v ∈ W}}

def rankTwoCosetPartition (P : Set (Set V)) : Prop :=
  ∃ W : Submodule F V, Module.finrank F W = 2 ∧ P = cosetPartition W

def rankTwoPartitions : Set (Set (Set V)) :=
  {P | rankTwoCosetPartition P}

def nonzeroNormalPartitions : Set (Set (Set V)) :=
  {P | ∃ n : V, n ≠ 0 ∧ P = levelPartition n}

def preservesPartition (f : Equiv.Perm V) (P : Set (Set V)) : Prop :=
  ∀ B, B ∈ P → ∃ C, C ∈ P ∧ Set.image (fun v => f v) B = C

/-- Exact rank-two `C₇²` coset-partition census on `F₇³`. -/
def claim36350 : Prop :=
  (rankTwoPartitions = nonzeroNormalPartitions) ∧
    Set.Finite rankTwoPartitions ∧
    Set.ncard rankTwoPartitions = 57 ∧
    (∀ (n m : V), n ≠ 0 → m ≠ 0 →
      (levelPartition n = levelPartition m ↔
        ∃ c : F, c ≠ 0 ∧ m = c • n)) ∧
    (∀ (n : V), n ≠ 0 → ∀ (f : Equiv.Perm V),
      (preservesPartition f (levelPartition n) ↔
        ∀ v w : V, dot n v = dot n w → dot n (f v) = dot n (f w)))

end MathlibPlus.Open.ResearchFormalization.R1935
