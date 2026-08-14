import Mathlib

noncomputable section

namespace MathlibPlus.Open.Research.Batch_019ffee1_8bc1_7a1b_84dd_470709b895e3

abbrev OrbitPoint := ZMod 8 × ZMod 35

/-- The two permutations used by the regular source group. -/
def sourceA : Equiv.Perm OrbitPoint :=
  { toFun := fun p => (p.1, p.2 + 1)
    invFun := fun p => (p.1, p.2 - 1)
    left_inv := by
      intro p
      ext <;> simp
    right_inv := by
      intro p
      ext <;> simp }

def sourceB : Equiv.Perm OrbitPoint :=
  { toFun := fun p => (p.1 + 1, -p.2)
    invFun := fun p => (p.1 - 1, -p.2)
    left_inv := by
      intro p
      ext <;> simp
    right_inv := by
      intro p
      ext <;> simp }

def sourceGroup : Subgroup (Equiv.Perm OrbitPoint) :=
  Subgroup.closure ({sourceA, sourceB} : Set (Equiv.Perm OrbitPoint))

def regularOnBase : Prop :=
  ∀ p : OrbitPoint, ∃! g : sourceGroup, g.1 (0, 0) = p

/-- The direct permutation-group calculation for the degree-280 regular action. -/
def claim_35560 : Prop :=
  Fintype.card OrbitPoint = 280 ∧
    sourceA ^ 35 = 1 ∧
    sourceB ^ 8 = 1 ∧
    sourceB * sourceA * sourceB⁻¹ = sourceA⁻¹ ∧
    regularOnBase

abbrev SwapTriple := ZMod 8 × ZMod 35 × ZMod 35

def transpositionOf (t : SwapTriple) : Equiv.Perm OrbitPoint :=
  Equiv.swap (t.1, t.2.1) (t.1, t.2.2)

def scoutPermutation (L : List SwapTriple) : Equiv.Perm OrbitPoint :=
  L.foldl (fun s t => s * transpositionOf t) 1

def permConjugate (s g : Equiv.Perm OrbitPoint) : Equiv.Perm OrbitPoint :=
  s⁻¹ * g * s

def targetGroup (L : List SwapTriple) : Subgroup (Equiv.Perm OrbitPoint) :=
  Subgroup.closure
    ({permConjugate (scoutPermutation L) sourceA,
      permConjugate (scoutPermutation L) sourceB} : Set (Equiv.Perm OrbitPoint))

def combinedGroup (L : List SwapTriple) : Subgroup (Equiv.Perm OrbitPoint) :=
  Subgroup.closure
    ({sourceA, sourceB,
      permConjugate (scoutPermutation L) sourceA,
      permConjugate (scoutPermutation L) sourceB} : Set (Equiv.Perm OrbitPoint))

def subgroupConjugateBy (K L : Subgroup (Equiv.Perm OrbitPoint))
    (s : Equiv.Perm OrbitPoint) : Prop :=
  ∀ g : Equiv.Perm OrbitPoint,
    g ∈ L ↔ ∃ k : Equiv.Perm OrbitPoint, k ∈ K ∧ g = permConjugate s k

def insideCombinedConjugacy (L : List SwapTriple) : Prop :=
  ∃ h : Equiv.Perm OrbitPoint,
    h ∈ combinedGroup L ∧ subgroupConjugateBy sourceGroup (targetGroup L) h

/-- The target regular group is a full-symmetric conjugate by construction; the
remaining scout question is exactly conjugacy with a conjugator in H. -/
def claim_35561 : Prop :=
  ∀ L : List SwapTriple,
    subgroupConjugateBy sourceGroup (targetGroup L) (scoutPermutation L)

/-- Blockwise transposition-list primitives for the eight scout patterns. -/
def blockSwapList (blocks : Finset (ZMod 8)) (x y : ZMod 35) : List SwapTriple :=
  blocks.toList.map (fun q => (q, x, y))

def allBlocks : Finset (ZMod 8) := Finset.univ
def firstFourBlocks : Finset (ZMod 8) := {0, 1, 2, 3}
def lastFourBlocks : Finset (ZMod 8) := {4, 5, 6, 7}
def evenBlocks : Finset (ZMod 8) := {0, 2, 4, 6}
def oddBlocks : Finset (ZMod 8) := {1, 3, 5, 7}

def patternSame01 : List SwapTriple := blockSwapList allBlocks 0 1
def patternSplit01_02 : List SwapTriple :=
  blockSwapList firstFourBlocks 0 1 ++ blockSwapList lastFourBlocks 0 2
def patternAlternating01_02 : List SwapTriple :=
  blockSwapList evenBlocks 0 1 ++ blockSwapList oddBlocks 0 2
def patternOne01 : List SwapTriple := blockSwapList {0} 0 1
def patternTwo01 : List SwapTriple := blockSwapList {0, 1} 0 1
def patternFour01 : List SwapTriple := blockSwapList firstFourBlocks 0 1
def patternFour012 : List SwapTriple :=
  patternFour01 ++ blockSwapList lastFourBlocks 0 2
def patternAntipodal01_23 : List SwapTriple :=
  blockSwapList firstFourBlocks 0 1 ++ blockSwapList lastFourBlocks 2 3

def scoutPatterns : List (List SwapTriple) :=
  [ patternSame01,
    patternSplit01_02,
    patternAlternating01_02,
    patternOne01,
    patternTwo01,
    patternFour01,
    patternFour012,
    patternAntipodal01_23 ]

/-- The eight listed patterns are the exact blockwise lists used by the scout. -/
def claim_35562 : Prop :=
  scoutPatterns =
    [ blockSwapList allBlocks 0 1,
      blockSwapList firstFourBlocks 0 1 ++ blockSwapList lastFourBlocks 0 2,
      blockSwapList evenBlocks 0 1 ++ blockSwapList oddBlocks 0 2,
      blockSwapList {0} 0 1,
      blockSwapList {0, 1} 0 1,
      blockSwapList firstFourBlocks 0 1,
      blockSwapList firstFourBlocks 0 1 ++ blockSwapList lastFourBlocks 0 2,
      blockSwapList firstFourBlocks 0 1 ++ blockSwapList lastFourBlocks 2 3 ]

end MathlibPlus.Open.Research.Batch_019ffee1_8bc1_7a1b_84dd_470709b895e3
