import Mathlib
import MathlibPlus.Combinatorics.Claim30192

namespace MathlibPlus.Open.ResearchFormalization.R1144Claim30193

noncomputable section

open MathlibPlus.Combinatorics.Claim30192

abbrev C7 := ZMod 7

def fanoLineSystem (F : Set (Set C7)) : Prop :=
  F.Finite ∧
    F.ncard = 7 ∧
      (∀ L : Set C7, L ∈ F → L.Finite ∧ L.ncard = 3) ∧
        (∀ x y : C7, x ≠ y →
          ∃! L : Set C7,
            L ∈ F ∧ L.Finite ∧ L.ncard = 3 ∧ x ∈ L ∧ y ∈ L)

def fanoBaseA : Set C7 :=
  ({0, 1, 3} : Set C7)

def fanoBaseB : Set C7 :=
  ({0, 2, 3} : Set C7)

def fanoSystemA : Set (Set C7) :=
  translationDevelopment fanoBaseA

def fanoSystemB : Set (Set C7) :=
  translationDevelopment fanoBaseB

def cyclicFanoLineSystem (B : Set C7) (F : Set (Set C7)) : Prop :=
  F = translationDevelopment B ∧ fanoLineSystem F

/-- Claim 30193: the two displayed cyclic developments are seven-line
three-subset Fano systems on the exact additive `ZMod 7` carrier. -/
def claim30193 : Prop :=
  cyclicFanoLineSystem fanoBaseA fanoSystemA ∧
    cyclicFanoLineSystem fanoBaseB fanoSystemB

end

end MathlibPlus.Open.ResearchFormalization.R1144Claim30193
