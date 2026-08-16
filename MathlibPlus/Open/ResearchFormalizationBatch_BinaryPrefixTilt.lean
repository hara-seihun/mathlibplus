import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalizationBatch_BinaryPrefixTilt

/-- A word `u` is a prefix of `v` when `v` is obtained by appending a suffix. -/
def isBinaryPrefix (u v : List Bool) : Prop :=
  ∃ t : List Bool, u ++ t = v

/-- The concrete prefix-free condition on a finite set of binary words. -/
def isPrefixFree (C : Finset (List Bool)) : Prop :=
  ∀ ⦃u v : List Bool⦄, u ∈ C → v ∈ C → u ≠ v →
    ¬ isBinaryPrefix u v ∧ ¬ isBinaryPrefix v u

/-- Kraft completeness for a binary prefix code. -/
def kraftSum (C : Finset (List Bool)) : ℝ :=
  ∑ w ∈ C, ((1 : ℝ) / 2) ^ w.length

def isCompleteBinaryPrefixCode (C : Finset (List Bool)) : Prop :=
  isPrefixFree C ∧ kraftSum C = 1

/-- The two concrete complete binary prefix codes from the admitted claim. -/
def Cminus : Finset (List Bool) :=
  {[false, false], [false, true], [true, false], [true, true]}

def Cplus : Finset (List Bool) :=
  {[false], [true, false], [true, true, false], [true, true, true, false],
    [true, true, true, true]}

def partitionSum (C : Finset (List Bool)) (q : ℝ) : ℝ :=
  ∑ w ∈ C, q ^ w.length

def Zminus (q : ℝ) : ℝ := partitionSum Cminus q

def Zplus (q : ℝ) : ℝ := partitionSum Cplus q

/-- Claim 10539: the second collision is at the positive golden-ratio tilt,
separate from the Kraft collision at `q = 1/2`. -/
def claim10539_secondExactEqualityAtPositiveRealTilt : Prop :=
  isCompleteBinaryPrefixCode Cminus ∧
    isCompleteBinaryPrefixCode Cplus ∧
    Cminus ≠ Cplus ∧
    let qstar : ℝ := (Real.sqrt 5 - 1) / 2
    let sstar : ℝ := -Real.log qstar
    sstar > 0 ∧
      sstar = Real.log ((1 + Real.sqrt 5) / 2) ∧
      Real.exp (-sstar) = qstar ∧
      Zplus qstar = Zminus qstar ∧
      Zplus (Real.exp (-sstar)) = Zminus (Real.exp (-sstar)) ∧
      qstar ≠ (1 / 2 : ℝ)

end MathlibPlus.Open.ResearchFormalizationBatch_BinaryPrefixTilt

end
