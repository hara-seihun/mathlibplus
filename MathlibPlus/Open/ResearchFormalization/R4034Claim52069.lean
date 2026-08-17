import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R4034

noncomputable section

abbrev BooleanTable52069 := Fin 8 → ℚ
abbrev Table4_52069 := Fin 4 → ℚ
abbrev Table2_52069 := Fin 2 → ℚ
abbrev Table1_52069 := Fin 1 → ℚ

/-- The exact three-bit target from the R-3965 witness. -/
def target52069 : BooleanTable52069 :=
  ![(9 / 16 : ℚ), -1, 1, -3 / 16, -15 / 16, 1 / 4, 1 / 4, 9 / 16]

def activePolicyIndex52069 : Fin 4 := 3

def tangentShift52069 : ℚ := 15 / 512

def tightMask52069 : Fin 256 := 204

def saturatedRows52069 : Finset (Fin 8) := {1, 2}

/-- The root term used in the finite policy-matrix construction. -/
def rootMatrix2_52069 (i j : Fin 2) : ℚ :=
  if i = j then (1 / 4 : ℚ) else -1 / 4

def rootMatrix4_52069 (i j : Fin 4) : ℚ :=
  if i = j then (3 / 16 : ℚ) else -1 / 16

def rootMatrix8_52069 (i j : Fin 8) : ℚ :=
  if i = j then (7 / 64 : ℚ) else -1 / 64

/-- Child-block maps for inserting the queried coordinate at position zero. -/
def block0_4_52069 (i : Fin 4) : Bool :=
  if i.val = 0 ∨ i.val = 2 then false else true

def index0_4_52069 (i : Fin 4) : Fin 2 :=
  if i.val = 0 then 0 else
  if i.val = 1 then 0 else
  if i.val = 2 then 1 else 1

def block1_4_52069 (i : Fin 4) : Bool :=
  if i.val < 2 then false else true

def index1_4_52069 (i : Fin 4) : Fin 2 :=
  if i.val = 0 then 0 else
  if i.val = 1 then 1 else
  if i.val = 2 then 0 else 1

def block0_8_52069 (i : Fin 8) : Bool :=
  if i.val = 0 ∨ i.val = 2 ∨ i.val = 4 ∨ i.val = 6 then false else true

def index0_8_52069 (i : Fin 8) : Fin 4 :=
  if i.val = 0 then 0 else
  if i.val = 1 then 0 else
  if i.val = 2 then 1 else
  if i.val = 3 then 1 else
  if i.val = 4 then 2 else
  if i.val = 5 then 2 else
  if i.val = 6 then 3 else 3

/-- The one-bit policy matrix, including its zero-dimensional child term. -/
def policyMatrix1_52069 (i j : Fin 2) : ℚ :=
  rootMatrix2_52069 i j

/-- The two possible order-two policy matrices. -/
def policyMatrix2Coord0_52069 (i j : Fin 4) : ℚ :=
  rootMatrix4_52069 i j +
    if block0_4_52069 i = block0_4_52069 j then
      policyMatrix1_52069 (index0_4_52069 i) (index0_4_52069 j) / 2
    else 0

def policyMatrix2Coord1_52069 (i j : Fin 4) : ℚ :=
  rootMatrix4_52069 i j +
    if block1_4_52069 i = block1_4_52069 j then
      policyMatrix1_52069 (index1_4_52069 i) (index1_4_52069 j) / 2
    else 0

/-- The active index-three policy from the exact finite policy enumeration. -/
def activePolicyMatrix52069 (i j : Fin 8) : ℚ :=
  rootMatrix8_52069 i j +
    if block0_8_52069 i = block0_8_52069 j then
      policyMatrix2Coord1_52069 (index0_8_52069 i) (index0_8_52069 j) / 2
    else 0

/-- Boolean tables are the sign tables of the 256 masks. -/
def bitValue52069 (b : Bool) : ℚ :=
  if b then 1 else -1

def maskBit52069 (m : Fin 256) (i : Fin 8) : Bool :=
  if (m.val / 2 ^ i.val) % 2 = 1 then true else false

def booleanTable52069 (m : Fin 256) : BooleanTable52069 :=
  fun i => bitValue52069 (maskBit52069 m i)

/-- The exact restriction maps for the Boolean-area recursion. -/
def restrict8_52069 (t : BooleanTable52069) (c : Fin 3) (b : Bool) : Table4_52069 :=
  if c = 0 then
    if b then ![t 1, t 3, t 5, t 7] else ![t 0, t 2, t 4, t 6]
  else if c = 1 then
    if b then ![t 2, t 3, t 6, t 7] else ![t 0, t 1, t 4, t 5]
  else
    if b then ![t 4, t 5, t 6, t 7] else ![t 0, t 1, t 2, t 3]

def restrict4_52069 (t : Table4_52069) (c : Fin 2) (b : Bool) : Table2_52069 :=
  if c = 0 then
    if b then ![t 1, t 3] else ![t 0, t 2]
  else
    if b then ![t 2, t 3] else ![t 0, t 1]

def restrict2_52069 (t : Table2_52069) (_c : Fin 1) (b : Bool) : Table1_52069 :=
  if b then ![t 1] else ![t 0]

def variance8_52069 (t : BooleanTable52069) : ℚ :=
  let μ : ℚ := (∑ i : Fin 8, t i) / 8
  (∑ i : Fin 8, (t i - μ) ^ 2) / 8

def variance4_52069 (t : Table4_52069) : ℚ :=
  let μ : ℚ := (∑ i : Fin 4, t i) / 4
  (∑ i : Fin 4, (t i - μ) ^ 2) / 4

def variance2_52069 (t : Table2_52069) : ℚ :=
  let μ : ℚ := (∑ i : Fin 2, t i) / 2
  (∑ i : Fin 2, (t i - μ) ^ 2) / 2

def area1_52069 (_t : Table1_52069) : ℚ := 0

def area2_52069 (t : Table2_52069) : ℚ :=
  variance2_52069 t +
    (area1_52069 (restrict2_52069 t 0 false) +
      area1_52069 (restrict2_52069 t 0 true)) / 2

def area4_52069 (t : Table4_52069) : ℚ :=
  variance4_52069 t +
    min
      ((area2_52069 (restrict4_52069 t 0 false) +
          area2_52069 (restrict4_52069 t 0 true)) / 2)
      ((area2_52069 (restrict4_52069 t 1 false) +
          area2_52069 (restrict4_52069 t 1 true)) / 2)

def area8_52069 (t : BooleanTable52069) : ℚ :=
  variance8_52069 t +
    min
      ((area4_52069 (restrict8_52069 t 0 false) +
          area4_52069 (restrict8_52069 t 0 true)) / 2)
      (min
        ((area4_52069 (restrict8_52069 t 1 false) +
            area4_52069 (restrict8_52069 t 1 true)) / 2)
        ((area4_52069 (restrict8_52069 t 2 false) +
            area4_52069 (restrict8_52069 t 2 true)) / 2))

def bilinear52069 (u v : BooleanTable52069) : ℚ :=
  ∑ i : Fin 8, ∑ j : Fin 8,
    u i * activePolicyMatrix52069 i j * v j

def targetArea52069 : ℚ :=
  bilinear52069 target52069 target52069

def tangentGradient52069 (i : Fin 8) : ℚ :=
  2 * ∑ j : Fin 8, activePolicyMatrix52069 i j * target52069 j

def tangentBeta52069 : ℚ :=
  -targetArea52069 - tangentShift52069

def affineMinorant52069 (t : BooleanTable52069) : ℚ :=
  tangentBeta52069 + ∑ i : Fin 8, tangentGradient52069 i * t i

/-- The tangent slack whose minimum defines the completion cost. -/
def tangentSlack52069 (m : Fin 256) : ℚ :=
  area8_52069 (booleanTable52069 m) -
    affineMinorant52069 (booleanTable52069 m)

/-- The two saturated rows encode a plus bit at row 2 and a minus bit at row 1. -/
def saturatedMismatchPattern52069 (m : Fin 256) : Fin 4 :=
  if booleanTable52069 m 2 = -target52069 2 then
    if booleanTable52069 m 1 = -target52069 1 then 3 else 1
  else if booleanTable52069 m 1 = -target52069 1 then 2 else 0

/-- A value is the exact completion cost for a prescribed pattern when it is
realized through a matching Boolean table and is no larger than every other such
completion. -/
def completionMinimum52069 (pattern : Fin 4) (value : ℚ) : Prop :=
  (∃ m : Fin 256,
    saturatedMismatchPattern52069 m = pattern ∧
      tangentSlack52069 m = value) ∧
    (∀ m : Fin 256,
      saturatedMismatchPattern52069 m = pattern →
        value ≤ tangentSlack52069 m)

def completionCostValue52069 (pattern : Fin 4) : ℚ :=
  ![(0 : ℚ), 17 / 16, 3 / 4, 19 / 8] pattern

/-- The only completions retained through tight-support saturated-row flips. -/
def restrictedCompletionMask52069 (pattern : Fin 4) : Fin 256 :=
  if pattern = 0 then 204 else
  if pattern = 1 then 200 else
  if pattern = 2 then 206 else 202

def restrictedCompletionCost52069 (pattern : Fin 4) : ℚ :=
  tangentSlack52069 (restrictedCompletionMask52069 pattern)

def unrestrictedCover52069 : ℚ :=
  min (completionCostValue52069 1)
    (min (completionCostValue52069 2)
      (completionCostValue52069 3 / 2))

def restrictedCover52069 : ℚ :=
  min (restrictedCompletionCost52069 1)
    (min (restrictedCompletionCost52069 2)
      (restrictedCompletionCost52069 3 / 2))

def changesAt52069 (m m' : Fin 256) (i : Fin 8) : Prop :=
  booleanTable52069 m i ≠ booleanTable52069 m' i

def unsaturatedRow52069 (i : Fin 8) : Prop :=
  i ≠ 1 ∧ i ≠ 2

abbrev AdaptiveCompletionRule52069 := Fin 4 → Fin 256

def suppliedAdaptiveCompletionRule52069 :
    Option AdaptiveCompletionRule52069 := none

def noAdaptiveCompletionRuleSupplied52069 : Prop :=
  suppliedAdaptiveCompletionRule52069 = none

/-- Claim 52069: the exact witness compares minimization over all Boolean
completions with the support-generated restriction, and records the absence
of a supplied adaptive completion selector. -/
def intermediateThresholdCompletionObstruction_claim52069 : Prop :=
  activePolicyIndex52069 = 3 ∧
    tangentShift52069 = 15 / 512 ∧
    tightMask52069 = 204 ∧
    saturatedRows52069 = {1, 2} ∧
    targetArea52069 = 529 / 512 ∧
    tangentBeta52069 = -17 / 16 ∧
    (∀ m : Fin 256, 0 ≤ tangentSlack52069 m) ∧
    (∀ m : Fin 256,
      tangentSlack52069 m = 0 ↔ m = tightMask52069) ∧
    completionMinimum52069 0 (completionCostValue52069 0) ∧
    completionMinimum52069 1 (completionCostValue52069 1) ∧
    completionMinimum52069 2 (completionCostValue52069 2) ∧
    completionMinimum52069 3 (completionCostValue52069 3) ∧
    restrictedCompletionMask52069 1 = 200 ∧
    restrictedCompletionMask52069 2 = 206 ∧
    restrictedCompletionMask52069 3 = 202 ∧
    restrictedCompletionCost52069 1 = 49 / 32 ∧
    restrictedCompletionCost52069 2 = 7 / 4 ∧
    restrictedCompletionCost52069 3 = 101 / 32 ∧
    unrestrictedCover52069 = 3 / 4 ∧
    restrictedCover52069 = 49 / 32 ∧
    restrictedCover52069 / unrestrictedCover52069 = 49 / 24 ∧
    saturatedMismatchPattern52069 239 = 2 ∧
    tangentSlack52069 239 = 3 / 4 ∧
    (∀ i : Fin 8,
      changesAt52069 239 tightMask52069 i ↔
        (i = 0 ∨ i = 1 ∨ i = 5)) ∧
    unsaturatedRow52069 0 ∧
    unsaturatedRow52069 5 ∧
    noAdaptiveCompletionRuleSupplied52069

end

end MathlibPlus.Open.ResearchFormalization.R4034
