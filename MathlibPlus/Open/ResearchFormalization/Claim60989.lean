import Mathlib

noncomputable section
open Classical
open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization

/-! Exact finite probability surface for the two supplied depth-two trees. -/

abbrev Claim60989SignInput := Fin 4 → Bool

abbrev Claim60989Transcript := Fin 4 → Option Bool

def claim60989A : Fin 4 := 0

def claim60989R : Fin 4 := 1

def claim60989B : Fin 4 := 2

def claim60989C : Fin 4 := 3

def claim60989SignValue (b : Bool) : ℝ := if b then 1 else -1

def claim60989Compatible (h : Claim60989Transcript) (x : Claim60989SignInput) : Prop :=
  ∀ i b, h i = some b → x i = b

def claim60989Update (h : Claim60989Transcript) (i : Fin 4) (b : Bool) : Claim60989Transcript :=
  Function.update h i (some b)

def claim60989Root : Claim60989Transcript := fun _ => none

def claim60989CompletionCount (h : Claim60989Transcript) : ℕ :=
  (Finset.univ.filter (claim60989Compatible h)).card

def claim60989UniformAverage (h : Claim60989Transcript)
    (f : Claim60989SignInput → ℝ) : ℝ :=
  (Finset.sum (Finset.univ.filter (claim60989Compatible h)) f) /
    (claim60989CompletionCount h : ℝ)

def claim60989ConditionalMean (f : Claim60989SignInput → ℝ)
    (h : Claim60989Transcript) : ℝ :=
  claim60989UniformAverage h f

def claim60989ConditionalVariance (f : Claim60989SignInput → ℝ)
    (h : Claim60989Transcript) : ℝ :=
  claim60989UniformAverage h
    (fun x => (f x - claim60989ConditionalMean f h) ^ 2)

def claim60989T1 (x : Claim60989SignInput) : ℝ :=
  if claim60989SignValue (x claim60989R) = -1 then
    claim60989SignValue (x claim60989C)
  else
    -claim60989SignValue (x claim60989B)

def claim60989T2 (x : Claim60989SignInput) : ℝ :=
  if claim60989SignValue (x claim60989A) = -1 then
    -claim60989SignValue (x claim60989B)
  else
    claim60989SignValue (x claim60989C)

def claim60989P : ℝ := 9 / 16

def claim60989Q : ℝ := 7 / 16

def claim60989Mu (x : Claim60989SignInput) : ℝ :=
  claim60989P * claim60989T1 x + claim60989Q * claim60989T2 x

def claim60989ResidualQueries1 (h : Claim60989Transcript)
    (x : Claim60989SignInput) : ℝ :=
  (if h claim60989R = none then 1 else 0) +
    (if claim60989SignValue (x claim60989R) = -1 then
      if h claim60989C = none then 1 else 0
     else
      if h claim60989B = none then 1 else 0)

def claim60989ResidualQueries2 (h : Claim60989Transcript)
    (x : Claim60989SignInput) : ℝ :=
  (if h claim60989A = none then 1 else 0) +
    (if claim60989SignValue (x claim60989A) = -1 then
      if h claim60989B = none then 1 else 0
     else
      if h claim60989C = none then 1 else 0)

def claim60989D1 (h : Claim60989Transcript) : ℝ :=
  claim60989UniformAverage h (fun x => claim60989ResidualQueries1 h x)

def claim60989D2 (h : Claim60989Transcript) : ℝ :=
  claim60989UniformAverage h (fun x => claim60989ResidualQueries2 h x)

def claim60989Potential (h : Claim60989Transcript) : ℝ :=
  claim60989P * claim60989D1 h * claim60989ConditionalVariance claim60989T1 h +
    claim60989Q * claim60989D2 h * claim60989ConditionalVariance claim60989T2 h

def claim60989Drop (h : Claim60989Transcript) (i : Fin 4) : ℝ :=
  claim60989Potential h -
    (claim60989Potential (claim60989Update h i false) +
      claim60989Potential (claim60989Update h i true)) / 2

def claim60989AfterR (x : Claim60989SignInput) : Claim60989Transcript :=
  claim60989Update claim60989Root claim60989R (x claim60989R)

def claim60989SecondCoordinate (x : Claim60989SignInput) : Fin 4 :=
  if claim60989SignValue (x claim60989R) = -1 then claim60989C else claim60989B

def claim60989AfterSecond (x : Claim60989SignInput) : Claim60989Transcript :=
  claim60989Update (claim60989AfterR x) (claim60989SecondCoordinate x)
    (x (claim60989SecondCoordinate x))

def claim60989AfterA (x : Claim60989SignInput) : Claim60989Transcript :=
  claim60989Update (claim60989AfterSecond x) claim60989A (x claim60989A)

def claim60989NeedsFourth (x : Claim60989SignInput) : Prop :=
  (claim60989SignValue (x claim60989R) = -1 ∧
      claim60989SignValue (x claim60989A) = -1) ∨
    (claim60989SignValue (x claim60989R) = 1 ∧
      claim60989SignValue (x claim60989A) = 1)

def claim60989AfterFourth (x : Claim60989SignInput) : Claim60989Transcript :=
  if claim60989SignValue (x claim60989R) = -1 ∧
      claim60989SignValue (x claim60989A) = -1 then
    claim60989Update (claim60989AfterA x) claim60989B (x claim60989B)
  else if claim60989SignValue (x claim60989R) = 1 ∧
      claim60989SignValue (x claim60989A) = 1 then
    claim60989Update (claim60989AfterA x) claim60989C (x claim60989C)
  else
    claim60989AfterA x

def claim60989PolicyQueryList (x : Claim60989SignInput) : List (Fin 4) :=
  [claim60989R, claim60989SecondCoordinate x, claim60989A] ++
    (if claim60989NeedsFourth x then
      if claim60989SignValue (x claim60989R) = -1 then [claim60989B] else [claim60989C]
     else [])

def claim60989PolicyIsLegal : Prop :=
  ∀ x, (claim60989PolicyQueryList x).Nodup

def claim60989PolicyDetermines : Prop :=
  ∀ x y, claim60989Compatible (claim60989AfterFourth x) y →
    claim60989Mu y = claim60989Mu x

def claim60989PathArea (x : Claim60989SignInput) : ℝ :=
  claim60989ConditionalVariance claim60989Mu claim60989Root +
    claim60989ConditionalVariance claim60989Mu (claim60989AfterR x) +
    claim60989ConditionalVariance claim60989Mu (claim60989AfterSecond x) +
    claim60989ConditionalVariance claim60989Mu (claim60989AfterA x) +
    (if claim60989NeedsFourth x then
      claim60989ConditionalVariance claim60989Mu (claim60989AfterFourth x)
     else 0)

def claim60989PolicyArea : ℝ :=
  claim60989UniformAverage claim60989Root claim60989PathArea

def claim60989 : Prop :=
  claim60989ConditionalVariance claim60989Mu claim60989Root = 193 / 256 ∧
    claim60989Potential claim60989Root = 2 ∧
    claim60989Drop claim60989Root claim60989A = 7 / 16 ∧
    claim60989Drop claim60989Root claim60989R = 9 / 16 ∧
    claim60989Drop claim60989Root claim60989B = 1 / 2 ∧
    claim60989Drop claim60989Root claim60989C = 1 / 2 ∧
    claim60989ConditionalVariance claim60989Mu claim60989Root -
        max (claim60989Drop claim60989Root claim60989A)
          (max (claim60989Drop claim60989Root claim60989R)
            (max (claim60989Drop claim60989Root claim60989B)
              (claim60989Drop claim60989Root claim60989C))) = 49 / 256 ∧
    0 < (49 / 256 : ℝ) ∧
    claim60989PolicyIsLegal ∧
    claim60989PolicyDetermines ∧
    claim60989PolicyArea = 1789 / 1024 ∧
    claim60989PolicyArea < 2

end MathlibPlus.Open.ResearchFormalization
