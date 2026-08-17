import Mathlib
import MathlibPlus.Open.ResearchFormalization.Claim1159

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.C0079Claim1192

open MathlibPlus.Open.ResearchFormalization.Claim1159

noncomputable section

/-- The seven partitions in the complete area-at-most-three sector, in the
order of the inverse cup block. -/
abbrev AreaThreeShape1192 := Fin 7

def minimumDimension1192 (shape : AreaThreeShape1192) : ℕ :=
  match shape.1 with
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 3
  | 5 => 2
  | _ => 3

def available1192 (shape : AreaThreeShape1192) (d : ℕ) : Prop :=
  minimumDimension1192 shape ≤ d

/-- The remaining padded-partition row sets, written in the same natural-row
carrier as the admitted flagged minors. -/
def threeRows1192 (d : ℕ) (i : Fin d) : ℕ :=
  if i.1 = d - 1 then d + 2 else i.1

def twoOneRows1192 (d : ℕ) (i : Fin d) : ℕ :=
  if i.1 = d - 2 then i.1 + 1
  else if i.1 = d - 1 then i.1 + 2
  else i.1

def oneOneOneRows1192 (d : ℕ) (i : Fin d) : ℕ :=
  if d - 3 ≤ i.1 then i.1 + 1 else i.1

def hEmpty1192 (d : ℕ) (a : ℝ) : ℝ :=
  principalFlaggedMinor a d

def hOne1192 (d : ℕ) (a : ℝ) : ℝ :=
  oneFlaggedMinor a d

def hTwo1192 (d : ℕ) (a : ℝ) : ℝ :=
  twoFlaggedMinor a d

def hOneOne1192 (d : ℕ) (a : ℝ) : ℝ :=
  oneOneFlaggedMinor a d

def hThree1192 (d : ℕ) (a : ℝ) : ℝ :=
  flaggedMinorFromRows a (threeRows1192 d)

def hTwoOne1192 (d : ℕ) (a : ℝ) : ℝ :=
  flaggedMinorFromRows a (twoOneRows1192 d)

def hOneOneOne1192 (d : ℕ) (a : ℝ) : ℝ :=
  flaggedMinorFromRows a (oneOneOneRows1192 d)

/-- The gauged inverse-cup coordinates are the exact signed flagged-minor
combinations from the area-at-most-three incidence block. -/
def alphaEmpty1192 (d : ℕ) (a : ℝ) : ℝ :=
  hEmpty1192 d a

def alphaOne1192 (d : ℕ) (a : ℝ) : ℝ :=
  hEmpty1192 d a - hOne1192 d a

def alphaTwo1192 (d : ℕ) (a : ℝ) : ℝ :=
  hEmpty1192 d a - hOne1192 d a + hTwo1192 d a

def alphaOneOne1192 (d : ℕ) (a : ℝ) : ℝ :=
  hEmpty1192 d a - hOne1192 d a + hOneOne1192 d a

def alphaThree1192 (d : ℕ) (a : ℝ) : ℝ :=
  hEmpty1192 d a - hOne1192 d a + hTwo1192 d a - hThree1192 d a

def alphaTwoOne1192 (d : ℕ) (a : ℝ) : ℝ :=
  2 * hEmpty1192 d a - hOne1192 d a + hTwo1192 d a +
    hOneOne1192 d a - hTwoOne1192 d a

def alphaOneOneOne1192 (d : ℕ) (a : ℝ) : ℝ :=
  hEmpty1192 d a - hOne1192 d a + hOneOne1192 d a - hOneOneOne1192 d a

def alpha1192 (shape : AreaThreeShape1192) (d : ℕ) (a : ℝ) : ℝ :=
  match shape.1 with
  | 0 => alphaEmpty1192 d a
  | 1 => alphaOne1192 d a
  | 2 => alphaTwo1192 d a
  | 3 => alphaOneOne1192 d a
  | 4 => alphaThree1192 d a
  | 5 => alphaTwoOne1192 d a
  | _ => alphaOneOneOne1192 d a

/-- The explicit numerator whose constant coefficient controls the additional
boundary zero. -/
def numeratorOneOneOne1192 (d : ℕ) (b : ℝ) : ℝ :=
  24 * b ^ 3 + 12 * (2 * (d : ℝ) - 1) * b ^ 2 +
    3 * (3 * (d : ℝ) ^ 2 + (d : ℝ) + 2) * b +
    ((d : ℝ) - 3) * ((d : ℝ) + 1) * ((d : ℝ) + 2)

def principalProduct1192 (d : ℕ) (b : ℝ) : ℝ :=
  (Nat.factorial d : ℝ) *
    ∏ p ∈ Finset.range (d + 1),
      ∏ q ∈ Finset.range (d + 1),
        if p < q then 2 * b + (p : ℝ) + (q : ℝ) + 1 else 1

/-- Exact pointwise positivity and the complete boundary-zero classification
for every available coordinate in the area-at-most-three sector. -/
def claim1192 : Prop :=
  ∀ (r : ℕ), 2 ≤ r →
    let d : ℕ := r - 1
    (∀ (shape : AreaThreeShape1192),
      available1192 shape d →
        ∀ a : ℝ, (1 / 2 : ℝ) < a → 0 < alpha1192 shape d a) ∧
    (∀ (shape : AreaThreeShape1192),
      available1192 shape d →
        (alpha1192 shape d (1 / 2 : ℝ) = 0 ↔
          shape.1 = 1 ∨ (d = 3 ∧ shape.1 = 6))) ∧
    (3 ≤ d →
      (∀ a : ℝ,
        let b : ℝ := a - 1 / 2
        let x : ℝ := 2 * b + (d : ℝ) + 1
        alphaOneOneOne1192 d a =
          numeratorOneOneOne1192 d b * principalProduct1192 d b /
            (3 * (x - 2) * (x - 1) * x)) ∧
      numeratorOneOneOne1192 d 0 =
        ((d : ℝ) - 3) * ((d : ℝ) + 1) * ((d : ℝ) + 2))

end

end MathlibPlus.Open.ResearchFormalization.C0079Claim1192
