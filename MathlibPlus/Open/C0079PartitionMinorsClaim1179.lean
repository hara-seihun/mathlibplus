import MathlibPlus.Open.C0079NeighboringMinor

namespace MathlibPlus.Open.C0079

open scoped BigOperators

noncomputable section

/-- The reverse-padded row index `i + lambda_(d+1-i)`. -/
def partitionRowValue1179 (d : ℕ) (lambda : Fin d → ℕ) (i : Fin d) : ℕ :=
  i.1 + lambda (Fin.rev i)

/-- The finite row carrier for a padded partition whose selected rows are in
`0,...,2d-1`. -/
def partitionRows1179 (d : ℕ) (lambda : Fin d → ℕ)
    (hrows : ∀ i : Fin d, partitionRowValue1179 d lambda i < 2 * d) :
    Fin d → Fin (2 * d) :=
  fun i => ⟨partitionRowValue1179 d lambda i, hrows i⟩

/-- The flagged maximal minor selected by a padded partition. -/
def partitionMinor1179 (d : ℕ) (a : ℝ) (lambda : Fin d → ℕ)
    (hrows : ∀ i : Fin d, partitionRowValue1179 d lambda i < 2 * d) : ℝ :=
  Matrix.det ((flaggedArray d a).submatrix (partitionRows1179 d lambda hrows)
    (fun j => j))

/-- The padded partition vectors for the three area-three shapes. -/
def areaThreeShapeThree1179 (d : ℕ) : Fin d → ℕ :=
  fun i => if i.1 = 0 then 3 else 0

def areaThreeShapeTwoOne1179 (d : ℕ) : Fin d → ℕ :=
  fun i => if i.1 = 0 then 2 else if i.1 = 1 then 1 else 0

def areaThreeShapeOneOneOne1179 (d : ℕ) : Fin d → ℕ :=
  fun i => if i.1 < 3 then 1 else 0

/-- Ordered row-value maps corresponding to the displayed tuples. -/
def displayedThreeRows1179 (d : ℕ) : Fin d → ℕ :=
  fun i => if i.1 < d - 1 then i.1 else d + 2

def displayedTwoOneRows1179 (d : ℕ) : Fin d → ℕ :=
  fun i =>
    if i.1 < d - 2 then i.1
    else if i.1 = d - 2 then d - 1
    else d + 1

def displayedOneOneOneRows1179 (d : ℕ) : Fin d → ℕ :=
  fun i =>
    if i.1 < d - 3 then i.1
    else if i.1 = d - 3 then d - 2
    else if i.1 = d - 2 then d - 1
    else d

/-- Claim 1179: padded partition row maps and their flagged minors, including
all three exact availability ranges. -/
def claim1179 : Prop :=
  (∀ (d : ℕ) (a : ℝ) (lambda : Fin d → ℕ)
      (_hlambda : Antitone lambda)
      (hrows : ∀ i : Fin d, partitionRowValue1179 d lambda i < 2 * d),
      partitionMinor1179 d a lambda hrows =
        Matrix.det ((flaggedArray d a).submatrix
          (partitionRows1179 d lambda hrows) (fun j => j))) ∧
  (∀ (d : ℕ), 3 ≤ d →
    ∀ i : Fin d,
      partitionRowValue1179 d (areaThreeShapeThree1179 d) i =
        displayedThreeRows1179 d i) ∧
  (∀ (d : ℕ), 2 ≤ d →
    ∀ i : Fin d,
      partitionRowValue1179 d (areaThreeShapeTwoOne1179 d) i =
        displayedTwoOneRows1179 d i) ∧
  (∀ (d : ℕ), 3 ≤ d →
    ∀ i : Fin d,
      partitionRowValue1179 d (areaThreeShapeOneOneOne1179 d) i =
        displayedOneOneOneRows1179 d i)

end

end MathlibPlus.Open.C0079
