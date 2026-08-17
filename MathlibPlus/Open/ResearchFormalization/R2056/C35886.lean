import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R2056C35886

noncomputable section

open scoped BigOperators

abbrev Point := ℝ × ℝ

 def dot (p q : Point) : ℝ := p.1 * q.1 + p.2 * q.2

def euclidSq (p : Point) : ℝ := dot p p

def euclidLength (p : Point) : ℝ := Real.sqrt (euclidSq p)

def absCosine (p q : Point) : ℝ :=
  |dot p q| / (euclidLength p * euclidLength q)

def determinant (p q : Point) : ℝ := p.1 * q.2 - p.2 * q.1

def direction (θ : ℝ) : Point := (Real.cos θ, Real.sin θ)

def u : Point := (1, 0)
def w : Point := (Real.cos (Real.pi / 10), -Real.sin (Real.pi / 10))
def v : Point := (Real.cos (2 * Real.pi / 5), Real.sin (2 * Real.pi / 5))
def b : Point := (0, 1)

def U (i : Fin 3) : Point :=
  if i = 0 then (0, 0) else if i = 1 then u else u + w

def V (i : Fin 3) : Point :=
  if i = 0 then (0, 0) else if i = 1 then v else v + b

def gridPoint (s t : Fin 3) : Point := U s + V t

def gridAdjacent (s t s' t' : Fin 3) : Prop :=
  ((s.val + 1 = s'.val ∨ s'.val + 1 = s.val) ∧ t = t') ∨
    ((t.val + 1 = t'.val ∨ t'.val + 1 = t.val) ∧ s = s')

def cellVertices (i j : Fin 2) : Finset Point :=
  {gridPoint (Fin.castSucc i) (Fin.castSucc j),
   gridPoint (Fin.succ i) (Fin.castSucc j),
   gridPoint (Fin.castSucc i) (Fin.succ j),
   gridPoint (Fin.succ i) (Fin.succ j)}

def cellSet (i j : Fin 2) : Set Point :=
  convexHull ℝ (cellVertices i j : Set Point)

def cellNeighbor (i j i' j' : Fin 2) : Prop :=
  ((i.val + 1 = i'.val ∨ i'.val + 1 = i.val) ∧ j = j') ∨
    ((j.val + 1 = j'.val ∨ j'.val + 1 = j.val) ∧ i = i')

def cellIsRhombus (i j : Fin 2) : Prop :=
  let p00 := gridPoint (Fin.castSucc i) (Fin.castSucc j)
  let p10 := gridPoint (Fin.succ i) (Fin.castSucc j)
  let p01 := gridPoint (Fin.castSucc i) (Fin.succ j)
  let p11 := gridPoint (Fin.succ i) (Fin.succ j)
  p11 = p10 + p01 - p00 ∧
    0 < determinant (p10 - p00) (p01 - p00) ∧
    euclidSq (p10 - p00) = 1 ∧
    euclidSq (p01 - p00) = 1 ∧
    euclidSq (p11 - p10) = 1 ∧
    euclidSq (p11 - p01) = 1

def faceToFace : Prop :=
  ∀ i j i' j' : Fin 2, (i, j) ≠ (i', j') →
    cellSet i j ∩ cellSet i' j' =
      convexHull ℝ ((cellVertices i j ∩ cellVertices i' j') : Set Point)

def cellIntersectionNonempty (i j i' j' : Fin 2) : Prop :=
  (cellSet i j ∩ cellSet i' j').Nonempty

def embeddedFaceToFaceDisk : Prop :=
  Function.Injective (fun st : Fin 3 × Fin 3 => gridPoint st.1 st.2) ∧
    (∀ i j : Fin 2, cellIsRhombus i j) ∧
    faceToFace ∧
    (∀ i j i' j' : Fin 2, cellNeighbor i j i' j' →
      cellIntersectionNonempty i j i' j') ∧
    (∀ i j i' j' : Fin 2, Relation.ReflTransGen
      (fun x y : Fin 2 × Fin 2 => cellNeighbor x.1 x.2 y.1 y.2)
      (i, j) (i', j'))

def unitPair (s t s' t' : Fin 3) : Prop :=
  euclidSq (gridPoint s t - gridPoint s' t') = 1

def unitGraphTriangleFree : Prop :=
  ∀ a c d : Fin 3 × Fin 3,
    a ≠ c → a ≠ d → c ≠ d →
    ¬ (unitPair a.1 a.2 c.1 c.2 ∧
      unitPair a.1 a.2 d.1 d.2 ∧
      unitPair c.1 c.2 d.1 d.2)

def connectedGrid : Prop :=
  ∀ a c : Fin 3 × Fin 3,
    Relation.ReflTransGen
      (fun x y : Fin 3 × Fin 3 => gridAdjacent x.1 x.2 y.1 y.2) a c

def unionOfCells : Set Point :=
  ⋃ i : Fin 2, ⋃ j : Fin 2, cellSet i j

def nonconvexDisk : Prop := ¬ Convex ℝ unionOfCells

def directionVector : Fin 4 → Point := ![u, v, w, b]

def cellDirections (i j : Fin 2) : Finset (Fin 4) :=
  if i = 0 then
    if j = 0 then {0, 1} else {0, 3}
  else if j = 0 then {2, 1} else {2, 3}

def rhombusDirectionMeeting (i j : Fin 4) : Prop :=
  ∃ r s : Fin 2,
    cellDirections r s = {i, j} ∧ cellIsRhombus r s ∧
      (cellSet r s).Nonempty

def directionCrossing (i j : Fin 4) : Prop :=
  rhombusDirectionMeeting i j

def projectiveDistance (p q : Point) : ℝ :=
  Real.arccos (absCosine p q)

def directionK22 : Prop :=
  ∀ i j : Fin 4, directionCrossing i j ↔
    ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
      (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
      (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
      (i = 3 ∧ j = 0) ∨ (i = 0 ∧ j = 3))

def notClique : Prop :=
  ¬ (∀ i j : Fin 4, i ≠ j → directionCrossing i j)

def twoDirectionRepresentative (h : Fin 4 → Fin 2) : Prop :=
  let representative : Fin 2 → Fin 4 := fun i => ⟨i.val, by omega⟩
  ∀ i : Fin 4, directionVector i = directionVector (representative (h i))

def notTwoDirectionReduction : Prop :=
  ¬ ∃ h : Fin 4 → Fin 2, twoDirectionRepresentative h

/-- Claim 35886: the actual direction vectors have the six projective
separations and the actual cell-direction meeting graph is K₂,₂. -/
def claim35886_directionCrossingK22 : Prop :=
  projectiveDistance (directionVector 0) (directionVector 1) =
      2 * Real.pi / 5 ∧
    projectiveDistance (directionVector 2) (directionVector 3) =
      2 * Real.pi / 5 ∧
    projectiveDistance (directionVector 0) (directionVector 3) =
      Real.pi / 2 ∧
    projectiveDistance (directionVector 2) (directionVector 1) =
      Real.pi / 2 ∧
    projectiveDistance (directionVector 0) (directionVector 2) =
      Real.pi / 10 ∧
    projectiveDistance (directionVector 1) (directionVector 3) =
      Real.pi / 10 ∧
    directionK22


end

end MathlibPlus.Open.ResearchFormalization.R2056C35886
