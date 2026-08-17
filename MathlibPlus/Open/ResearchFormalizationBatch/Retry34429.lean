import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch.Retry34429

noncomputable section

private abbrev Point := ℝ × ℝ

private def zeroPoint : Point := (0, 0)
private def pointNorm (p : Point) : ℝ := Real.sqrt (p.1 ^ 2 + p.2 ^ 2)
private def dotProduct (p q : Point) : ℝ := p.1 * q.1 + p.2 * q.2
private def determinant (p q : Point) : ℝ := p.1 * q.2 - p.2 * q.1
private def projectiveAngle (p q : Point) : ℝ :=
  Real.arccos (|dotProduct p q| / (pointNorm p * pointNorm q))
private def pointScale (r : ℝ) (p : Point) : Point := (r * p.1, r * p.2)

private def constructionU : Point := (1, 0)
private def constructionW : Point :=
  (Real.cos (Real.pi / 10), -Real.sin (Real.pi / 10))
private def constructionV : Point :=
  (Real.cos (2 * Real.pi / 5), Real.sin (2 * Real.pi / 5))
private def constructionB : Point := (0, 1)

private def constructionUAt (i : Fin 3) : Point :=
  if i = 0 then zeroPoint
  else if i = 1 then constructionU else constructionU + constructionW
private def constructionVAt (j : Fin 3) : Point :=
  if j = 0 then zeroPoint
  else if j = 1 then constructionV else constructionV + constructionB
private def constructionGridPoint (i j : Fin 3) : Point :=
  constructionUAt i + constructionVAt j

private def constructionHorizontalDirection (i : Fin 2) : Point :=
  if i = 0 then constructionU else constructionW
private def constructionVerticalDirection (j : Fin 2) : Point :=
  if j = 0 then constructionV else constructionB

private def embeddedUnitRhombus (u v : Point) : Prop :=
  pointNorm u = 1 ∧ pointNorm v = 1 ∧ determinant u v ≠ 0

private def constructionCells : Prop :=
  ∀ i j : Fin 2,
    embeddedUnitRhombus
      (constructionHorizontalDirection i)
      (constructionVerticalDirection j)

private def constructionGridInjective : Prop :=
  ∀ i j k l : Fin 3,
    constructionGridPoint i j = constructionGridPoint k l →
      i = k ∧ j = l

private def constructionAdjacent (a b : Fin 3) : Prop :=
  a.val + 1 = b.val ∨ b.val + 1 = a.val

private def constructionGridNeighbor (i j k l : Fin 3) : Prop :=
  (i = k ∧ constructionAdjacent j l) ∨
    (j = l ∧ constructionAdjacent i k)

private def constructionUnitEdge
    (a b : Fin 3 × Fin 3) : Prop :=
  pointNorm
    (constructionGridPoint a.1 a.2 - constructionGridPoint b.1 b.2) = 1

private def constructionLexLess
    (a b : Fin 3 × Fin 3) : Prop :=
  a.1.val < b.1.val ∨ (a.1 = b.1 ∧ a.2.val < b.2.val)

private def constructionGridEdgeCount : ℕ :=
  Nat.card {e : ((Fin 3 × Fin 3) × (Fin 3 × Fin 3)) //
    constructionLexLess e.1 e.2 ∧ constructionUnitEdge e.1 e.2}

private def constructionUnitGraphExact : Prop :=
  ∀ i j k l : Fin 3,
    (i, j) ≠ (k, l) →
      (constructionUnitEdge (i, j) (k, l) ↔
        constructionGridNeighbor i j k l)

private def constructionGridTriangleFree : Prop :=
  ∀ a b c : Fin 3 × Fin 3,
    a ≠ b → a ≠ c → b ≠ c →
    ¬(constructionUnitEdge a b ∧
      constructionUnitEdge b c ∧ constructionUnitEdge c a)

private def constructionDirection (i : Fin 4) : Point :=
  if i = 0 then constructionU
  else if i = 1 then constructionV
  else if i = 2 then constructionW else constructionB

private def constructionDirectionCrossing?
    (i j : Fin 4) (h k : Fin 2) : Prop :=
  (constructionDirection i = constructionHorizontalDirection h ∧
      constructionDirection j = constructionVerticalDirection k) ∨
    (constructionDirection j = constructionHorizontalDirection h ∧
      constructionDirection i = constructionVerticalDirection k)

private def constructionDirectionCrossing (i j : Fin 4) : Prop :=
  ∃ h k : Fin 2, constructionDirectionCrossing? i j h k

private def constructionFourCycleEdge (i j : Fin 4) : Prop :=
  (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
  (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
  (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
  (i = 3 ∧ j = 0) ∨ (i = 0 ∧ j = 3)

private def constructionDirectionClassesDistinct : Prop :=
  ∀ i j : Fin 4, i ≠ j →
    ¬(constructionDirection i = constructionDirection j ∨
      constructionDirection i = -constructionDirection j)

private def constructionUpath (s : ℝ) : Point :=
  if s ≤ 1 then pointScale s constructionU
  else constructionU + pointScale (s - 1) constructionW
private def constructionVpath (t : ℝ) : Point :=
  if t ≤ 1 then pointScale t constructionV
  else constructionV + pointScale (t - 1) constructionB
private def constructionSeparableMap (s t : ℝ) : Point :=
  constructionUpath s + constructionVpath t

private def constructionMapInjectiveOnCells : Prop :=
  ∀ s t s' t' : ℝ,
    0 ≤ s → s ≤ 2 → 0 ≤ t → t ≤ 2 →
    0 ≤ s' → s' ≤ 2 → 0 ≤ t' → t' ≤ 2 →
    constructionSeparableMap s t = constructionSeparableMap s' t' →
    s = s' ∧ t = t'

private def constructionAllDeterminantsPositive : Prop :=
  0 < determinant constructionU constructionV ∧
  0 < determinant constructionU constructionB ∧
  0 < determinant constructionW constructionV ∧
  0 < determinant constructionW constructionB

private def constructionTrackLength : ℝ :=
  2 * Real.cos (Real.pi / 20)
private def constructionCosineBound : ℝ :=
  Real.cos (2 * Real.pi / 5)

private def constructionUDisplacement (a : Point) : Prop :=
  ∃ i j : Fin 3, i ≠ j ∧ a = constructionUAt i - constructionUAt j
private def constructionVDisplacement (b : Point) : Prop :=
  ∃ i j : Fin 3, i ≠ j ∧ b = constructionVAt i - constructionVAt j

private def constructionMixedDisplacementBounds : Prop :=
  ∀ a b : Point,
    constructionUDisplacement a →
    constructionVDisplacement b →
    1 ≤ pointNorm a ∧ pointNorm a ≤ constructionTrackLength ∧
    1 ≤ pointNorm b ∧ pointNorm b ≤ constructionTrackLength ∧
    |dotProduct a b / (pointNorm a * pointNorm b)| ≤
      constructionCosineBound ∧
    pointNorm (a + b) ^ 2 ≥ 2 - 2 * constructionCosineBound

def claim34429 : Prop :=
  projectiveAngle constructionU constructionV = 2 * Real.pi / 5 ∧
  projectiveAngle constructionU constructionB = Real.pi / 2 ∧
  projectiveAngle constructionW constructionV = Real.pi / 2 ∧
  projectiveAngle constructionW constructionB = 2 * Real.pi / 5 ∧
  constructionCells ∧
  constructionGridInjective ∧
  constructionGridEdgeCount = 12 ∧
  constructionUnitGraphExact ∧
  constructionGridTriangleFree ∧
  constructionDirectionClassesDistinct ∧
  (∀ i j : Fin 4,
    constructionDirectionCrossing i j ↔ constructionFourCycleEdge i j) ∧
  constructionAllDeterminantsPositive ∧
  constructionMapInjectiveOnCells ∧
  pointNorm (constructionU + constructionW) = constructionTrackLength ∧
  pointNorm (constructionV + constructionB) = constructionTrackLength ∧
  1 < constructionTrackLength ∧ constructionTrackLength < 2 ∧
  constructionCosineBound < 1 / 2 ∧
  2 - 2 * constructionCosineBound = (5 - Real.sqrt 5) / 2 ∧
  1 < (5 - Real.sqrt 5) / 2 ∧
  constructionMixedDisplacementBounds

end
end MathlibPlus.Open.ResearchFormalizationBatch.Retry34429
