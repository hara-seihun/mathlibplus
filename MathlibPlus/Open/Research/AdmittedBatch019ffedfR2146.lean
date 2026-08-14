import Mathlib

namespace MathlibPlus.Open.Research.R2146

noncomputable section

abbrev Point := ℤ × ℤ

def shearedRho (r : ℕ) : ℚ :=
  (1 : ℚ) / 2 - 1 / (16 * (r : ℚ))

def shearedQ (r : ℕ) (p : Point) : ℚ :=
  (p.1 : ℚ) ^ 2 + (p.2 : ℚ) ^ 2 +
    2 * shearedRho r * (p.1 : ℚ) * (p.2 : ℚ)

def triQ (p : Point) : ℚ :=
  (p.1 : ℚ) ^ 2 + (p.2 : ℚ) ^ 2 +
    (p.1 : ℚ) * (p.2 : ℚ)

def distanceSq (q : Point → ℚ) (p p' : Point) : ℚ := q (p - p')

def hexCore (r : ℕ) : Finset Point :=
  (Finset.Icc (-(r : ℤ)) (r : ℤ)).product
      (Finset.Icc (-(r : ℤ)) (r : ℤ)) |>.filter
    (fun p => max (max |p.1| |p.2|) |p.1 + p.2| ≤ (r : ℤ))

def rightTail (r a : ℕ) : Finset Point :=
  (Finset.Icc 1 a).image (fun t : ℕ =>
    (((r + t : ℕ) : ℤ), (0 : ℤ)))

def upTail (r b : ℕ) : Finset Point :=
  (Finset.Icc 1 b).image (fun t : ℕ =>
    (((0 : ℤ)), ((r + t : ℕ) : ℤ)))

def leftTail (r c : ℕ) : Finset Point :=
  (Finset.Icc 1 c).image (fun t : ℕ =>
    (-((r + t : ℕ) : ℤ), (0 : ℤ)))

def downTail (r d : ℕ) : Finset Point :=
  (Finset.Icc 1 d).image (fun t : ℕ =>
    ((0 : ℤ), -((r + t : ℕ) : ℤ)))

def source (r a b c d : ℕ) : Finset Point :=
  hexCore r ∪ rightTail r a ∪ upTail r b ∪ leftTail r c ∪ downTail r d

def rightTurnedTail (r a : ℕ) : Finset Point :=
  (Finset.Icc 1 a).image (fun t : ℕ =>
    (((r + t : ℕ) : ℤ), -((t : ℕ) : ℤ)))

def upTurnedTail (r b : ℕ) : Finset Point :=
  (Finset.Icc 1 b).image (fun t : ℕ =>
    (((t : ℕ) : ℤ), ((r : ℕ) : ℤ)))

def leftTurnedTail (r c : ℕ) : Finset Point :=
  (Finset.Icc 1 c).image (fun t : ℕ =>
    (-((r + t : ℕ) : ℤ), ((t : ℕ) : ℤ)))

def downTurnedTail (r d : ℕ) : Finset Point :=
  (Finset.Icc 1 d).image (fun t : ℕ =>
    (-((t : ℕ) : ℤ), -((r : ℕ) : ℤ)))

def target (r a b c d : ℕ) : Finset Point :=
  hexCore r ∪ rightTurnedTail r a ∪ upTurnedTail r b ∪
    leftTurnedTail r c ∪ downTurnedTail r d

def pairwiseUnitSeparated (q : Point → ℚ) (S : Finset Point) : Prop :=
  ∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → 1 ≤ distanceSq q p p'

def unitEdge (q : Point → ℚ) (p p' : Point) : Prop :=
  p ≠ p' ∧ distanceSq q p p' = 1

def unitConnected (q : Point → ℚ) (S : Finset Point) : Prop :=
  ∀ p ∈ S, ∀ p' ∈ S,
    Relation.ReflTransGen
      (fun x y => x ∈ S ∧ y ∈ S ∧ unitEdge q x y) p p'

def triangleFree (q : Point → ℚ) (S : Finset Point) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S,
    x ≠ y → y ≠ z → x ≠ z →
      ¬(distanceSq q x y = 1 ∧
        distanceSq q y z = 1 ∧ distanceSq q x z = 1)

def fullShearedLatticeUnitSeparated (r : ℕ) : Prop :=
  ∀ p p' : Point, p ≠ p' → 1 ≤ distanceSq (shearedQ r) p p'

def onlyShearedUnitDirections (r : ℕ) : Prop :=
  ∀ p : Point,
    shearedQ r p = 1 ↔
      p = ((1 : ℤ), (0 : ℤ)) ∨
      p = ((-1 : ℤ), (0 : ℤ)) ∨
      p = ((0 : ℤ), (1 : ℤ)) ∨
      p = ((0 : ℤ), (-1 : ℤ))

/-- Claim 31403: the sheared hexagonal source and its exact order and unit graph. -/
def claim31403 : Prop :=
  ∀ (r a b c d : ℕ),
    1 ≤ r → a ≤ r → b ≤ r → c ≤ r → d ≤ r →
    0 < a + b + c + d →
      fullShearedLatticeUnitSeparated r ∧
      onlyShearedUnitDirections r ∧
      pairwiseUnitSeparated (shearedQ r) (source r a b c d) ∧
      unitConnected (shearedQ r) (source r a b c d) ∧
      triangleFree (shearedQ r) (source r a b c d) ∧
      (source r a b c d).card = 3 * r ^ 2 + 3 * r + 1 + a + b + c + d

def rightTip (r a : ℕ) : Point :=
  (((r + a : ℕ) : ℤ), -((a : ℕ) : ℤ))

def upTip (r b : ℕ) : Point :=
  (((b : ℕ) : ℤ), ((r : ℕ) : ℤ))

def leftTip (r c : ℕ) : Point :=
  (-((r + c : ℕ) : ℤ), ((c : ℕ) : ℤ))

def downTip (r d : ℕ) : Point :=
  (-((d : ℕ) : ℤ), -((r : ℕ) : ℤ))

def turnedTips (r a b c d : ℕ) : Finset Point :=
  {rightTip r a, upTip r b, leftTip r c, downTip r d}

def hexVertices (r : ℕ) : Finset Point :=
  {((r : ℤ), (0 : ℤ)), ((r : ℤ), -(r : ℤ)),
   ((0 : ℤ), -(r : ℤ)), (-(r : ℤ), (0 : ℤ)),
   (-(r : ℤ), (r : ℤ)), ((0 : ℤ), (r : ℤ))}

def containsEquilateralTriangle (q : Point → ℚ) (S : Finset Point) : Prop :=
  ∃ x y z : Point,
    x ∈ S ∧ y ∈ S ∧ z ∈ S ∧
    x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
    distanceSq q x y = 1 ∧
    distanceSq q y z = 1 ∧
    distanceSq q x z = 1

def isUnitLatticeTail (q : Point → ℚ) (base step : Point)
    (tail : Finset Point) (n : ℕ) : Prop :=
  distanceSq q step (0, 0) = 1 ∧
    tail = (Finset.Icc 1 n).image (fun t : ℕ =>
      base + (t : ℤ) • step)

def crossMaximumReduction (S T : Finset Point) (q : Point → ℚ)
    (vertices tips : Finset Point) : Prop :=
  ∀ p ∈ S, ∀ p' ∈ T,
    ∃ v ∈ vertices, ∃ w ∈ tips,
      distanceSq q p p' ≤ distanceSq q v w

/-- Claim 31404: the simultaneously turned triangular-lattice target. -/
def claim31404 : Prop :=
  ∀ (r a b c d : ℕ),
    1 ≤ r → a ≤ r → b ≤ r → c ≤ r → d ≤ r →
    0 < a + b + c + d →
      (target r a b c d).card = 3 * r ^ 2 + 3 * r + 1 + a + b + c + d ∧
      pairwiseUnitSeparated triQ (target r a b c d) ∧
      containsEquilateralTriangle triQ (hexCore r) ∧
      isUnitLatticeTail triQ ((r : ℤ), (0 : ℤ)) ((1 : ℤ), (-1 : ℤ))
        (rightTurnedTail r a) a ∧
      isUnitLatticeTail triQ ((0 : ℤ), (r : ℤ)) ((1 : ℤ), (0 : ℤ))
        (upTurnedTail r b) b ∧
      isUnitLatticeTail triQ (-(r : ℤ), (0 : ℤ)) ((-1 : ℤ), (1 : ℤ))
        (leftTurnedTail r c) c ∧
      isUnitLatticeTail triQ ((0 : ℤ), -(r : ℤ)) ((-1 : ℤ), (0 : ℤ))
        (downTurnedTail r d) d ∧
      crossMaximumReduction (source r a b c d) (target r a b c d) triQ
        (hexVertices r) (turnedTips r a b c d)

def hSpan (r a c : ℕ) : ℚ :=
  2 * (r : ℚ) + (a : ℚ) + (c : ℚ)

def vSpan (r b d : ℕ) : ℚ :=
  2 * (r : ℚ) + (b : ℚ) + (d : ℚ)

def mSpan (r a b c d : ℕ) : ℚ :=
  max (hSpan r a c) (vSpan r b d)

def rightSourceTip (r a : ℕ) : Point :=
  (((r + a : ℕ) : ℤ), (0 : ℤ))

def leftSourceTip (r c : ℕ) : Point :=
  (-((r + c : ℕ) : ℤ), (0 : ℤ))

def upSourceTip (r b : ℕ) : Point :=
  ((0 : ℤ), ((r + b : ℕ) : ℤ))

def downSourceTip (r d : ℕ) : Point :=
  ((0 : ℤ), -((r + d : ℕ) : ℤ))

def diameterSq (q : Point → ℚ) (S : Finset Point) : ℚ :=
  if h : (S.product S).Nonempty then
    (S.product S).sup' h (fun pp => distanceSq q pp.1 pp.2)
  else 0

def sourceSpanWitnesses (r a b c d : ℕ) : Prop :=
  let S := source r a b c d
  rightSourceTip r a ∈ S ∧ leftSourceTip r c ∈ S ∧
  upSourceTip r b ∈ S ∧ downSourceTip r d ∈ S ∧
  distanceSq (shearedQ r) (rightSourceTip r a) (leftSourceTip r c) =
    hSpan r a c ^ 2 ∧
  distanceSq (shearedQ r) (upSourceTip r b) (downSourceTip r d) =
    vSpan r b d ^ 2 ∧
  mSpan r a b c d ^ 2 ≤ diameterSq (shearedQ r) S

def explicitTargetBounds (r a b c d : ℕ) : Prop :=
  let R := rightTip r a
  let U := upTip r b
  let L := leftTip r c
  let B := downTip r d
  let H := hSpan r a c
  let V := vSpan r b d
  distanceSq triQ R ((-(r : ℤ)), (0 : ℤ)) =
      4 * (r : ℚ) ^ 2 + 2 * (r : ℚ) * (a : ℚ) + (a : ℚ) ^ 2 ∧
  distanceSq triQ R ((-(r : ℤ)), (r : ℤ)) =
      3 * (r : ℚ) ^ 2 + 3 * (r : ℚ) * (a : ℚ) + (a : ℚ) ^ 2 ∧
  distanceSq triQ R ((-(r : ℤ)), (0 : ℤ)) < (2 * (r : ℚ) + (a : ℚ)) ^ 2 ∧
  distanceSq triQ R ((-(r : ℤ)), (r : ℤ)) < (2 * (r : ℚ) + (a : ℚ)) ^ 2 ∧
  (2 * (r : ℚ) + (a : ℚ)) ^ 2 ≤ H ^ 2 ∧
  distanceSq triQ R L =
      4 * (r : ℚ) ^ 2 + 2 * (r : ℚ) * ((a + c : ℕ) : ℚ) +
        ((a + c : ℕ) : ℚ) ^ 2 ∧
  (0 < a + c → distanceSq triQ R L < H ^ 2) ∧
  distanceSq triQ U B =
      4 * (r : ℚ) ^ 2 + 2 * (r : ℚ) * ((b + d : ℕ) : ℚ) +
        ((b + d : ℕ) : ℚ) ^ 2 ∧
  (0 < b + d → distanceSq triQ U B < V ^ 2) ∧
  distanceSq triQ R U ≤ (r + a : ℕ) ^ 2 ∧
  (r + a : ℕ) ^ 2 < H ^ 2 ∧
  (2 * (r : ℚ) + (d : ℚ)) ^ 2 - distanceSq triQ R B =
      ((r - a : ℕ) : ℚ) * ((r + a + d : ℕ) : ℚ) ∧
  0 ≤ (2 * (r : ℚ) + (d : ℚ)) ^ 2 - distanceSq triQ R B ∧
  (2 * (r : ℚ) + (b : ℚ)) ^ 2 - distanceSq triQ U L =
      ((r - c : ℕ) : ℚ) * ((r + b + c : ℕ) : ℚ) ∧
  0 ≤ (2 * (r : ℚ) + (b : ℚ)) ^ 2 - distanceSq triQ U L

def exceptionalEqualityCases (r a b c d : ℕ) : Prop :=
  diameterSq triQ (target r a b c d) = mSpan r a b c d ^ 2 →
    (a = r ∧ b = 0 ∧ c = 0 ∧ d = r) ∨
    (a = 0 ∧ b = r ∧ c = r ∧ d = 0)

def exceptionalSourceDistances (r a b c d : ℕ) : Prop :=
  (a = r ∧ b = 0 ∧ c = 0 ∧ d = r →
    rightSourceTip r a - downSourceTip r d =
        ((2 * (r : ℤ)), (2 * (r : ℤ))) ∧
    distanceSq (shearedQ r) (rightSourceTip r a) (downSourceTip r d) =
        12 * (r : ℚ) ^ 2 - (r : ℚ) / 2 ∧
    12 * (r : ℚ) ^ 2 - (r : ℚ) / 2 > 9 * (r : ℚ) ^ 2 ∧
    mSpan r a b c d ^ 2 = 9 * (r : ℚ) ^ 2) ∧
  (a = 0 ∧ b = r ∧ c = r ∧ d = 0 →
    upSourceTip r b - leftSourceTip r c =
        ((2 * (r : ℤ)), (2 * (r : ℤ))) ∧
    distanceSq (shearedQ r) (upSourceTip r b) (leftSourceTip r c) =
        12 * (r : ℚ) ^ 2 - (r : ℚ) / 2 ∧
    12 * (r : ℚ) ^ 2 - (r : ℚ) / 2 > 9 * (r : ℚ) ^ 2 ∧
    mSpan r a b c d ^ 2 = 9 * (r : ℚ) ^ 2)

/-- Claim 31405: the target diameter bound, equality cases, and strict comparison. -/
def claim31405 : Prop :=
  ∀ (r a b c d : ℕ),
    1 ≤ r → a ≤ r → b ≤ r → c ≤ r → d ≤ r →
    0 < a + b + c + d →
      sourceSpanWitnesses r a b c d ∧
      explicitTargetBounds r a b c d ∧
      diameterSq triQ (target r a b c d) ≤ mSpan r a b c d ^ 2 ∧
      exceptionalEqualityCases r a b c d ∧
      exceptionalSourceDistances r a b c d ∧
      diameterSq triQ (target r a b c d) <
        diameterSq (shearedQ r) (source r a b c d)

end

end MathlibPlus.Open.Research.R2146
