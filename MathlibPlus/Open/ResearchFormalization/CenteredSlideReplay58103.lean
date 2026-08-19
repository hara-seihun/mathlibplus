import MathlibPlus.Open.ResearchFormalizationBatch_53368

namespace MathlibPlus.Open.ResearchFormalization.CenteredSlideReplay58103

noncomputable section

open Classical
open scoped BigOperators
open MathlibPlus.Open.ResearchFormalizationBatch_53368

attribute [local instance] Classical.propDecidable Classical.decEq

abbrev Vertex (m : ℕ) := Fin (m + 2)
abbrev EdgeSet (m : ℕ) := Finset (Vertex m × Vertex m)

noncomputable def normalizedEdge {m : ℕ} (u v : Vertex m) : Vertex m × Vertex m :=
  if u.val ≤ v.val then (u, v) else (v, u)

def sortedEdges {m : ℕ} (E : EdgeSet m) : Prop :=
  ∀ e ∈ E, e.1.val < e.2.val

def graph58103 {m : ℕ} (E : EdgeSet m) : SimpleGraph (Vertex m) :=
  SimpleGraph.fromRel (edgeRelation53368 E)

def edgeCode {m : ℕ} (E : EdgeSet m) : ℕ :=
  ∑ e ∈ E, 2 ^ (e.1.val * (m + 2) + e.2.val)

def canonicalTree58103 {m : ℕ} (E : EdgeSet m) : Prop :=
  treeEdges53368 E ∧ sortedEdges E ∧
    ∀ F : EdgeSet m, treeEdges53368 F → sortedEdges F →
      graphIso53368 E F → edgeCode E ≤ edgeCode F

noncomputable def canonicalTrees58103 (m : ℕ) : Finset (EdgeSet m) :=
  (Finset.univ : Finset (EdgeSet m)).filter canonicalTree58103

def strictCentroid58103 {m : ℕ} (E : EdgeSet m) (c : Vertex m) : Prop :=
  ∀ v : Vertex m, v ≠ c →
    2 * (deletedComponent53368 E c v).card < m + 2

def uniqueCentroid58103 {m : ℕ} (E : EdgeSet m) (c : Vertex m) : Prop :=
  treeEdges53368 E ∧ strictCentroid58103 E c ∧
    ∀ d : Vertex m, strictCentroid58103 E d → d = c

def cutEdgeRelation58103 {m : ℕ} (E : EdgeSet m)
    (cut : Vertex m × Vertex m) (u v : Vertex m) : Prop :=
  edgeRelation53368 E u v ∧ normalizedEdge u v ≠ normalizedEdge cut.1 cut.2

def cutReachable58103 {m : ℕ} (E : EdgeSet m)
    (cut : Vertex m × Vertex m) (u v : Vertex m) : Prop :=
  Relation.ReflTransGen (cutEdgeRelation58103 E cut) u v

noncomputable def cutComponent58103 {m : ℕ} (E : EdgeSet m)
    (cut : Vertex m × Vertex m) (u : Vertex m) : Finset (Vertex m) :=
  Finset.univ.filter (fun v => cutReachable58103 E cut u v)

def edgeRemovedReachable58103 {m : ℕ} (E : EdgeSet m)
    (cuts : Finset (Vertex m × Vertex m)) (u v : Vertex m) : Prop :=
  Relation.ReflTransGen
    (fun a b => edgeRelation53368 E a b ∧ normalizedEdge a b ∉ cuts) u v

noncomputable def componentAfterCuts58103 {m : ℕ} (E : EdgeSet m)
    (cuts : Finset (Vertex m × Vertex m)) (u : Vertex m) : Finset (Vertex m) :=
  Finset.univ.filter (fun v => edgeRemovedReachable58103 E cuts u v)

def depth58103 {m : ℕ} (E : EdgeSet m) (r v : Vertex m) : ℕ :=
  (graph58103 E).dist r v

def descendantSet58103 {m : ℕ} (E : EdgeSet m)
    (r x : Vertex m) : Finset (Vertex m) :=
  Finset.univ.filter (fun v =>
    depth58103 E r v = depth58103 E r x + depth58103 E x v)

noncomputable def parentCandidates58103 {m : ℕ} (E : EdgeSet m)
    (r x : Vertex m) : Finset (Vertex m) :=
  Finset.univ.filter (fun p =>
    (graph58103 E).Adj p x ∧ depth58103 E r p + 1 = depth58103 E r x)

noncomputable def chooseVertex58103 {m : ℕ} (s : Finset (Vertex m)) : Vertex m :=
  if h : s.Nonempty then s.min' h else Fin.ofNat (m + 2) 0

def parent58103 {m : ℕ} (E : EdgeSet m) (r x : Vertex m) : Vertex m :=
  chooseVertex58103 (parentCandidates58103 E r x)

def candidateVertices58103 {m : ℕ} (E : EdgeSet m)
    (r : Vertex m) : Finset (Vertex m) :=
  Finset.univ.filter (fun x => 2 ≤ depth58103 E r x)

noncomputable def candidateScore58103 {m : ℕ} (E : EdgeSet m)
    (r x : Vertex m) : ℕ :=
  depth58103 E r x * (m + 3) + x.val

noncomputable def maximalCandidates58103 {m : ℕ} (E : EdgeSet m)
    (r : Vertex m) : Finset (Vertex m) :=
  (candidateVertices58103 E r).filter (fun x =>
    ∀ y ∈ candidateVertices58103 E r,
      candidateScore58103 E r y ≤ candidateScore58103 E r x)

noncomputable def selectedVertex58103 {m : ℕ} (E : EdgeSet m)
    (r : Vertex m) : Vertex m :=
  chooseVertex58103 (maximalCandidates58103 E r)

def hasCandidate58103 {m : ℕ} (E : EdgeSet m) (r : Vertex m) : Prop :=
  (candidateVertices58103 E r).Nonempty

def slideGraph58103 {m : ℕ} (E : EdgeSet m)
    (x p g : Vertex m) : EdgeSet m :=
  insert (normalizedEdge g x) (E.erase (normalizedEdge p x))

noncomputable def nextGraph58103 {m : ℕ} (E : EdgeSet m)
    (r : Vertex m) : EdgeSet m :=
  if h : hasCandidate58103 E r then
    let x := selectedVertex58103 E r
    let p := parent58103 E r x
    let g := parent58103 E r p
    slideGraph58103 E x p g
  else E

noncomputable def uniqueRun58103 {m : ℕ} (E : EdgeSet m)
    (r : Vertex m) (t : ℕ) : EdgeSet m :=
  Nat.iterate (fun F => nextGraph58103 F r) t E

def rootedEnergy58103 {m : ℕ} (E : EdgeSet m) (r : Vertex m) : ℕ :=
  ∑ v : Vertex m, depth58103 E r v

def threePieceCut58103 {m : ℕ} (before : EdgeSet m)
    (x p g : Vertex m) : Prop :=
  let cuts : Finset (Vertex m × Vertex m) :=
    {normalizedEdge p x, normalizedEdge p g}
  let moved := componentAfterCuts58103 before cuts x
  let pPiece := componentAfterCuts58103 before cuts p
  let gPiece := componentAfterCuts58103 before cuts g
  moved.Nonempty ∧ pPiece.Nonempty ∧ gPiece.Nonempty ∧
    (∀ v, v ∈ moved → v ∉ pPiece ∧ v ∉ gPiece) ∧
      (∀ v, v ∈ pPiece → v ∉ gPiece) ∧
        moved ∪ pPiece ∪ gPiece = (Finset.univ : Finset (Vertex m))

def uniqueSlideCertificate58103 {m : ℕ} (before after : EdgeSet m)
    (r x p g : Vertex m) : Prop :=
  treeEdges53368 before ∧
    treeEdges53368 after ∧
      (graph58103 before).Adj p x ∧
        (graph58103 before).Adj p g ∧
          ¬ (graph58103 before).Adj g x ∧
            after = slideGraph58103 before x p g ∧
              threePieceCut58103 before x p g ∧
                descendantSet58103 before r x =
                  componentAfterCuts58103 before
                    ({normalizedEdge p x, normalizedEdge p g} :
                      Finset (Vertex m × Vertex m)) x ∧
                  rootedEnergy58103 after r < rootedEnergy58103 before r ∧
                    rootedEnergy58103 before r - rootedEnergy58103 after r =
                      (descendantSet58103 before r x).card

def uniqueStrictHost58103 {m : ℕ} (before : EdgeSet m)
    (r x p g : Vertex m) : Prop :=
  ∃ activeOrder : ℕ,
    activeOrder < m + 2 ∧
      activeOrder =
        (deletedComponent53368 before r x).card +
          if g = r then 1 else 0

structure uniqueReplayRecord58103 (m : ℕ) where
  initial : EdgeSet m
  root : Vertex m
  time : Fin ((m + 2) ^ 3)

def isUniqueReplayRecord58103 {m : ℕ}
    (record : uniqueReplayRecord58103 m) : Prop :=
  canonicalTree58103 record.initial ∧
    uniqueCentroid58103 record.initial record.root ∧
      record.time.val < (m + 2) ^ 3 ∧
        hasCandidate58103
          (uniqueRun58103 record.initial record.root record.time.val)
          record.root

def uniqueRecordBefore58103 {m : ℕ}
    (record : uniqueReplayRecord58103 m) : EdgeSet m :=
  uniqueRun58103 record.initial record.root record.time.val

def uniqueRecordVertex58103 {m : ℕ}
    (record : uniqueReplayRecord58103 m) : Vertex m :=
  selectedVertex58103 (uniqueRecordBefore58103 record) record.root

def uniqueRecordParent58103 {m : ℕ}
    (record : uniqueReplayRecord58103 m) : Vertex m :=
  parent58103 (uniqueRecordBefore58103 record) record.root
    (uniqueRecordVertex58103 record)

def uniqueRecordGrandparent58103 {m : ℕ}
    (record : uniqueReplayRecord58103 m) : Vertex m :=
  parent58103 (uniqueRecordBefore58103 record) record.root
    (uniqueRecordParent58103 record)

def uniqueRecordAfter58103 {m : ℕ}
    (record : uniqueReplayRecord58103 m) : EdgeSet m :=
  nextGraph58103 (uniqueRecordBefore58103 record) record.root

def isPhysicalUniqueRecord58103 {m : ℕ}
    (record : uniqueReplayRecord58103 m) : Prop :=
  isUniqueReplayRecord58103 record ∧
    uniqueSlideCertificate58103 (uniqueRecordBefore58103 record)
      (uniqueRecordAfter58103 record) (record.root)
      (uniqueRecordVertex58103 record)
      (uniqueRecordParent58103 record)
      (uniqueRecordGrandparent58103 record) ∧
        uniqueCentroid58103 (uniqueRecordAfter58103 record) record.root ∧
          uniqueStrictHost58103 (uniqueRecordBefore58103 record)
            record.root (uniqueRecordVertex58103 record)
            (uniqueRecordParent58103 record)
            (uniqueRecordGrandparent58103 record)

abbrev UniqueRecordSet58103 (m : ℕ) :=
  {r : uniqueReplayRecord58103 m // isUniqueReplayRecord58103 r}

abbrev PhysicalUniqueRecordSet58103 (m : ℕ) :=
  {r : uniqueReplayRecord58103 m // isPhysicalUniqueRecord58103 r}

def bicentroid58103 {m : ℕ} (E : EdgeSet m) (a b : Vertex m) : Prop :=
  treeEdges53368 E ∧ a ≠ b ∧
    (graph58103 E).Adj a b ∧
      let sideA := cutComponent58103 E (a, b) a
      let sideB := cutComponent58103 E (a, b) b
      sideA.card = sideB.card ∧
        sideA ∪ sideB = (Finset.univ : Finset (Vertex m)) ∧
          (∀ v : Vertex m,
            centroid53368 E v ↔ v = a ∨ v = b)

noncomputable def halfEdges58103 {m : ℕ} (E : EdgeSet m)
    (side : Finset (Vertex m)) : EdgeSet m :=
  E.filter (fun e => e.1 ∈ side ∧ e.2 ∈ side)

def treeEdgesOnSide58103 {m : ℕ} (E : EdgeSet m)
    (side : Finset (Vertex m)) : Prop :=
  side.Nonempty ∧
    (∀ u ∈ side, ∀ v ∈ side,
      Relation.ReflTransGen
        (fun a b => edgeRelation53368 E a b ∧ a ∈ side ∧ b ∈ side) u v) ∧
      (halfEdges58103 E side).card = side.card - 1

noncomputable def sideComponentAfterCuts58103 {m : ℕ}
    (E : EdgeSet m) (side : Finset (Vertex m))
    (cuts : Finset (Vertex m × Vertex m)) (u : Vertex m) :
    Finset (Vertex m) :=
  (componentAfterCuts58103 E cuts u).filter (fun v => v ∈ side)

def threePieceSideCut58103 {m : ℕ} (before : EdgeSet m)
    (side : Finset (Vertex m)) (x p g : Vertex m) : Prop :=
  let cuts : Finset (Vertex m × Vertex m) :=
    {normalizedEdge p x, normalizedEdge p g}
  let moved := sideComponentAfterCuts58103 before side cuts x
  let pPiece := sideComponentAfterCuts58103 before side cuts p
  let gPiece := sideComponentAfterCuts58103 before side cuts g
  moved.Nonempty ∧ pPiece.Nonempty ∧ gPiece.Nonempty ∧
    (∀ v, v ∈ moved → v ∉ pPiece ∧ v ∉ gPiece) ∧
      (∀ v, v ∈ pPiece → v ∉ gPiece) ∧
        moved ∪ pPiece ∪ gPiece = side

def halfSlideCertificate58103 {m : ℕ} (before after : EdgeSet m)
    (side : Finset (Vertex m)) (r x p g : Vertex m) : Prop :=
  treeEdgesOnSide58103 before side ∧
    treeEdgesOnSide58103 after side ∧
      (graph58103 before).Adj p x ∧
        (graph58103 before).Adj p g ∧
          ¬ (graph58103 before).Adj g x ∧
            after = slideGraph58103 before x p g ∧
              threePieceSideCut58103 before side x p g ∧
                rootedEnergy58103 after r < rootedEnergy58103 before r ∧
                  rootedEnergy58103 before r - rootedEnergy58103 after r =
                    (sideComponentAfterCuts58103 before side
                      ({normalizedEdge p x, normalizedEdge p g} :
                        Finset (Vertex m × Vertex m)) x).card

noncomputable def bicentroidSides58103 {m : ℕ} (E : EdgeSet m)
    (a b : Vertex m) : Finset (Vertex m) × Finset (Vertex m) :=
  (cutComponent58103 E (a, b) a, cutComponent58103 E (a, b) b)

structure bicentroidState58103 (m : ℕ) where
  left : EdgeSet m
  right : EdgeSet m

noncomputable def initialBicentroidState58103 {m : ℕ}
    (E : EdgeSet m) (a b : Vertex m) : bicentroidState58103 m :=
  let sides := bicentroidSides58103 E a b
  { left := halfEdges58103 E sides.1
    right := halfEdges58103 E sides.2 }

noncomputable def nextBicentroidState58103 {m : ℕ}
    (state : bicentroidState58103 m) (a b : Vertex m) : bicentroidState58103 m :=
  if leftStep : hasCandidate58103 state.left a then
    { left := nextGraph58103 state.left a, right := state.right }
  else if rightStep : hasCandidate58103 state.right b then
    { left := state.left, right := nextGraph58103 state.right b }
  else state

noncomputable def bicentroidRun58103 {m : ℕ}
    (state : bicentroidState58103 m) (a b : Vertex m) (t : ℕ) :
    bicentroidState58103 m :=
  Nat.iterate (fun s => nextBicentroidState58103 s a b) t state

structure bicentroidReplayRecord58103 (m : ℕ) where
  initial : EdgeSet m
  leftCenter : Vertex m
  rightCenter : Vertex m
  time : Fin ((m + 2) ^ 3)

def isBicentroidReplayRecord58103 {m : ℕ}
    (record : bicentroidReplayRecord58103 m) : Prop :=
  canonicalTree58103 record.initial ∧
    bicentroid58103 record.initial record.leftCenter record.rightCenter ∧
      record.leftCenter.val < record.rightCenter.val ∧
        record.time.val < (m + 2) ^ 3 ∧
          (hasCandidate58103
              (bicentroidRun58103
                (initialBicentroidState58103 record.initial
                  record.leftCenter record.rightCenter)
                record.leftCenter record.rightCenter record.time.val).left
                record.leftCenter ∨
            hasCandidate58103
              (bicentroidRun58103
                (initialBicentroidState58103 record.initial
                  record.leftCenter record.rightCenter)
                record.leftCenter record.rightCenter record.time.val).right
                record.rightCenter)

noncomputable def bicentroidRecordBefore58103 {m : ℕ}
    (record : bicentroidReplayRecord58103 m) : bicentroidState58103 m :=
  bicentroidRun58103
    (initialBicentroidState58103 record.initial
      record.leftCenter record.rightCenter)
    record.leftCenter record.rightCenter record.time.val

noncomputable def bicentroidRecordAfter58103 {m : ℕ}
    (record : bicentroidReplayRecord58103 m) : bicentroidState58103 m :=
  nextBicentroidState58103 (bicentroidRecordBefore58103 record)
    record.leftCenter record.rightCenter

def bicentroidSlideCertificate58103 {m : ℕ}
    (record : bicentroidReplayRecord58103 m) : Prop :=
  isBicentroidReplayRecord58103 record ∧
    let before := bicentroidRecordBefore58103 record
    let after := bicentroidRecordAfter58103 record
    let sides := bicentroidSides58103 record.initial
      record.leftCenter record.rightCenter
    sides.1.card = sides.2.card ∧
      (hasCandidate58103 before.left record.leftCenter →
      let x := selectedVertex58103 before.left record.leftCenter
      let p := parent58103 before.left record.leftCenter x
      let g := parent58103 before.left record.leftCenter p
      halfSlideCertificate58103 before.left after.left sides.1
        record.leftCenter x p g ∧ before.right = after.right) ∧
      (¬ hasCandidate58103 before.left record.leftCenter →
        hasCandidate58103 before.right record.rightCenter →
          let x := selectedVertex58103 before.right record.rightCenter
          let p := parent58103 before.right record.rightCenter x
          let g := parent58103 before.right record.rightCenter p
          halfSlideCertificate58103 before.right after.right sides.2
            record.rightCenter x p g ∧ before.left = after.left)

def bicentroidStrictHost58103 {m : ℕ}
    (record : bicentroidReplayRecord58103 m) : Prop :=
  let sides := bicentroidSides58103 record.initial
    record.leftCenter record.rightCenter
  sides.1.card < m + 2 ∧ sides.2.card < m + 2

abbrev BicentroidRecordSet58103 (m : ℕ) :=
  {r : bicentroidReplayRecord58103 m // isBicentroidReplayRecord58103 r}

abbrev PhysicalBicentroidRecordSet58103 (m : ℕ) :=
  {r : bicentroidReplayRecord58103 m // bicentroidSlideCertificate58103 r}

noncomputable def replayTreeCount58103 : ℕ :=
  ∑ m ∈ Finset.range 11, treeCount53368 (m + 2)

noncomputable def replayUniqueCentroidCount58103 : ℕ :=
  ∑ m ∈ Finset.range 11, legalTreeCount53368 (m + 2)

noncomputable def replayBicentroidCount58103 : ℕ :=
  replayTreeCount58103 - replayUniqueCentroidCount58103

noncomputable def replayUniqueSlideCount58103 : ℕ :=
  ∑ m ∈ Finset.range 11,
    Nat.card (UniqueRecordSet58103 m)

noncomputable def replayBicentroidSlideCount58103 : ℕ :=
  ∑ m ∈ Finset.range 11,
    Nat.card (BicentroidRecordSet58103 m)

noncomputable def replayPhysicalSlideCount58103 : ℕ :=
  ∑ m ∈ Finset.range 11,
    (Nat.card (PhysicalUniqueRecordSet58103 m) +
      Nat.card (PhysicalBicentroidRecordSet58103 m))

noncomputable def replayStrictHostCheck58103 : Prop :=
  (∀ m ∈ Finset.range 11,
    ∀ r : UniqueRecordSet58103 m,
      uniqueStrictHost58103 (uniqueRecordBefore58103 r.1) r.1.root
        (uniqueRecordVertex58103 r.1)
        (uniqueRecordParent58103 r.1)
        (uniqueRecordGrandparent58103 r.1)) ∧
  (∀ m ∈ Finset.range 11,
    ∀ r : BicentroidRecordSet58103 m,
      bicentroidStrictHost58103 r.1)

def dependencyBoundary58103 : Prop :=
  replayStrictHostCheck58103 ∧
    (∀ m ∈ Finset.range 11,
      ∀ r : PhysicalUniqueRecordSet58103 m,
        uniqueSlideCertificate58103 (uniqueRecordBefore58103 r.1)
          (uniqueRecordAfter58103 r.1) r.1.root
          (uniqueRecordVertex58103 r.1)
          (uniqueRecordParent58103 r.1)
          (uniqueRecordGrandparent58103 r.1)) ∧
    (∀ m ∈ Finset.range 11,
      ∀ r : PhysicalBicentroidRecordSet58103 m,
        bicentroidStrictHost58103 r.1)

/-- Claim 58103: the finite canonical-tree replay records the exact census,
normalization-step counts, physical certificates, strict-host inequalities,
center invariants, and the local dependency-boundary checks.  It is an
alignment to the executable replay report only; it does not assert any of the
three downstream research questions. -/
def centeredSlideReplayClaim58103 : Prop :=
  replayTreeCount58103 = 986 ∧
    replayUniqueCentroidCount58103 = 716 ∧
      replayBicentroidCount58103 = 270 ∧
        replayUniqueSlideCount58103 = 6443 ∧
          replayBicentroidSlideCount58103 = 2288 ∧
            replayPhysicalSlideCount58103 = 8731 ∧
              replayStrictHostCheck58103 ∧
                dependencyBoundary58103

end

end MathlibPlus.Open.ResearchFormalization.CenteredSlideReplay58103
