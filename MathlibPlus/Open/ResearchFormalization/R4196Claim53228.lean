import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R4196

open scoped BigOperators

private inductive QueryTree where
  | leaf (value : ℤ)
  | query (coordinate : ℕ) (minus plus : QueryTree)

private def negateTree : QueryTree → QueryTree
  | .leaf value => .leaf (-value)
  | .query coordinate minus plus =>
      .query coordinate (negateTree minus) (negateTree plus)

private def treeValue : QueryTree → (ℕ → Bool) → ℤ
  | .leaf value, _ => value
  | .query coordinate minus plus, x =>
      match x coordinate with
      | false => treeValue minus x
      | true => treeValue plus x

private def queryPath : QueryTree → (ℕ → Bool) → List ℕ
  | .leaf _, _ => []
  | .query coordinate minus plus, x =>
      coordinate ::
        match x coordinate with
        | false => queryPath minus x
        | true => queryPath plus x

private def appendLayers : List (List ℕ) → List (List ℕ) → List (List ℕ)
  | [], right => right
  | left, [] => left
  | leftHead :: leftTail, rightHead :: rightTail =>
      (leftHead ++ rightHead) :: appendLayers leftTail rightTail

private structure PathProductData where
  tree : QueryTree
  layers : List (List ℕ)

private def buildPathProduct : ℕ → ℕ → PathProductData
  | 0, offset =>
      { tree := .leaf 1
        layers := [] }
  | depth + 1, offset =>
      let left := buildPathProduct depth (offset + 1)
      let right := buildPathProduct depth (offset + 1 + ((2 : ℕ) ^ depth - 1))
      { tree := .query offset (negateTree left.tree) right.tree
        layers := [ [offset] ] ++ appendLayers left.layers right.layers }

private def pathProductData (depth : ℕ) : PathProductData :=
  buildPathProduct depth 0

private def pathProductTree (depth : ℕ) : QueryTree :=
  (pathProductData depth).tree

private def pathProductCoordinateCount (depth : ℕ) : ℕ :=
  (2 : ℕ) ^ depth - 1

private def bottomUpOrder (depth : ℕ) : List ℕ :=
  ((pathProductData depth).layers.reverse).flatten

private def parityValue (depth : ℕ) (x : ℕ → Bool) : ℤ :=
  ∏ i ∈ Finset.range (pathProductCoordinateCount depth),
    if x i then 1 else -1

private def independentLiteralValue (depth : ℕ) (x : ℕ → Bool) : ℤ :=
  if x (pathProductCoordinateCount depth) then 1 else -1

private def pointValue {n : ℕ} (point : Fin n → Bool) (i : ℕ) : Bool :=
  if h : i < n then point ⟨i, h⟩ else false

private def stateCompatible {n : ℕ}
    (state : ℕ → Option Bool) (point : Fin n → Bool) : Prop :=
  ∀ i b, state i = some b → ∃ h : i < n, point ⟨i, h⟩ = b

private noncomputable def completionSet {n : ℕ}
    (state : ℕ → Option Bool) : Finset (Fin n → Bool) :=
  let _ : DecidablePred (fun point : Fin n → Bool =>
      stateCompatible state point) :=
    fun _ => Classical.propDecidable _
  Finset.univ.filter (fun point => stateCompatible state point)

private def emptyState : ℕ → Option Bool :=
  fun _ => none

private def revealState
    (state : ℕ → Option Bool) (coordinate : ℕ) (value : Bool) :
    ℕ → Option Bool :=
  Function.update state coordinate (some value)

private noncomputable def pathProbability {n : ℕ}
    (tree : QueryTree) (state : ℕ → Option Bool) (coordinate : ℕ) : ℚ :=
  ((completionSet (n := n) state).filter (fun point =>
      coordinate ∈ queryPath tree (fun i => pointValue (n := n) point i))).card /
    ((completionSet (n := n) state).card : ℚ)

private noncomputable def conditionalPacket {n : ℕ}
    (tree : QueryTree) (state : ℕ → Option Bool) (coordinate : ℕ) : ℚ :=
  (completionSet (n := n) state).sum (fun point =>
      (treeValue tree (fun i => pointValue (n := n) point i) : ℚ) *
        (if pointValue (n := n) point coordinate then 1 else -1)) /
    ((completionSet (n := n) state).card : ℚ)

private noncomputable def directContribution {n : ℕ}
    (tree : QueryTree) :
    List ℕ → (Fin n → Bool) → ℕ → (ℕ → Option Bool) → ℚ
  | [], _, _, _ => 0
  | coordinate :: rest, point, position, state =>
      let packet := conditionalPacket (n := n) tree state coordinate
      (position : ℚ) /
          (Fintype.card (Fin n → Bool) : ℚ) * packet ^ 2 +
        directContribution tree rest point (position + 1)
          (revealState state coordinate (pointValue (n := n) point coordinate))

private noncomputable def directAreaFromTree {n : ℕ}
    (tree : QueryTree) (order : List ℕ) : ℚ :=
  ∑ point : Fin n → Bool,
    directContribution tree order point 1 emptyState

private noncomputable def pathProductDirectArea (depth : ℕ) : ℚ :=
  directAreaFromTree (n := pathProductCoordinateCount depth)
    (pathProductTree depth) (bottomUpOrder depth)

private def pathProductFamilyNonredundant (depth : ℕ) : Prop :=
  (∀ x : ℕ → Bool,
    List.Nodup (queryPath (pathProductTree depth) x)) ∧
    List.Nodup (bottomUpOrder depth)

private noncomputable def symmetricJointResidualQueryCostMargin (depth : ℕ) : ℚ :=
  2 * (pathProductCoordinateCount depth : ℚ) +
    8 * (depth : ℚ) - 3 * pathProductDirectArea depth

/-- Claim 53228: on the explicit complete path-product/parity/literal family,
the tested symmetric residual-query-cost replacement has the displayed
nonnegative range and the first negative margin at depth six. -/
def claim53228_failedResidualCostReplacement : Prop :=
  (∀ depth : ℕ, 1 ≤ depth → depth ≤ 5 →
    pathProductFamilyNonredundant depth ∧
      pathProductDirectArea depth =
        (pathProductCoordinateCount depth : ℚ) -
          3 * ((depth - 1 : ℕ) : ℚ) / 4 ∧
      symmetricJointResidualQueryCostMargin depth =
        (41 * (depth : ℚ) - 9) / 4 -
          ((2 : ℚ) ^ depth - 1) ∧
      0 ≤ symmetricJointResidualQueryCostMargin depth) ∧
    pathProductFamilyNonredundant 6 ∧
      pathProductDirectArea 6 =
        (pathProductCoordinateCount 6 : ℚ) -
          3 * ((6 - 1 : ℕ) : ℚ) / 4 ∧
      symmetricJointResidualQueryCostMargin 6 = -15 / 4 ∧
      symmetricJointResidualQueryCostMargin 6 < 0

end MathlibPlus.Open.ResearchFormalization.R4196
