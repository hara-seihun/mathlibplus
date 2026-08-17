import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R3861

noncomputable section

open scoped BigOperators
open Classical

inductive SignedBinaryTree : Nat → Type
  | leaf : SignedBinaryTree 0
  | node {d : Nat} (x : Bool) (left right : SignedBinaryTree d) :
      SignedBinaryTree (d + 1)

def allSignedBinaryTrees : (k : Nat) → Finset (SignedBinaryTree k)
  | 0 => {SignedBinaryTree.leaf}
  | d + 1 =>
      (allSignedBinaryTrees d).biUnion (fun left =>
        (allSignedBinaryTrees d).biUnion (fun right =>
          {SignedBinaryTree.node false left right,
            SignedBinaryTree.node true left right}))

def signValue (x : Bool) : ℚ :=
  if x then 1 else -1

def signedTreeValue : {k : Nat} → SignedBinaryTree k → ℚ
  | _, SignedBinaryTree.leaf => 1
  | _, SignedBinaryTree.node x left right =>
      if x then signedTreeValue right
      else -signedTreeValue left

def internalNodeCount : {k : Nat} → SignedBinaryTree k → Nat
  | _, SignedBinaryTree.leaf => 0
  | _, SignedBinaryTree.node _ left right =>
      1 + internalNodeCount left + internalNodeCount right

def binaryWords : Nat → Finset (List Bool)
  | 0 => {[]}
  | d + 1 =>
      (binaryWords d).biUnion (fun w =>
        {w ++ [false], w ++ [true]})

def internalPaths (k : Nat) : Finset (List Bool) :=
  (Finset.range k).biUnion binaryWords

def nodeSign : {k : Nat} → SignedBinaryTree k → List Bool → ℚ
  | _, SignedBinaryTree.leaf, _ => 0
  | _, SignedBinaryTree.node x _ _, [] => signValue x
  | _, SignedBinaryTree.node _ left _, false :: rest =>
      nodeSign left rest
  | _, SignedBinaryTree.node _ _ right, true :: rest =>
      nodeSign right rest

def subtreeValue : {k : Nat} → SignedBinaryTree k → List Bool → ℚ
  | _, SignedBinaryTree.leaf, _ => 1
  | _, tree, [] => signedTreeValue tree
  | _, SignedBinaryTree.node _ left _, false :: rest =>
      subtreeValue left rest
  | _, SignedBinaryTree.node _ _ right, true :: rest =>
      subtreeValue right rest

def selectedPath : {k : Nat} → SignedBinaryTree k → List (List Bool)
  | _, SignedBinaryTree.leaf => []
  | _, SignedBinaryTree.node x left right =>
      [] :: ((selectedPath (if x then right else left)).map (fun p => x :: p))

def selectedPathSignProduct {k : Nat} (tree : SignedBinaryTree k) : ℚ :=
  (selectedPath tree).foldl (fun z p => z * nodeSign tree p) 1

def requiredAncestorProduct (p : List Bool) : ℚ :=
  p.foldl (fun z x => z * signValue x) 1

def pathPrefix : List Bool → List Bool → Prop
  | [], _ => True
  | _ :: _, [] => False
  | x :: xs, y :: ys => x = y ∧ pathPrefix xs ys

def bottomUpLayerOrder (k : Nat) (order : List (List Bool)) : Prop :=
  order.Nodup ∧
    order.toFinset = internalPaths k ∧
    List.Pairwise (fun p q => q.length ≤ p.length) order

def prefixBefore {α : Type} [DecidableEq α] (p : α) : List α → List α
  | [] => []
  | q :: qs => if q = p then [] else q :: prefixBefore p qs

def preQueryTranscript {k : Nat}
    (tree : SignedBinaryTree k) (order : List (List Bool)) (p : List Bool) :
    List (List Bool × ℚ) :=
  (prefixBefore p order).map (fun q => (q, nodeSign tree q))

def fullTranscript {k : Nat}
    (tree : SignedBinaryTree k) (order : List (List Bool)) :
    List (List Bool × ℚ) :=
  order.map (fun q => (q, nodeSign tree q))

def preQueryNode (k : Nat) (order : List (List Bool)) (p : List Bool) : Prop :=
  p ∈ internalPaths k ∧
    p ∈ order ∧
    (∀ q ∈ prefixBefore p order,
      ¬ (pathPrefix q p ∧ q ≠ p)) ∧
    (∀ q ∈ internalPaths k,
      pathPrefix p q → q ≠ p → q ∈ prefixBefore p order)

def transcriptCompatible {k : Nat}
    (tree : SignedBinaryTree k) (order : List (List Bool))
    (p : List Bool) (transcript : List (List Bool × ℚ)) : Prop :=
  preQueryTranscript tree order p = transcript

def compatibleTrees50496 (k : Nat) (order : List (List Bool))
    (p : List Bool) (transcript : List (List Bool × ℚ)) :
    Finset (SignedBinaryTree k) :=
  (allSignedBinaryTrees k).filter
    (fun tree => transcriptCompatible tree order p transcript)

def conditionalPathProbability50496 (k : Nat) (order : List (List Bool))
    (p : List Bool) (transcript : List (List Bool × ℚ)) : ℚ :=
  let compatible := compatibleTrees50496 k order p transcript
  if compatible.card = 0 then 0
  else
    ((compatible.filter (fun tree => p ∈ selectedPath tree)).card : ℚ) /
      compatible.card

def conditionalCorrelation50496 (k : Nat) (order : List (List Bool))
    (p : List Bool) (transcript : List (List Bool × ℚ)) : ℚ :=
  let compatible := compatibleTrees50496 k order p transcript
  if compatible.card = 0 then 0
  else
    (∑ tree ∈ compatible,
      signedTreeValue tree * nodeSign tree p) / compatible.card

def packetRatio50496 (pValue cValue : ℚ) : ℚ :=
  if pValue = 0 then 0 else cValue ^ 2 / pValue

def compatibleFullTrees50496 (k : Nat) (order : List (List Bool))
    (transcript : List (List Bool × ℚ)) :
    Finset (SignedBinaryTree k) :=
  (allSignedBinaryTrees k).filter
    (fun tree => fullTranscript tree order = transcript)

def functionDetermined50496 (k : Nat) (order : List (List Bool))
    (transcript : List (List Bool × ℚ)) : Prop :=
  ∀ tree₁ ∈ compatibleFullTrees50496 k order transcript,
    ∀ tree₂ ∈ compatibleFullTrees50496 k order transcript,
      signedTreeValue tree₁ = signedTreeValue tree₂

def postDeterminationPathProbability50496
    (k : Nat) (order : List (List Bool))
    (transcript : List (List Bool × ℚ)) (_external : Nat) :
    Option ℚ :=
  if functionDetermined50496 k order transcript then some 0 else none

def postDeterminationCorrelation50496
    (k : Nat) (order : List (List Bool))
    (transcript : List (List Bool × ℚ)) (_external : Nat) :
    Option ℚ :=
  if functionDetermined50496 k order transcript then some 0 else none

def postDeterminationPacketRatio50496
    (k : Nat) (order : List (List Bool))
    (transcript : List (List Bool × ℚ)) (external : Nat) :
    Option ℚ :=
  match postDeterminationPathProbability50496 k order transcript external,
    postDeterminationCorrelation50496 k order transcript external with
  | some pValue, some cValue => some (packetRatio50496 pValue cValue)
  | _, _ => none

def querySchedule50494 (order : List (List Bool))
    (continuation : List Nat) : List (List Bool ⊕ Nat) :=
  order.map Sum.inl ++ continuation.map Sum.inr

def nodePacketRatio50497 {k : Nat}
    (tree : SignedBinaryTree k) (order : List (List Bool))
    (p : List Bool) : ℚ :=
  let transcript := preQueryTranscript tree order p
  packetRatio50496
    (conditionalPathProbability50496 k order p transcript)
    (conditionalCorrelation50496 k order p transcript)

def globalExpectation50497 (k : Nat) (order : List (List Bool)) : ℚ :=
  let assignments := allSignedBinaryTrees k
  if assignments.card = 0 then 0
  else
    (∑ tree ∈ assignments,
      ∑ p ∈ internalPaths k, nodePacketRatio50497 tree order p) /
      assignments.card

def layerExpectation50497 (k : Nat) (order : List (List Bool)) (d : Nat) : ℚ :=
  let assignments := allSignedBinaryTrees k
  let layer := (internalPaths k).filter (fun p => p.length = d)
  if assignments.card = 0 then 0
  else
    (∑ tree ∈ assignments,
      ∑ p ∈ layer, nodePacketRatio50497 tree order p) /
      assignments.card

/-- Claim 50494: the recursive signed tree, selected path product, exact
internal-node count, bottom-up layer order, and zero continuation packets are
retained on the complete independent-sign carrier. -/
def recursiveSignedTreeConstruction_claim50494 : Prop :=
  (∀ d : Nat, ∀ (x : Bool)
      (left right : SignedBinaryTree d),
      signedTreeValue (SignedBinaryTree.node x left right) =
        (if x then signedTreeValue right
         else -signedTreeValue left)) ∧
  (∀ k : Nat, ∀ tree : SignedBinaryTree k,
      internalNodeCount tree = 2 ^ k - 1 ∧
        (selectedPath tree).length = k ∧
        signedTreeValue tree = selectedPathSignProduct tree) ∧
  (∀ k : Nat, ∀ order : List (List Bool),
      bottomUpLayerOrder k order →
        (∀ q ∈ order, q ∈ internalPaths k) ∧
        (∀ tree : SignedBinaryTree k, ∀ continuation : List Nat,
          ∀ external,
            Sum.inr external ∈
                (querySchedule50494 order continuation).drop order.length →
              postDeterminationPacketRatio50496 k order
                (fullTranscript tree order) external = some 0))

/-- Claim 50496: the exact pre-query transcript, conditional path probability,
conditional correlation, zero-convention ratio, and post-determination zero
packets are retained for every valid arbitrary-within-layer order. -/
def preQueryNodePacketIdentities_claim50496 : Prop :=
  (∀ {k : Nat} (tree : SignedBinaryTree k)
      (order : List (List Bool)) (p : List Bool),
    1 ≤ k →
      bottomUpLayerOrder k order →
      preQueryNode k order p →
      let transcript := preQueryTranscript tree order p
      let pValue := conditionalPathProbability50496 k order p transcript
      let cValue := conditionalCorrelation50496 k order p transcript
      let r := p.length
      let leftValue := subtreeValue tree (p ++ [false])
      let rightValue := subtreeValue tree (p ++ [true])
      let ancestorSign := requiredAncestorProduct p
      pValue = 1 / (2 : ℚ) ^ r ∧
        cValue =
          (1 / (2 : ℚ) ^ r) * ancestorSign *
            (leftValue + rightValue) / 2 ∧
        packetRatio50496 pValue cValue =
          (1 / (2 : ℚ) ^ r) *
            (if leftValue = rightValue then (1 : ℚ) else 0)) ∧
  (∀ {k : Nat} (tree : SignedBinaryTree k)
      (order : List (List Bool)) (continuation : List Nat),
    bottomUpLayerOrder k order →
      functionDetermined50496 k order (fullTranscript tree order) ∧
      (∀ external,
        Sum.inr external ∈
            (querySchedule50494 order continuation).drop order.length →
          postDeterminationPathProbability50496 k order
              (fullTranscript tree order) external = some 0 ∧
            postDeterminationCorrelation50496 k order
              (fullTranscript tree order) external = some 0 ∧
            postDeterminationPacketRatio50496 k order
              (fullTranscript tree order) external = some 0))

/-- Claim 50497: the exact uniform independent-sign expectation over every
internal node is `(k+1)/2`, with deepest-layer contribution `1` and every
higher-layer contribution `1/2`, for each allowed bottom-up order. -/
def treePacketExpectation_claim50497 : Prop :=
  ∀ k : Nat, 1 ≤ k →
    ∀ order : List (List Bool), bottomUpLayerOrder k order →
      globalExpectation50497 k order = (k + 1 : ℚ) / 2 ∧
        layerExpectation50497 k order (k - 1) = 1 ∧
        (∀ d : Nat, d < k - 1 →
          layerExpectation50497 k order d = (1 : ℚ) / 2)

end
end MathlibPlus.Open.ResearchFormalization.R3861
