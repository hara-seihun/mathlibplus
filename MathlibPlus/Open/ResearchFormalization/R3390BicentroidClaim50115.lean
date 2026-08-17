import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R3390

open scoped BigOperators

noncomputable section

/-- An occurrence presentation of a finite rooted tree; rooted-type counts use
`rootedCode`, so child-list order does not create a second rooted type. -/
inductive RootedTree where
  | node (children : List RootedTree)

attribute [local instance] Classical.decEq

def node (children : List RootedTree) : RootedTree :=
  .node children

namespace RootedTree

def order : RootedTree → ℕ
  | .node children => 1 + children.foldr (fun child n => order child + n) 0

def rootedCode : RootedTree → List ℕ
  | .node children =>
      0 :: ((children.map rootedCode).mergeSort).flatten ++ [1]

def leaf : RootedTree := .node []

def addRootLeaf : RootedTree → RootedTree
  | .node children => .node (leaf :: children)

def addRootLeafN : ℕ → RootedTree → RootedTree
  | 0, R => R
  | n + 1, R => addRootLeafN n (addRootLeaf R)

def children : RootedTree → List RootedTree
  | .node branches => branches
end RootedTree

/-- The component containing the distinguished root and the residual
component-size partition left outside it. -/
structure BoundaryState where
  openSize : ℕ
  residual : List ℕ

mutual
  def internalStates : RootedTree → List BoundaryState
    | .node children =>
        foldChildren children [{ openSize := 1, residual := [] }]
  def foldChildren : List RootedTree → List BoundaryState → List BoundaryState
    | [], states => states
    | child :: children, states =>
        foldChildren children <|
          states.flatMap (fun state =>
            (internalStates child).flatMap (fun childState =>
              [ { openSize := state.openSize + childState.openSize
                  residual := state.residual ++ childState.residual }
              , { openSize := state.openSize
                  residual := childState.openSize ::
                    (state.residual ++ childState.residual) }
              ]))
end

abbrev ComponentPolynomial := MvPolynomial ℕ ℤ
abbrev BoundaryPolynomial := Polynomial ComponentPolynomial

def componentVariable (n : ℕ) : ComponentPolynomial :=
  MvPolynomial.X n

def componentMonomial (parts : List ℕ) : ComponentPolynomial :=
  parts.foldr (fun n p => componentVariable n * p) 1

/-- The complete rooted boundary factor: the outer polynomial variable records
an open component, while `x_n` records a closed component of order `n`. -/
def genuineRootedFactor (R : RootedTree) : BoundaryPolynomial :=
  (internalStates R).foldr (fun state p =>
    ((Polynomial.X : BoundaryPolynomial) ^ state.openSize +
      Polynomial.C (componentVariable state.openSize)) *
        Polynomial.C (componentMonomial state.residual) + p) 0

def rootedFactorProduct (branches : List RootedTree) : BoundaryPolynomial :=
  (branches.map genuineRootedFactor).prod

/-- The selector `Phi(z^r Q)=x_r Q` used in the bicentroid two-sector formula. -/
def componentSelector (P : BoundaryPolynomial) : ComponentPolynomial :=
  (Finset.range (P.natDegree + 1)).sum (fun n =>
    componentVariable n * P.coeff n)

/-- The ordinary bicentroid `U` polynomial obtained from the two rooted halves:
the first summand omits the central edge and the second selects it. -/
def bicentroidUPolynomial
    (A B : List RootedTree) : ComponentPolynomial :=
  componentSelector ((Polynomial.X : BoundaryPolynomial) * rootedFactorProduct A) *
      componentSelector ((Polynomial.X : BoundaryPolynomial) * rootedFactorProduct B) +
    componentSelector ((Polynomial.X : BoundaryPolynomial) ^ 2 *
      rootedFactorProduct A * rootedFactorProduct B)

/-- A bicentroid parent is the pair of rooted halves joined by its central
edge. The central edge is implicit in this two-half carrier. -/
structure BicentroidParent where
  leftHalf : RootedTree
  rightHalf : RootedTree

def biNode (A B : RootedTree) : BicentroidParent :=
  { leftHalf := A, rightHalf := B }

def isBicentroidParent (h : ℕ) (T : BicentroidParent) : Prop :=
  RootedTree.order T.leftHalf = h ∧ RootedTree.order T.rightHalf = h

def totalOffCore (T : BicentroidParent) : List RootedTree :=
  RootedTree.children T.leftHalf ++ RootedTree.children T.rightHalf

def parentUPolynomial (T : BicentroidParent) : ComponentPolynomial :=
  bicentroidUPolynomial (RootedTree.children T.leftHalf)
    (RootedTree.children T.rightHalf)

def occurrenceCount (branches : List RootedTree) (R : RootedTree) : ℤ :=
  (branches.map (fun S =>
    if RootedTree.rootedCode S = RootedTree.rootedCode R then
      (1 : ℤ) else 0)).sum

abbrev Packet := RootedTree → ℤ

def packetFromTerms (terms : List (RootedTree × ℤ)) : Packet :=
  fun R => (terms.map (fun term =>
    if RootedTree.rootedCode term.1 = RootedTree.rootedCode R then
      term.2 else 0)).sum

def packetAdd (W V : Packet) : Packet := fun R => W R + V R
def packetScale (a : ℤ) (W : Packet) : Packet := fun R => a * W R
def zeroPacket : Packet := fun _ => 0

def packetAtOrder (d : ℕ) (M M' : List RootedTree) : Packet :=
  fun R => if RootedTree.order R = d then
    occurrenceCount M R - occurrenceCount M' R else 0

/-- `d` is the maximum differing rooted order and `W` is its signed total
off-core multiplicity packet. -/
def packetIsMaximum
    (d : ℕ) (M M' : List RootedTree) (W : Packet) : Prop :=
  (∀ R : RootedTree, d < RootedTree.order R →
    occurrenceCount M R = occurrenceCount M' R) ∧
  (∃ R : RootedTree, RootedTree.order R = d ∧
    occurrenceCount M R ≠ occurrenceCount M' R) ∧
  (∀ R : RootedTree, W R = packetAtOrder d M M' R)

/-- The two source-listed support-eight order-seven basis packets. -/
def a₁ : RootedTree :=
  node [node [node [node [node []]]], node [node []]]
def a₂ : RootedTree :=
  node [node [node [node [node []]]], node [], node []]
def a₃ : RootedTree :=
  node [node [node [node []], node []], node [node []]]
def a₄ : RootedTree :=
  node [node [node [node []], node []], node [], node []]
def a₅ : RootedTree :=
  node [node [node [node []]], node [node [node []]]]
def a₆ : RootedTree :=
  node [node [node [node []]], node [node [], node []]]
def a₇ : RootedTree :=
  node [node [node [node []]], node [node []], node []]
def a₈ : RootedTree :=
  node [node [node [], node []], node [node []], node []]

def b₁ : RootedTree :=
  node [node [node [node [], node []]], node [node []]]
def b₂ : RootedTree :=
  node [node [node [node [], node []]], node [], node []]
def b₃ : RootedTree :=
  node [node [node [node []]], node [node [], node []]]
def b₄ : RootedTree :=
  node [node [node [node []]], node [], node [], node []]
def b₅ : RootedTree :=
  node [node [node [], node [], node []], node [node []]]
def b₆ : RootedTree :=
  node [node [node [], node [], node []], node [], node []]
def b₇ : RootedTree :=
  node [node [node [], node []], node [node [], node []]]
def b₈ : RootedTree :=
  node [node [node [], node []], node [], node [], node []]

def firstClosedCurrentATerms : List (RootedTree × ℤ) :=
  [(a₁, 1), (a₂, -1), (a₃, -1), (a₄, 1),
    (a₅, -1), (a₆, 1), (a₇, 1), (a₈, -1)]
def firstClosedCurrentBTerms : List (RootedTree × ℤ) :=
  [(b₁, 1), (b₂, -1), (b₃, -1), (b₄, 1),
    (b₅, -1), (b₆, 1), (b₇, 1), (b₈, -1)]
def firstClosedCurrentA : Packet :=
  packetFromTerms firstClosedCurrentATerms
def firstClosedCurrentB : Packet :=
  packetFromTerms firstClosedCurrentBTerms

def liftTerms (d : ℕ) (terms : List (RootedTree × ℤ)) : List (RootedTree × ℤ) :=
  terms.map (fun term =>
    (RootedTree.addRootLeafN (d - 7) term.1, term.2))
def liftedCurrentA (d : ℕ) : Packet :=
  packetFromTerms (liftTerms d firstClosedCurrentATerms)
def liftedCurrentB (d : ℕ) : Packet :=
  packetFromTerms (liftTerms d firstClosedCurrentBTerms)

/-- Claim 50115: an equal-ordinary-`U` bicentroid pair cannot have a nonzero
maximum total off-core packet in the lifted first closed-current plane. -/
def claim50115 : Prop :=
  ∀ (h d : ℕ) (T T' : BicentroidParent) (a b : ℤ),
    isBicentroidParent h T →
    isBicentroidParent h T' →
    7 ≤ d →
    parentUPolynomial T = parentUPolynomial T' →
    let M := totalOffCore T
    let M' := totalOffCore T'
    let W := packetAtOrder d M M'
    packetIsMaximum d M M' W →
    W = packetAdd (packetScale a (liftedCurrentA d))
          (packetScale b (liftedCurrentB d)) →
    W ≠ zeroPacket → False

end
end MathlibPlus.Open.ResearchFormalization.R3390
