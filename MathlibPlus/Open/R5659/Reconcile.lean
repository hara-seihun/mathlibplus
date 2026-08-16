import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.R5659

noncomputable section
open Classical

/-- The component partitions used by the partition-lattice transform. -/
def IsComponentPartition (parts : List ℕ) : Prop :=
  parts ≠ [] ∧
    (∀ n ∈ parts, 0 < n) ∧
    parts.Pairwise (· ≥ ·)

/-- A finite set partition, represented by its nonempty, disjoint blocks. -/
def IsSetPartition {α : Type} [Fintype α] [DecidableEq α]
    (π : Finset (Finset α)) : Prop :=
  (∀ B ∈ π, B.Nonempty) ∧
    (∀ a, ∃ B, B ∈ π ∧ a ∈ B) ∧
    (∀ B ∈ π, ∀ C ∈ π, B ≠ C → Disjoint B C)

def blockSum (parts : List ℕ) (B : Finset (Fin parts.length)) : ℕ :=
  ∑ i ∈ B, parts.get i

def componentExponent (parts : List ℕ) : ℕ →₀ ℕ :=
  ∑ i : Fin parts.length, Finsupp.single (parts.get i) 1

def xMonomial (parts : List ℕ) : MvPolynomial ℕ ℚ :=
  MvPolynomial.monomial (componentExponent parts) 1

/-- The cumulant formula from the finite partition lattice over `ℚ`. -/
def partitionLatticeCumulant (parts : List ℕ) : MvPolynomial ℕ ℚ :=
  ∑ π : Finset (Finset (Fin parts.length)),
    if IsSetPartition π then
      ((-1 : ℚ) ^ (π.card - 1) * Nat.factorial (π.card - 1)) •
        (∏ B ∈ π, MvPolynomial.X (blockSum parts B))
    else 0

def monomialDegree (d : ℕ →₀ ℕ) : ℕ :=
  d.sum (fun _ exponent => exponent)

def IsTriangularByNumberOfParts (parts : List ℕ) : Prop :=
  (∀ d ∈ (partitionLatticeCumulant parts).support,
      monomialDegree d ≤ parts.length) ∧
    MvPolynomial.coeff (componentExponent parts) (partitionLatticeCumulant parts) =
      ((-1 : ℚ) ^ (parts.length - 1) * Nat.factorial (parts.length - 1)) ∧
    MvPolynomial.coeff (componentExponent parts) (partitionLatticeCumulant parts) ≠ 0

/-- Claim 60783. -/
def claim60783 : Prop :=
  ∀ parts : List ℕ, IsComponentPartition parts → IsTriangularByNumberOfParts parts


def lineAdjacent {n : ℕ} (s : Finset (Fin n))
    (u v : Fin (n + 1)) : Prop :=
  ∃ i : Fin n, i ∈ s ∧
    ((u = i.castSucc ∧ v = i.succ) ∨
      (u = i.succ ∧ v = i.castSucc))

def lineComponent {n : ℕ} (s : Finset (Fin n))
    (v : Fin (n + 1)) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun w => Relation.ReflTransGen (lineAdjacent s) v w)

def lineComponents {n : ℕ} (s : Finset (Fin n)) :
    Finset (Finset (Fin (n + 1))) :=
  Finset.univ.image (lineComponent s)

def lineComponentSizePartition {n : ℕ} (s : Finset (Fin n)) : Multiset ℕ :=
  (lineComponents s).val.map Finset.card

def centralEdge : Fin 11 := 5

def maskEdges (mask : ℕ) : Finset (Fin 11) :=
  Finset.univ.filter (fun i => mask.testBit i.val = true)

def partition6411 : Multiset ℕ :=
  Multiset.ofList [6, 4, 1, 1]

def partition5411 : Multiset ℕ :=
  Multiset.ofList [5, 4, 1, 1]

def hasComponentLargerThanSix (s : Finset (Fin 11)) : Prop :=
  ∃ C ∈ lineComponents s, 6 < C.card

def contractedEdgeIndex : Fin 11 → Fin 10 :=
  Fin.predAbove (5 : Fin 10)

def contractedMask (s : Finset (Fin 11)) : Finset (Fin 10) :=
  (s.erase centralEdge).image contractedEdgeIndex

def contractedComponentSizePartition (s : Finset (Fin 11)) : Multiset ℕ :=
  lineComponentSizePartition (contractedMask s)

/-- Claim 60786. -/
def claim60786 : Prop :=
  Fintype.card (Finset (Fin 11)) = 2 ^ 11 ∧
    2 ^ 11 = 2048 ∧
    (∀ s : Finset (Fin 11), centralEdge ∉ s →
      ¬ hasComponentLargerThanSix s) ∧
    (Finset.univ.filter (fun s : Finset (Fin 11) =>
      centralEdge ∈ s ∧ hasComponentLargerThanSix s)).card = 112 ∧
    (Finset.univ.filter (fun s : Finset (Fin 11) =>
      centralEdge ∈ s ∧ lineComponentSizePartition s = partition6411)).card = 6 ∧
    (Finset.univ.filter (fun s : Finset (Fin 11) =>
      centralEdge ∉ s ∧ lineComponentSizePartition s = partition6411)).card = 6 ∧
    centralEdge ∈ maskEdges 503 ∧
    centralEdge ∉ maskEdges 479 ∧
    lineComponentSizePartition (maskEdges 503) = partition6411 ∧
    lineComponentSizePartition (maskEdges 479) = partition6411 ∧
    (∀ s : Finset (Fin 11), centralEdge ∈ s →
      lineComponentSizePartition s = partition6411 →
      contractedComponentSizePartition s = partition5411) ∧
    contractedComponentSizePartition (maskEdges 503) = partition5411

end
end MathlibPlus.Open.R5659
