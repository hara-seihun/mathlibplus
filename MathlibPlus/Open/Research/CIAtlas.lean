import Mathlib

namespace MathlibPlus.Open.Research.CIAtlas

abbrev C2CubedC9 := ZMod 2 × ZMod 2 × ZMod 2 × ZMod 9

def connectionSet72 (n : ℕ) (S : Finset C2CubedC9) : Prop :=
  S.card = n ∧ 0 ∉ S ∧ ∀ x, x ∈ S ↔ -x ∈ S

def graphDifference72 (x y : C2CubedC9) : C2CubedC9 := y - x

def autEquivalent72 (S T : Finset C2CubedC9) : Prop :=
  ∃ e : AddEquiv C2CubedC9 C2CubedC9,
    S.image (fun x => e x) = T

def graphEquivalent72 (S T : Finset C2CubedC9) : Prop :=
  ∃ e : Equiv C2CubedC9 C2CubedC9,
    ∀ x y, graphDifference72 x y ∈ S ↔
      graphDifference72 (e x) (e y) ∈ T

def graphAdjacent72 (S : Finset C2CubedC9) (x y : C2CubedC9) : Prop :=
  graphDifference72 x y ∈ S

def graphConnected72 (S : Finset C2CubedC9) : Prop :=
  ∀ x y, Relation.ReflTransGen (graphAdjacent72 S) x y

/-- Group order, automorphism order, and the 71 available nonidentity neighbors. -/
def claim27840 : Prop :=
  Fintype.card C2CubedC9 = 72 ∧
  Nat.card (AddEquiv C2CubedC9 C2CubedC9) = 1008 ∧
  Fintype.card {x : C2CubedC9 // x ≠ 0} = 71

/-- Exact number of inverse-closed connection sets of valency twelve. -/
def claim27841 : Prop :=
  Nat.card {S : Finset C2CubedC9 // connectionSet72 12 S} = 6428408

/-- Exact valency-twelve orbit/type census and equality of the two partitions. -/
def claim27842 : Prop :=
  ∃ autRepresentatives graphRepresentatives : Finset (Finset C2CubedC9),
    autRepresentatives.card = 16992 ∧
    graphRepresentatives.card = 16992 ∧
    (∀ T, T ∈ autRepresentatives → connectionSet72 12 T) ∧
    (∀ T, T ∈ graphRepresentatives → connectionSet72 12 T) ∧
    (∀ S, connectionSet72 12 S →
      ∃! T, T ∈ autRepresentatives ∧ connectionSet72 12 T ∧ autEquivalent72 S T) ∧
    (∀ S, connectionSet72 12 S →
      ∃! T, T ∈ graphRepresentatives ∧ connectionSet72 12 T ∧ graphEquivalent72 S T) ∧
    (∀ S T, connectionSet72 12 S → connectionSet72 12 T →
      (graphEquivalent72 S T ↔ autEquivalent72 S T))

/-- The valency-twelve undirected Cayley graphs satisfy the connection-set CI criterion. -/
def claim27844 : Prop :=
  ∀ S T : Finset C2CubedC9,
    connectionSet72 12 S → connectionSet72 12 T →
    graphEquivalent72 S T → autEquivalent72 S T

/-- Exact valency-thirteen orbit/type census and zero defect fibers. -/
def claim27854 : Prop :=
  ∃ autRepresentatives graphRepresentatives : Finset (Finset C2CubedC9),
    autRepresentatives.card = 35022 ∧
    graphRepresentatives.card = 35022 ∧
    (∀ T, T ∈ autRepresentatives → connectionSet72 13 T) ∧
    (∀ T, T ∈ graphRepresentatives → connectionSet72 13 T) ∧
    (∀ S, connectionSet72 13 S →
      ∃! T, T ∈ autRepresentatives ∧ connectionSet72 13 T ∧ autEquivalent72 S T) ∧
    (∀ S, connectionSet72 13 S →
      ∃! T, T ∈ graphRepresentatives ∧ connectionSet72 13 T ∧ graphEquivalent72 S T) ∧
    (∀ S T, connectionSet72 13 S → connectionSet72 13 T →
      (graphEquivalent72 S T ↔ autEquivalent72 S T))

/-- Exactly 33,244 connected ordinary graph types occur at valency thirteen. -/
def claim27855 : Prop :=
  ∃ representatives : Finset (Finset C2CubedC9),
    representatives.card = 33244 ∧
    (∀ T, T ∈ representatives →
      connectionSet72 13 T ∧ graphConnected72 T) ∧
    (∀ S, connectionSet72 13 S → graphConnected72 S →
      ∃! T, T ∈ representatives ∧ connectionSet72 13 T ∧
        graphConnected72 T ∧ graphEquivalent72 S T)

/-- The valency-thirteen undirected Cayley graphs are CI. -/
def claim27856 : Prop :=
  ∀ S T : Finset C2CubedC9,
    connectionSet72 13 S → connectionSet72 13 T →
    graphEquivalent72 S T → autEquivalent72 S T

def nonidentityC2CubedC9 : Finset C2CubedC9 :=
  (Finset.univ : Finset C2CubedC9).erase 0

def complementC2CubedC9 (S : Finset C2CubedC9) : Finset C2CubedC9 :=
  nonidentityC2CubedC9 \ S

/-- Complementation identifies valencies thirteen and fifty-eight and preserves CI. -/
def claim27858 : Prop :=
  (∀ S, connectionSet72 13 S →
    connectionSet72 58 (complementC2CubedC9 S) ∧
    (∀ T, connectionSet72 13 T →
      (graphEquivalent72 S T ↔
        graphEquivalent72 (complementC2CubedC9 S) (complementC2CubedC9 T)) ∧
      (autEquivalent72 S T ↔
        autEquivalent72 (complementC2CubedC9 S) (complementC2CubedC9 T)))) ∧
  (∀ S T, connectionSet72 58 S → connectionSet72 58 T →
    graphEquivalent72 S T → autEquivalent72 S T)

end MathlibPlus.Open.Research.CIAtlas
