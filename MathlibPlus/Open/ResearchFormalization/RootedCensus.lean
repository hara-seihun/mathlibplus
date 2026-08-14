import Mathlib

open scoped BigOperators
open Finset
noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.RootedCensus

attribute [local instance] Classical.propDecidable Classical.decEq

/-- A finite rooted tree is represented by its unique parent map and a strictly
rank-decreasing parent certificate.  Its oriented edges are away from `root`. -/
structure RootedTree (n : ℕ) where
  parent : Fin n → Option (Fin n)
  root : Fin n
  rank : Fin n → ℕ
  root_parent : parent root = none
  parent_exists : ∀ v, v ≠ root → ∃ p, parent v = some p
  parent_rank : ∀ v p, parent v = some p → rank p < rank v

def treeAdj {n : ℕ} (R : RootedTree n) (u v : Fin n) : Prop :=
  R.parent u = some v ∨ R.parent v = some u

def descendant {n : ℕ} (R : RootedTree n) (z w : Fin n) : Prop :=
  Relation.ReflTransGen (fun a b => R.parent b = some a) z w

def fringe {n : ℕ} (R : RootedTree n) (z : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (descendant R z)

def connectedOn {n : ℕ} (R : RootedTree n) (F S : Finset (Fin n)) : Prop :=
  S.Nonempty ∧ ∀ u ∈ S, ∀ v ∈ S,
    Relation.ReflTransGen
      (fun a b => treeAdj R a b ∧ a ∈ F ∧ b ∈ F ∧ a ∈ S ∧ b ∈ S) u v

def boundary {n : ℕ} (R : RootedTree n)
    (F S : Finset (Fin n)) : ℕ :=
  S.sum fun v =>
    (Finset.univ.filter fun w => w ∈ F ∧ treeAdj R v w ∧ w ∉ S).card

def allSubsets (n : ℕ) : Finset (Finset (Fin n)) :=
  Finset.powerset (Finset.univ : Finset (Fin n))

abbrev UV := MvPolynomial (Fin 2) ℚ

private def uvar : UV := MvPolynomial.X 0
private def vvar : UV := MvPolynomial.X 1

/-- Rooted connected-subtree and avoiding-root censuses. -/
def rootedA {n : ℕ} (R : RootedTree n) (u v : UV) : UV :=
  ((allSubsets n).filter (fun S =>
    S.Nonempty ∧ R.root ∈ S ∧ connectedOn R (Finset.univ : Finset (Fin n)) S)).sum
    (fun S => u ^ (S.card - 1) * v ^ boundary R Finset.univ S)

def rootedAProper {n : ℕ} (R : RootedTree n) (u v : UV) : UV :=
  ((allSubsets n).filter (fun S =>
    S.card ≥ 2 ∧ R.root ∈ S ∧ connectedOn R (Finset.univ : Finset (Fin n)) S)).sum
    (fun S => u ^ (S.card - 1) * v ^ boundary R Finset.univ S)

def rootedE {n : ℕ} (R : RootedTree n) (u v : UV) : UV :=
  ((allSubsets n).filter (fun S =>
    S.Nonempty ∧ R.root ∉ S ∧ connectedOn R (Finset.univ : Finset (Fin n)) S)).sum
    (fun S => u ^ (S.card - 1) * v ^ boundary R Finset.univ S)

def rootedEProper {n : ℕ} (R : RootedTree n) (u v : UV) : UV :=
  ((allSubsets n).filter (fun S =>
    S.card ≥ 2 ∧ R.root ∉ S ∧ connectedOn R (Finset.univ : Finset (Fin n)) S)).sum
    (fun S => u ^ (S.card - 1) * v ^ boundary R Finset.univ S)

def fringeA {n : ℕ} (R : RootedTree n) (z : Fin n) (u v : UV) : UV :=
  let F := fringe R z
  ((allSubsets n).filter (fun S =>
    S.Nonempty ∧ z ∈ S ∧ S ⊆ F ∧ connectedOn R F S)).sum
    (fun S => u ^ (S.card - 1) * v ^ boundary R F S)

def fringeAProper {n : ℕ} (R : RootedTree n) (z : Fin n) (u v : UV) : UV :=
  let F := fringe R z
  ((allSubsets n).filter (fun S =>
    S.card ≥ 2 ∧ z ∈ S ∧ S ⊆ F ∧ connectedOn R F S)).sum
    (fun S => u ^ (S.card - 1) * v ^ boundary R F S)

abbrev FringeKey (n : ℕ) := Σ R : RootedTree n, Fin n

/-- The proper-fringe occurrence current retains the rooted presentation of a
fringe, rather than identifying equal vertex subsets from different trees. -/
def properFringeCurrent {n : ℕ} (R : RootedTree n) : FringeKey n →₀ ℚ :=
  (Finset.univ.erase R.root).sum fun z => Finsupp.single (Sigma.mk R z) 1

def fringeAOnCurrent {n : ℕ} (C : FringeKey n →₀ ℚ) (u v : UV) : UV :=
  C.sum fun k c => c • fringeA k.1 k.2 u v

def fringeAProperOnCurrent {n : ℕ} (C : FringeKey n →₀ ℚ) (u v : UV) : UV :=
  C.sum fun k c => c • fringeAProper k.1 k.2 u v

def packetA {n : ℕ} (W : RootedTree n →₀ ℚ) (u v : UV) : UV :=
  W.sum fun R c => c • rootedA R u v

def packetAProper {n : ℕ} (W : RootedTree n →₀ ℚ) (u v : UV) : UV :=
  W.sum fun R c => c • rootedAProper R u v

def packetE {n : ℕ} (W : RootedTree n →₀ ℚ) (u v : UV) : UV :=
  W.sum fun R c => c • rootedE R u v

def packetEProper {n : ℕ} (W : RootedTree n →₀ ℚ) (u v : UV) : UV :=
  W.sum fun R c => c • rootedEProper R u v

def packetFringe {n : ℕ} (W : RootedTree n →₀ ℚ) : FringeKey n →₀ ℚ :=
  W.sum fun R c => c • properFringeCurrent R

def rootedBOne {n : ℕ} (R : RootedTree n) : UV :=
  (((allSubsets n).filter (fun S =>
    S.card ≥ 2 ∧ R.root ∉ S ∧ connectedOn R (Finset.univ : Finset (Fin n)) S)).sum
    (fun S =>
      (uvar * vvar) ^ (S.card - 1) *
        (1 + uvar) ^ (n - S.card - boundary R Finset.univ S)))

def packetBOne {n : ℕ} (W : RootedTree n →₀ ℚ) : UV :=
  W.sum fun R c => c • rootedBOne R

abbrev FracUV := FractionRing UV

def uvSubstitution (p : UV) : FracUV :=
  MvPolynomial.eval₂Hom (algebraMap ℚ FracUV) (fun i =>
    if i = (0 : Fin 2) then
      algebraMap UV FracUV (MvPolynomial.X 0) *
          algebraMap UV FracUV (MvPolynomial.X 1) /
        algebraMap UV FracUV (1 + MvPolynomial.X 0)
    else
      1 / algebraMap UV FracUV (1 + MvPolynomial.X 0)) p

/-- Claim 50553: the four exact finite censuses and their rational packet
extensions are linear in the rooted packet. -/
def claim50553 : Prop :=
  ∀ {n : ℕ} (W W' : RootedTree n →₀ ℚ) (c : ℚ) (u v : UV),
    packetA (W + W') u v = packetA W u v + packetA W' u v ∧
    packetA (c • W) u v = c • (packetA W u v) ∧
    packetAProper (W + W') u v = packetAProper W u v + packetAProper W' u v ∧
    packetAProper (c • W) u v = c • (packetAProper W u v) ∧
    packetE (W + W') u v = packetE W u v + packetE W' u v ∧
    packetE (c • W) u v = c • (packetE W u v) ∧
    packetEProper (W + W') u v = packetEProper W u v + packetEProper W' u v ∧
    packetEProper (c • W) u v = c • (packetEProper W u v)

/-- Claim 50554: topmost-vertex decomposition and the extra parent boundary
edge, expressed by the exact census identity. -/
def claim50554 : Prop :=
  ∀ {n : ℕ} (R : RootedTree n),
    (∀ S : Finset (Fin n),
      S.Nonempty → R.root ∉ S → connectedOn R Finset.univ S →
        ∃! z, z ≠ R.root ∧ z ∈ S ∧ S ⊆ fringe R z) ∧
    rootedE R uvar vvar =
      vvar * fringeAOnCurrent (properFringeCurrent R) uvar vvar

/-- Claim 50555: the size-at-least-two restriction and the packet boundary
identities. -/
def claim50555 : Prop :=
  (∀ {n : ℕ} (R : RootedTree n),
    rootedEProper R uvar vvar =
      vvar * fringeAProperOnCurrent (properFringeCurrent R) uvar vvar) ∧
  (∀ {n : ℕ} (W : RootedTree n →₀ ℚ),
    packetE W uvar vvar = vvar * fringeAOnCurrent (packetFringe W) uvar vvar ∧
    packetEProper W uvar vvar = vvar * fringeAProperOnCurrent (packetFringe W) uvar vvar ∧
    packetFringe W = 0 → packetE W uvar vvar = 0 ∧ packetEProper W uvar vvar = 0)

/-- Claim 50556: the marked y=1 transform is the indicated rational
specialization of the proper-fringe avoiding census, and a closed fringe
current has zero aggregate marked face. -/
def claim50556 : Prop :=
  (∀ {d : ℕ} (R : RootedTree d),
    algebraMap UV FracUV (rootedBOne R) =
      algebraMap UV FracUV ((1 + uvar) ^ (d - 1)) *
        uvSubstitution (rootedEProper R uvar vvar)) ∧
  (∀ {d : ℕ} (W : RootedTree d →₀ ℚ),
    packetFringe W = 0 → packetBOne W = 0)

end MathlibPlus.Open.ResearchFormalization.RootedCensus
