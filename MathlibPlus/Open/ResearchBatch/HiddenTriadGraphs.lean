import Mathlib

namespace MathlibPlus.Open.ResearchBatch.HiddenTriadGraphs

/-- The concrete four binary sections in the rank-three hidden-triad carrier.
The carrier is the displayed product `C₂^3 × C₉`. -/
abbrev HiddenTriadCarrier := (ZMod 2 × ZMod 2 × ZMod 2) × ZMod 9

def hiddenSection₀ : Finset (ZMod 9) := {3, 6}
def hiddenSection₁ : Finset (ZMod 9) := {3, 6}
def hiddenSection₂ : Finset (ZMod 9) := {2, 4, 5, 7}
def hiddenSection₃ : Finset (ZMod 9) := {0, 2, 4, 5, 7}

def hiddenSection (u : ZMod 2 × ZMod 2) : Finset (ZMod 9) :=
  if u = (0, 0) then hiddenSection₀
  else if u = (1, 0) then hiddenSection₁
  else if u = (0, 1) then hiddenSection₂
  else hiddenSection₃

def hiddenTriadBase : Finset HiddenTriadCarrier :=
  (Finset.univ : Finset (ZMod 2 × ZMod 2)).biUnion (fun u =>
    (Finset.univ : Finset (ZMod 2)).biUnion (fun t =>
      (hiddenSection u).image (fun c =>
        ((u.1, u.2, t), c))))

def hiddenTriadE₃ : HiddenTriadCarrier :=
  ((0, 0, 1), 0)

def hiddenTriadConnection : Finset HiddenTriadCarrier :=
  hiddenTriadBase ∪ {hiddenTriadE₃}

/-- The displayed sections and the additional binary involution have the
reported cardinality. -/
def hidden_triad_connection_claim : Prop :=
  hiddenTriadConnection.card = 27

abbrev Rank := {r : ℕ // r = 4 ∨ r = 5}

def rankDimension (r : Rank) : ℕ := r.1 - 3

abbrev RankCarrier (r : Rank) :=
  HiddenTriadCarrier × (Fin (rankDimension r) → ZMod 2)

def cubeBasis (d : ℕ) (i : Fin d) : Fin d → ZMod 2 :=
  fun j => if i = j then 1 else 0

def rankConnection (r : Rank) : Finset (RankCarrier r) :=
  hiddenTriadConnection.image (fun h => (h, (0 : Fin (rankDimension r) → ZMod 2))) ∪
    (Finset.univ : Finset (Fin (rankDimension r))).image (fun i =>
      (0, cubeBasis (rankDimension r) i))

def rankAdjacency (r : Rank) (x y : RankCarrier r) : Prop :=
  y - x ∈ rankConnection r

def rankConnected (r : Rank) : Prop :=
  ∀ x y, Relation.ReflTransGen (rankAdjacency r) x y

/-- The Cartesian Cayley lifts have the stated finite carriers, symmetry,
connectivity, and valencies. -/
def cartesian_lift_graph_claim : Prop :=
  ∀ r : Rank,
    Fintype.card (RankCarrier r) = (if r.1 = 4 then 144 else 288) ∧
    (∀ x, ¬ rankAdjacency r x x) ∧
    (∀ x y, rankAdjacency r x y ↔ rankAdjacency r y x) ∧
    rankConnected r ∧
    (rankConnection r).card = (if r.1 = 4 then 28 else 29)

end MathlibPlus.Open.ResearchBatch.HiddenTriadGraphs
