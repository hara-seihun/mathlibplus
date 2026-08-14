import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-!
  A concrete finite simple-graph edge-set carrier for the support and
  symmetric-difference claims in the lease packet.  An edge is a two-element
  subset of `Fin n`, and an edge set is a finite set of such edges.
-/

abbrev Vertex (n : ℕ) := Fin n

abbrev Edge (n : ℕ) := {e : Finset (Vertex n) // e.card = 2}

abbrev EdgeSet (n : ℕ) := Finset (Edge n)

noncomputable instance edgeFintype (n : ℕ) : Fintype (Edge n) := Fintype.ofFinite _

def support {n : ℕ} (A : EdgeSet n) : Finset (Vertex n) :=
  A.biUnion (fun e => e.1)

def isolateCount {n : ℕ} (A : EdgeSet n) : ℕ :=
  n - (support A).card

def IsIsolated {n : ℕ} (A : EdgeSet n) (v : Vertex n) : Prop :=
  v ∉ support A

def IsSpanning {n : ℕ} (A : EdgeSet n) : Prop :=
  support A = Finset.univ

def xorEdges {n : ℕ} (A B : EdgeSet n) : EdgeSet n :=
  (A \ B) ∪ (B \ A)

def supportOverlap {n : ℕ} (A B : EdgeSet n) : ℕ :=
  (support A).card + (support B).card - n

def edgePresent {n : ℕ} (A : EdgeSet n) (u v : Vertex n) : Prop :=
  ∃ e, e ∈ A ∧ u ∈ e.1 ∧ v ∈ e.1

def edgeMissing {n : ℕ} (A : EdgeSet n) (u v : Vertex n) : Prop :=
  u ≠ v ∧ ¬ edgePresent A u v

noncomputable def completeEdgeSet (n : ℕ) : EdgeSet n :=
  Finset.univ

noncomputable def complement {n : ℕ} (C : EdgeSet n) : EdgeSet n :=
  completeEdgeSet n \ C

def IsMatching {n : ℕ} (M : EdgeSet n) : Prop :=
  ∀ ⦃e₁ e₂ : Edge n⦄,
    e₁ ∈ M → e₂ ∈ M → e₁ ≠ e₂ →
    ∀ v : Vertex n, v ∈ e₁.1 → v ∈ e₂.1 → False

def cStar {n : ℕ} (C : EdgeSet n) (v : Vertex n) : EdgeSet n :=
  C.filter (fun e => v ∈ e.1)

def LowOverlapFactorization {n : ℕ} (A B : EdgeSet n) : Prop :=
  IsSpanning (xorEdges A B) ∧
  0 < isolateCount A ∧
  0 < isolateCount B ∧
  (2 ≤ isolateCount A ∨ 2 ≤ isolateCount B)

/-- Claim 21241. -/
def supportIsolatesAndOverlapFiltration : Prop :=
  (∀ (n : ℕ) (A : EdgeSet n) (v : Vertex n),
    v ∈ support A ↔ ∃ e, e ∈ A ∧ v ∈ e.1) ∧
  (∀ (n : ℕ) (A : EdgeSet n),
    isolateCount A = n - (support A).card) ∧
  (∀ (n : ℕ) (A B : EdgeSet n),
    IsSpanning (xorEdges A B) →
      supportOverlap A B = (support A).card + (support B).card - n) ∧
  (∀ (n : ℕ) (A B : EdgeSet n),
    LowOverlapFactorization A B ↔
      IsSpanning (xorEdges A B) ∧
      0 < isolateCount A ∧
      0 < isolateCount B ∧
      (2 ≤ isolateCount A ∨ 2 ≤ isolateCount B))

/-- Claim 21242. -/
def lowOverlapBound : Prop :=
  ∀ (n : ℕ) (A B : EdgeSet n),
    IsSpanning (xorEdges A B) →
    0 < isolateCount A →
    0 < isolateCount B →
    (2 ≤ isolateCount A ∨ 2 ≤ isolateCount B) →
    supportOverlap A B ≤ n - 3

/-- Claim 21243. -/
def adjacentComplementWedgeFactorization : Prop :=
  ∀ (n : ℕ) (C : EdgeSet n),
    IsSpanning C →
    ∀ (u v w : Vertex n),
      u ≠ v → v ≠ w → u ≠ w →
      edgeMissing C u v →
      edgeMissing C v w →
      let A := cStar C v
      let B := xorEdges C A
      IsIsolated A u ∧
      IsIsolated A w ∧
      IsIsolated B v ∧
      xorEdges A B = C

/-- Claim 21244. -/
def matchingComplementFactorizationRigidity : Prop :=
  ∀ (n : ℕ) (M A B : EdgeSet n) (u v : Vertex n),
    IsMatching M →
    let C := complement M
    xorEdges A B = C →
    IsIsolated A u →
    IsIsolated B v →
    u ≠ v ∧
    edgePresent M u v ∧
    (∀ w : Vertex n, w ≠ u → w ≠ v →
      w ∈ support A ∧ w ∈ support B) ∧
    support A = Finset.univ.erase u ∧
    support B = Finset.univ.erase v ∧
    isolateCount A = 1 ∧
    isolateCount B = 1

/-- Claim 21245. -/
def exactSupportClassification : Prop :=
  ∀ (n : ℕ) (C : EdgeSet n),
    IsSpanning C →
    ((∃ A B : EdgeSet n,
        xorEdges A B = C ∧
        0 < isolateCount A ∧
        0 < isolateCount B ∧
        (2 ≤ isolateCount A ∨ 2 ≤ isolateCount B)) ↔
      ¬ IsMatching (complement C))

/-- Claim 21961. -/
def exactNumberOfOuterCoprimePairs : Prop :=
  let P : ℕ := 32768
  let pairs := (Finset.Icc 0 P).product (Finset.Icc 0 P)
  (pairs.filter (fun pq : ℕ × ℕ =>
    7 * P / 8 ≤ pq.2 ∧
    pq.2 ≤ pq.1 ∧
    pq.1 ≤ P ∧
    Nat.Coprime pq.1 pq.2)).card = 5_101_506

end MathlibPlus.Open.ResearchFormalization
