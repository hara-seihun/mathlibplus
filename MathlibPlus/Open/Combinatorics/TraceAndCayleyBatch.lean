import Mathlib

namespace MathlibPlus.Open.Combinatorics.Claim3374

/-- The actual ground set of a finite family of finite sets. -/
def ground {n : ℕ} (F : Finset (Finset (Fin n))) : Finset (Fin n) :=
  F.biUnion (fun A => A)

/-- Membership frequency in a finite family. -/
def frequency {n : ℕ} (F : Finset (Finset (Fin n))) (x : Fin n) : ℕ :=
  (F.filter (fun A => x ∈ A)).card

/-- Union closure of a finite family. -/
def unionClosed {n : ℕ} (F : Finset (Finset (Fin n))) : Prop :=
  ∀ ⦃A B : Finset (Fin n)⦄, A ∈ F → B ∈ F → A ∪ B ∈ F

/-- A finite Frankl counterexample, with the actual finite ground set. -/
def franklCounterexample {n : ℕ} (F : Finset (Finset (Fin n))) : Prop :=
  1 < F.card ∧
    unionClosed F ∧
      ∀ x ∈ ground F, 2 * frequency F x < F.card

/-- Minimum cardinality is taken over all finite carriers, up to relabeling. -/
def minimumFranklCounterexample {n : ℕ} (F : Finset (Finset (Fin n))) : Prop :=
  franklCounterexample F ∧
    ∀ (m : ℕ) (G : Finset (Finset (Fin m))),
      franklCounterexample G → F.card ≤ G.card

/-- A member whose deletion preserves union closure. -/
def removable {n : ℕ} (F : Finset (Finset (Fin n))) (A : Finset (Fin n)) : Prop :=
  A ∈ F ∧ unionClosed (F.erase A)

/-- The tight coordinates, using the slack-one characterization. -/
def tightSet {n : ℕ} (F : Finset (Finset (Fin n))) : Finset (Fin n) :=
  (ground F).filter (fun x => 2 * frequency F x + 1 = F.card)

/-- Exactly-three tight coordinates force the stated trace conclusions. -/
def exactlyThreeTightTraceRestrictions : Prop :=
  ∀ (n : ℕ) (F : Finset (Finset (Fin n))),
    minimumFranklCounterexample F →
      (tightSet F).card = 3 →
        (∀ A, A ∈ F → removable F A → (A ∩ tightSet F).card ≤ 1) ∧
          (∀ x, x ∈ tightSet F →
            ∃ A, A ∈ F ∧ removable F A ∧ x ∈ A ∩ tightSet F) ∧
          (∀ x, x ∈ tightSet F →
            ∃ A, A ∈ F ∧ removable F A ∧ A ∩ tightSet F = ({x} : Finset (Fin n)))

end MathlibPlus.Open.Combinatorics.Claim3374

namespace MathlibPlus.Open.Combinatorics.Claim59784

/-- The explicitly presented semidirect product F₅² ⋊ C₂. -/
structure H where
  x : ZMod 5
  y : ZMod 5
  bit : Bool
deriving DecidableEq, Fintype

/-- Addition in the C₂ coordinate. -/
def bitAdd (a b : Bool) : Bool :=
  if a = b then false else true

/-- The semidirect-product multiplication, with the nonidentity bit acting by negation. -/
def mul (a b : H) : H :=
  { x := a.x + (if a.bit then -b.x else b.x)
    y := a.y + (if a.bit then -b.y else b.y)
    bit := bitAdd a.bit b.bit }

/-- The identity of the displayed semidirect product. -/
def one : H :=
  { x := 0, y := 0, bit := false }

/-- Inversion for the displayed semidirect product. -/
def inv (a : H) : H :=
  { x := if a.bit then a.x else -a.x
    y := if a.bit then a.y else -a.y
    bit := a.bit }

/-- Ordinary inverse-closed connection sets not containing the identity. -/
def connectionSet (S : Finset H) : Prop :=
  one ∉ S ∧ ∀ x, x ∈ S → inv x ∈ S

/-- Adjacency in the ordinary undirected Cayley graph on the displayed group. -/
def cayleyAdjacent (S : Finset H) (x y : H) : Prop :=
  x ≠ y ∧ ∃ s, s ∈ S ∧ y = mul x s

/-- Isomorphism of the two Cayley graphs. -/
def cayleyGraphIsomorphic (S T : Finset H) : Prop :=
  ∃ e : H ≃ H, ∀ x y, cayleyAdjacent S x y ↔ cayleyAdjacent T (e x) (e y)

/-- A group automorphism of the displayed semidirect-product operation. -/
def groupAutomorphism (e : H ≃ H) : Prop :=
  e one = one ∧ ∀ x y, e (mul x y) = mul (e x) (e y)

/-- An automorphism maps one connection set onto another. -/
def automorphismMaps (S T : Finset H) : Prop :=
  ∃ e : H ≃ H, groupAutomorphism e ∧ ∀ x, x ∈ S ↔ e x ∈ T

/-- Exact cardinality of the set of graph-isomorphism fibers at one valency. -/
def graphFiberCount (k n : ℕ) : Prop :=
  ∃ representatives : Finset (Finset H),
    representatives.card = n ∧
      (∀ C, C ∈ representatives → connectionSet C ∧ C.card = k) ∧
        (∀ S, connectionSet S → S.card = k →
          ∃! C, C ∈ representatives ∧ cayleyGraphIsomorphic S C)

/-- Exact cardinality of the Aut(H)-orbits at one valency. -/
def automorphismOrbitCount (k n : ℕ) : Prop :=
  ∃ representatives : Finset (Finset H),
    representatives.card = n ∧
      (∀ C, C ∈ representatives → connectionSet C ∧ C.card = k) ∧
        (∀ S, connectionSet S → S.card = k →
          ∃! C, C ∈ representatives ∧ automorphismMaps S C)

/-- CI through valency six, together with both asserted enumerators. -/
def ciThroughSix : Prop :=
  (∀ S T, connectionSet S → connectionSet T →
    S.card ≤ 6 → T.card ≤ 6 →
      (cayleyGraphIsomorphic S T ↔ automorphismMaps S T)) ∧
    graphFiberCount 0 1 ∧ automorphismOrbitCount 0 1 ∧
    graphFiberCount 1 1 ∧ automorphismOrbitCount 1 1 ∧
    graphFiberCount 2 2 ∧ automorphismOrbitCount 2 2 ∧
    graphFiberCount 3 3 ∧ automorphismOrbitCount 3 3 ∧
    graphFiberCount 4 10 ∧ automorphismOrbitCount 4 10 ∧
    graphFiberCount 5 20 ∧ automorphismOrbitCount 5 20 ∧
    graphFiberCount 6 61 ∧ automorphismOrbitCount 6 61

end MathlibPlus.Open.Combinatorics.Claim59784
