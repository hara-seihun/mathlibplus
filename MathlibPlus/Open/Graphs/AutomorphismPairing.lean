import Mathlib

namespace MathlibPlus.Open.Graphs

open scoped BigOperators
noncomputable section

/-- A simple graph whose vertex set is the finite set `Fin n`. -/
structure FiniteSimpleGraph (n : ℕ) where
  adjacent : Fin n → Fin n → Prop
  symmetric : ∀ {u v}, adjacent u v → adjacent v u
  loopless : ∀ u, ¬ adjacent u u

/-- An isomorphism between two finite simple graphs on the same vertex set. -/
def graphIsomorphic {n : ℕ} (G H : FiniteSimpleGraph n) : Prop :=
  ∃ e : Equiv.Perm (Fin n),
    ∀ u v, G.adjacent u v ↔ H.adjacent (e u) (e v)

private theorem graphIsomorphic_refl {n : ℕ} (G : FiniteSimpleGraph n) :
    graphIsomorphic G G := by
  exact ⟨Equiv.refl _, fun _ _ => Iff.rfl⟩

private theorem graphIsomorphic_symm {n : ℕ} {G H : FiniteSimpleGraph n} :
    graphIsomorphic G H → graphIsomorphic H G := by
  rintro ⟨e, h⟩
  refine ⟨e.symm, ?_⟩
  intro u v
  simpa using (h (e.symm u) (e.symm v)).symm

private theorem graphIsomorphic_trans {n : ℕ} {G H K : FiniteSimpleGraph n} :
    graphIsomorphic G H → graphIsomorphic H K → graphIsomorphic G K := by
  rintro ⟨e, h⟩ ⟨f, k⟩
  refine ⟨e.trans f, ?_⟩
  intro u v
  exact (h u v).trans (k (e u) (e v))

def finiteSimpleGraphSetoid (n : ℕ) : Setoid (FiniteSimpleGraph n) where
  r := graphIsomorphic
  iseqv := ⟨graphIsomorphic_refl, graphIsomorphic_symm, graphIsomorphic_trans⟩

/-- The isomorphism classes of simple graphs on `n` vertices. -/
def GraphClass (n : ℕ) := Quotient (finiteSimpleGraphSetoid n)

/-- The automorphism permutations of a representative finite simple graph. -/
def GraphAutomorphism {n : ℕ} (G : FiniteSimpleGraph n) :=
  {e : Equiv.Perm (Fin n) // ∀ u v, G.adjacent u v ↔ G.adjacent (e u) (e v)}

noncomputable instance graphAutomorphismFintype {n : ℕ} (G : FiniteSimpleGraph n) :
    Fintype (GraphAutomorphism G) := by
  classical
  refine Fintype.subtype
    (Finset.univ.filter fun e : Equiv.Perm (Fin n) =>
      ∀ u v, G.adjacent u v ↔ G.adjacent (e u) (e v)) ?_
  intro e
  simp

/-- The automorphism-group cardinality of an isomorphism class. -/
noncomputable def graphAutCard {n : ℕ} (G : GraphClass n) : ℕ :=
  Fintype.card (GraphAutomorphism (Quotient.out G))

abbrev GraphVector (n : ℕ) := GraphClass n →₀ ℚ

noncomputable def graphBasisPairing {n : ℕ} (G H : GraphClass n) : ℚ := by
  classical
  exact if G = H then (graphAutCard G : ℚ) else 0

/-- The bilinear extension of the automorphism-weighted basis pairing. -/
noncomputable def automorphismWeightedGraphPairing {n : ℕ}
    (v w : GraphVector n) : ℚ :=
  ∑ G ∈ v.support, ∑ H ∈ w.support,
    v G * w H * graphBasisPairing G H

/--
The automorphism-weighted graph pairing on the free rational vector space on
isomorphism classes of simple `n`-vertex graphs has the prescribed basis values.
The displayed finite-support sum is its bilinear extension.
-/
def automorphismWeightedGraphPairingClaim (n : ℕ) : Prop := by
  classical
  exact ∀ G H : GraphClass n,
    automorphismWeightedGraphPairing (Finsupp.single G 1) (Finsupp.single H 1) =
      if G = H then (graphAutCard G : ℚ) else 0

end

end MathlibPlus.Open.Graphs
