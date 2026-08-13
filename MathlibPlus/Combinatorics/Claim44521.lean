import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Fintype.Quotient

namespace MathlibPlus.Combinatorics.Claim44521

/-- Labeled simple graphs on the canonical `n`-vertex set. -/
def labeledGraph (n : ℕ) := SimpleGraph (Fin n)

/-- Two labeled graphs represent the same unlabeled graph when a graph
isomorphism identifies their vertex sets. -/
def graphIsomorphic (n : ℕ) (G H : labeledGraph n) : Prop :=
  Nonempty (G ≃g H)

noncomputable def graphIsoSetoid (n : ℕ) : Setoid (labeledGraph n) where
  r := graphIsomorphic n
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro G
      exact ⟨SimpleGraph.Iso.refl⟩
    · intro G H h
      exact ⟨h.some.symm⟩
    · intro G H K hGH hHK
      exact ⟨hGH.some.trans hHK.some⟩

/-- The exact isomorphism classes of simple graphs with `n` vertices. -/
def finiteSimpleGraphType (n : ℕ) := Quotient (graphIsoSetoid n)

noncomputable instance finiteSimpleGraphType.fintype (n : ℕ) :
    Fintype (finiteSimpleGraphType n) := by
  letI : Fintype (SimpleGraph (Fin n)) := inferInstance
  letI : Finite (labeledGraph n) :=
    Fintype.finite (inferInstance : Fintype (SimpleGraph (Fin n)))
  exact @Fintype.ofFinite _ (Quotient.finite (graphIsoSetoid n))

/-- The graph-isomorphism class represented by a labeled graph. -/
noncomputable def graphTypeOf (n : ℕ) (G : labeledGraph n) : finiteSimpleGraphType n :=
  Quotient.mk (graphIsoSetoid n) G

/-- The finitely supported rational span of graph types. -/
def rationalGraphSpace (n : ℕ) := finiteSimpleGraphType n →₀ ℚ

/-- The finitely supported basis vector attached to a graph type. -/
noncomputable def graphTypeBasis (n : ℕ) (G : labeledGraph n) : rationalGraphSpace n :=
  Finsupp.single (graphTypeOf n G) 1

/-- Claim 44521's exact carrier is finite for every vertex count. -/
theorem finiteSimpleGraphType_isFinite_claim44521 (n : ℕ) :
    Finite (finiteSimpleGraphType n) := by
  infer_instance

/-- Each graph-type basis vector has finite support, as required by the rational
span carrier; no finite census or hash canonicalization enters the identity. -/
theorem graphTypeBasis_support_claim44521 (n : ℕ) (G : labeledGraph n) :
    (graphTypeBasis n G).support = {graphTypeOf n G} := by
  simp [graphTypeBasis]

end MathlibPlus.Combinatorics.Claim44521
