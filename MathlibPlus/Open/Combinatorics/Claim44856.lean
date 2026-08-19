import Mathlib

open scoped BigOperators
open BigOperators
open Classical

namespace MathlibPlus.Open.Combinatorics

noncomputable section

/-- The undirected adjacency relation underlying a finite oriented occurrence
graph. -/
def occurrenceAdjacency44856
    {V E : Type*} (source target : E → V) (u v : V) : Prop :=
  (∃ e, source e = u ∧ target e = v) ∨
    (∃ e, source e = v ∧ target e = u)

/-- A finite vertex set is one connected component of the occurrence graph. -/
def occurrenceComponent44856
    {V E : Type*} [Fintype V] [DecidableEq V]
    (source target : E → V) (C : Finset V) : Prop :=
  C.Nonempty ∧
    ∀ x ∈ C, ∀ y : V,
      Relation.ReflTransGen (occurrenceAdjacency44856 source target) x y ↔
        y ∈ C

def integralEdgeBoundary44856
    {V E : Type*} [Fintype E] [DecidableEq V]
    (source target : E → V) (flow : E → ℤ) (v : V) : ℤ :=
  (∑ e : E, if target e = v then flow e else 0) -
    ∑ e : E, if source e = v then flow e else 0

def isIntegralEdgeBoundary44856
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (source target : E → V) (chain : V → ℤ) : Prop :=
  ∃ flow : E → ℤ, ∀ v : V,
    integralEdgeBoundary44856 source target flow v = chain v

def componentBalance44856
    {V E : Type*} [Fintype V] [DecidableEq V]
    (source target : E → V) (chain : V → ℤ) : Prop :=
  ∀ C : Finset V,
    occurrenceComponent44856 source target C →
      ∑ v ∈ C, chain v = 0

/-- A nonnegative integral pairing of positive and negative unit copies by
paths in the occurrence graph. -/
def componentPathPairing44856
    {V E : Type*} [Fintype V] [DecidableEq V]
    (source target : E → V) (chain : V → ℤ) : Prop :=
  ∃ pair : V → V → ℕ,
    (∀ u : V,
      ((∑ v : V, pair u v : ℕ) : ℤ) = max (chain u) 0) ∧
    (∀ v : V,
      ((∑ u : V, pair u v : ℕ) : ℤ) = max (-chain v) 0) ∧
    (∀ u v : V, pair u v ≠ 0 →
      Relation.ReflTransGen (occurrenceAdjacency44856 source target) u v)

/-- Claim 44856: an integral vertex zero-chain is an integral edge boundary
exactly when every connected component has zero total coefficient; the same
criterion is the path pairing of positive and negative unit copies. -/
def integralBoundaryComponentCriterion_claim44856 : Prop :=
  ∀ {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E]
    (source target : E → V) (chain : V → ℤ),
    (isIntegralEdgeBoundary44856 source target chain ↔
      componentBalance44856 source target chain) ∧
    (componentBalance44856 source target chain ↔
      componentPathPairing44856 source target chain)

end

end MathlibPlus.Open.Combinatorics
