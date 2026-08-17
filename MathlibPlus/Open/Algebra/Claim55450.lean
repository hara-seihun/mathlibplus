import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Algebra.Claim55450

noncomputable section

/-- The boundary of the edge from `P_i` to `P_(i+1)` in the free module. -/
def pathEdgeBoundary {R α : Type*} [CommRing R] [DecidableEq α]
    (P : ℕ → α) (i : ℕ) : α →₀ R :=
  Finsupp.single (P i) (1 : R) - Finsupp.single (P (i + 1)) (1 : R)

def pathBoundary {R α : Type*} [CommRing R] [DecidableEq α]
    (l : ℕ) (P : ℕ → α) (t : ℕ → R) : α →₀ R :=
  ∑ i ∈ Finset.range l, t i • pathEdgeBoundary P i

def displayedPathBoundary {R α : Type*} [CommRing R] [DecidableEq α]
    (l : ℕ) (P : ℕ → α) (t : ℕ → R) : α →₀ R :=
  t 0 • Finsupp.single (P 0) (1 : R) +
    (∑ i ∈ Finset.range (l - 1),
      (t (i + 1) - t i) • Finsupp.single (P (i + 1)) (1 : R)) -
    t (l - 1) • Finsupp.single (P l) (1 : R)

/-- R-4922.1: the path-incidence identity for pairwise distinct basis
positions and the displayed edge-boundary operator. -/
def pathIncidenceIdentity_claim55450 : Prop :=
  ∀ {R α : Type*} [CommRing R] [DecidableEq α]
    (l : ℕ) (P : ℕ → α) (t : ℕ → R),
    0 < l →
    (∀ i j : ℕ, i ≤ l → j ≤ l → i ≠ j → P i ≠ P j) →
    pathBoundary l P t = displayedPathBoundary l P t

end

end MathlibPlus.Open.Algebra.Claim55450
