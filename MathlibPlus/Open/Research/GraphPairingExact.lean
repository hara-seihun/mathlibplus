import MathlibPlus.Open.Graphs.BasisTranspose

open scoped BigOperators

namespace MathlibPlus.Open.Research.GraphPairingExact

noncomputable section

open MathlibPlus.Open.Graphs

attribute [local instance] Classical.propDecidable

abbrev GraphSpace (n : ℕ) := GraphIsoClass n →₀ ℚ

def weightedPairing {n : ℕ} (x y : GraphSpace n) : ℚ :=
  ∑ G ∈ x.support,
    x G * y G * graphAutWeight n G

def basisPairing {n : ℕ} (G H : GraphIsoClass n) : ℚ :=
  weightedPairing (Finsupp.single G 1) (Finsupp.single H 1)

def treeClass {n : ℕ} (G : GraphIsoClass n) : Prop :=
  (graphRepresentative G).IsTree

def treeSupported {n : ℕ} (x : GraphSpace n) : Prop :=
  ∀ G : GraphIsoClass n, ¬ treeClass G → x G = 0

/-- The automorphism-weighted diagonal pairing is positive definite both on
finite-graph classes and on its tree-supported restriction. -/
def claim19594 : Prop :=
  (∀ n : ℕ, ∀ G H : GraphIsoClass n,
    basisPairing G H =
      if G = H then graphAutWeight n G else 0) ∧
  (∀ n : ℕ, ∀ x : GraphSpace n,
    0 ≤ weightedPairing x x ∧
      (weightedPairing x x = 0 ↔ x = 0)) ∧
  (∀ n : ℕ, ∀ G H : GraphIsoClass n,
    treeClass G → treeClass H →
      basisPairing G H =
        if G = H then graphAutWeight n G else 0) ∧
  (∀ n : ℕ, ∀ x : GraphSpace n, treeSupported x →
    0 ≤ weightedPairing x x ∧
      (weightedPairing x x = 0 ↔ x = 0))

end
end MathlibPlus.Open.Research.GraphPairingExact
