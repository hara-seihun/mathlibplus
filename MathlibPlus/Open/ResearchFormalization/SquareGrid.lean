import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

abbrev PlanarPoint := ℝ × ℝ

noncomputable def planarDistance (p q : PlanarPoint) : ℝ :=
  Real.sqrt ((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2)

def normalizedPlanarConfiguration (n : ℕ) (X : Finset PlanarPoint) : Prop :=
  X.card = n ∧
    (∀ p ∈ X, ∀ q ∈ X, p ≠ q → 1 ≤ planarDistance p q) ∧
    ∃ p ∈ X, ∃ q ∈ X, p ≠ q ∧ planarDistance p q = 1

noncomputable def planarDiameter (X : Finset PlanarPoint) : ℝ :=
  sSup {d : ℝ | ∃ p ∈ X, ∃ q ∈ X, d = planarDistance p q}

noncomputable def optimalPlanarDiameter (n : ℕ) : ℝ :=
  sInf {d : ℝ | ∃ X : Finset PlanarPoint,
    normalizedPlanarConfiguration n X ∧ d = planarDiameter X}

noncomputable def integerGridPoints (s : ℕ) : Finset PlanarPoint := by
  classical
  exact (Finset.range s).biUnion (fun i =>
    (Finset.range s).image (fun j => ((i : ℝ), (j : ℝ))))

def squareGridGlobalComparison : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    let s : ℕ := ⌈Real.sqrt (n : ℝ)⌉₊
    ∃ X : Finset PlanarPoint,
      X.card = n ∧ X ⊆ integerGridPoints s ∧
      normalizedPlanarConfiguration n X ∧
      planarDiameter X ≤ Real.sqrt 2 * (s - 1 : ℕ) ∧
      optimalPlanarDiameter n ≤ Real.sqrt 2 * (s - 1 : ℕ)

end MathlibPlus.Open.ResearchFormalization
