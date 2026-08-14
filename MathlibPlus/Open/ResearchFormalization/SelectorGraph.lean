import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.SelectorGraph

abbrev SelectorSample (n m : ℕ) := (Fin n → Bool) × (Fin m → Bool)

def signValue (b : Bool) : ℝ := if b then 1 else -1

def uniformExpectation {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (Fintype.card α : ℝ)⁻¹ * ∑ x, f x

def finiteVariance {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  uniformExpectation (fun x => (f x - uniformExpectation f) ^ 2)

def selectorTarget {n m : ℕ}
    (e : Fin n → Fin m × Fin m) (weights : Fin n → ℝ)
    (ω : SelectorSample n m) : ℝ :=
  ∑ i, weights i *
    (if ω.1 i then signValue (ω.2 (e i).2) else signValue (ω.2 (e i).1))

def incidenceWeight {n m : ℕ}
    (e : Fin n → Fin m × Fin m) (weights : Fin n → ℝ) (v : Fin m) : ℝ :=
  ∑ i, if v = (e i).1 ∨ v = (e i).2 then weights i else 0

def selectorCoefficient {n m : ℕ}
    (e : Fin n → Fin m × Fin m) (weights : Fin n → ℝ) (v : Fin m) : ℝ :=
  incidenceWeight e weights v / 2

def singletonEnergy {n m : ℕ}
    (e : Fin n → Fin m × Fin m) (weights : Fin n → ℝ) : ℝ :=
  ∑ v, (selectorCoefficient e weights v) ^ 2

def bilinearEnergy {n : ℕ} (weights : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, (weights i) ^ 2

def selectorEnergy {n m : ℕ}
    (e : Fin n → Fin m × Fin m) (weights : Fin n → ℝ) : ℝ :=
  singletonEnergy e weights + bilinearEnergy weights

def selectorWalshExpansion {n m : ℕ}
    (e : Fin n → Fin m × Fin m) (weights : Fin n → ℝ)
    (ω : SelectorSample n m) : ℝ :=
  (∑ v, selectorCoefficient e weights v * signValue (ω.2 v)) +
    (1 / 2 : ℝ) * ∑ i, weights i * signValue (ω.1 i) *
      (signValue (ω.2 (e i).2) - signValue (ω.2 (e i).1))

/-- The exact arbitrary shared-top selector graph identity, on its finite
uniform product sign space.  No restriction is imposed on incidence beyond
having distinct endpoints, so parallel edges and cycles remain allowed. -/
def arbitrarySharedTopSelectorGraphAndWalshEnergy : Prop :=
  ∀ (n m : ℕ), 0 < n → 0 < m →
    ∀ (e : Fin n → Fin m × Fin m),
      (∀ i, (e i).1 ≠ (e i).2) →
      ∀ (weights : Fin n → ℝ),
        (∀ i, 0 ≤ weights i) →
        (∑ i, weights i = 1) →
        (∀ ω : SelectorSample n m,
          selectorTarget e weights ω = selectorWalshExpansion e weights ω) ∧
        finiteVariance (selectorTarget e weights) = selectorEnergy e weights

end MathlibPlus.Open.ResearchFormalization.SelectorGraph
