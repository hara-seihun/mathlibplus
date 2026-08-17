import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R4922

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.decEq

/-- The boundary of one oriented edge of the simple path
`P_0 -> P_1 -> ... -> P_l`. -/
def pathEdgeBoundary {α : Type*} (l : ℕ) (P : Fin (l + 1) → α)
    (i : Fin l) : α →₀ ℝ :=
  Finsupp.single (P i.castSucc) (1 : ℝ) -
    Finsupp.single (P i.succ) (1 : ℝ)

/-- The incidence map `D` obtained by summing the oriented edge boundaries. -/
def pathIncidence {α : Type*} (l : ℕ) (P : Fin (l + 1) → α)
    (t : Fin l → ℝ) : α →₀ ℝ :=
  ∑ i : Fin l, t i • pathEdgeBoundary l P i

/-- The scaled endpoint boundary on the same path. -/
def endpointBoundary {α : Type*} (l : ℕ) (P : Fin (l + 1) → α)
    (c : ℝ) : α →₀ ℝ :=
  c • (Finsupp.single (P 0) (1 : ℝ) -
    Finsupp.single (P (Fin.last l)) (1 : ℝ))

/-- R-4922.2: on a nonempty simple path, a nonnegative same-path repair at
fixed endpoint scale is exactly the coordinatewise constant total, hence is
coordinatewise `c - q` and is unique whenever it is feasible. -/
def claim55451 : Prop :=
  ∀ {α : Type*} (l : ℕ) (P : Fin (l + 1) → α),
    0 < l → Function.Injective P →
    ∀ (q r : Fin l → ℝ) (c : ℝ),
      (∀ i, 0 ≤ q i) → (∀ i, 0 ≤ r i) → 0 ≤ c →
      let target := endpointBoundary l P c
      (pathIncidence l P (q + r) = target ↔
          ∀ i, q i + r i = c) ∧
        ((∀ i, q i + r i = c) ↔
          ∀ i, r i = c - q i) ∧
        (pathIncidence l P (q + r) = target →
          ∀ r' : Fin l → ℝ,
            (∀ i, 0 ≤ r' i) →
            pathIncidence l P (q + r') = target → r' = r)

end
end MathlibPlus.Open.ResearchFormalization.R4922
