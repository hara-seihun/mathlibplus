import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-- Weak decrease and positivity for a list of parts; nonemptiness is a separate hypothesis. -/
def IsPartition : List ℕ → Prop
  | [] => True
  | x :: xs => x > 0 ∧ IsPartition xs ∧ ∀ y ∈ xs, x ≥ y

/-- Zero-based access to displayed parts, with the convention μ_{ℓ+1}=0. -/
def partAt (μ : List ℕ) (j : ℕ) : ℕ :=
  if h : j < μ.length then μ.get ⟨j, h⟩ else 0

/-- The shape λ^(k) from the chamber formula. -/
def chamberShape (m k : ℕ) (μ : List ℕ) : List ℕ :=
  if k = 0 then
    m :: μ
  else
    (μ.take k).map (fun a => a - 1) ++ (m + k) :: μ.drop k

/-- The displayed chamber condition, using 0 for μ_{ℓ+1}. -/
def chamberCondition (μ : List ℕ) (m k : ℕ) : Prop :=
  if k = 0 then
    m ≥ partAt μ 0
  else
    k ≤ μ.length ∧
      partAt μ (k - 1) - 1 ≥ m + k ∧
      m + k ≥ partAt μ k

/-- Exact chamber inequalities and disjointness of their degree intervals. -/
def exactChamberInequalities : Prop :=
  ∀ (s : ℕ) (μ : List ℕ),
    μ ≠ [] → IsPartition μ → μ.sum = s →
      ∀ m : ℕ,
        (IsPartition (chamberShape m 0 μ) ↔ chamberCondition μ m 0) ∧
        (∀ k : ℕ, 1 ≤ k → k ≤ μ.length →
          (IsPartition (chamberShape m k μ) ↔ chamberCondition μ m k)) ∧
        (∀ k₁ k₂ : ℕ,
          k₁ ≤ μ.length → k₂ ≤ μ.length →
          chamberCondition μ m k₁ → chamberCondition μ m k₂ → k₁ = k₂)

end MathlibPlus.Open.ResearchFormalizationBatch
