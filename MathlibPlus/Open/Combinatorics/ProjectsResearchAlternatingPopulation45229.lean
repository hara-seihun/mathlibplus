import Mathlib

open scoped BigOperators Classical
noncomputable section

namespace MathlibPlus.Open.ProjectsResearch

/-- The six cells are kept in the stated order `(1,2,4,12,13,23)`. -/
def cell145229 : Fin 6 := 0
def cell245229 : Fin 6 := 1
def cell445229 : Fin 6 := 2
def cell1245229 : Fin 6 := 3
def cell1345229 : Fin 6 := 4
def cell2345229 : Fin 6 := 5

def massTable45229 (q : ℕ) (x : Fin 6 → ℕ) : Prop :=
  (∑ c : Fin 6, x c) = q

def lineTable45229 (q k : ℕ) : Fin 6 → ℕ :=
  fun c => if c = cell145229 then k
    else if c = cell245229 then q - k else 0

def populationPlus45229 (q : ℕ) : (Fin 6 → ℕ) → ℕ :=
  fun x => ∑ k ∈ (Finset.range (q + 1)).filter (fun k => Even k),
    if x = lineTable45229 q k then Nat.choose q k else 0

def populationMinus45229 (q : ℕ) : (Fin 6 → ℕ) → ℕ :=
  fun x => ∑ k ∈ (Finset.range (q + 1)).filter (fun k => Odd k),
    if x = lineTable45229 q k then Nat.choose q k else 0

/-- Claim R-2816.2 (45229). -/
def claim45229 : Prop :=
  ∀ q : ℕ, 1 ≤ q →
    (∀ k, k ≤ q → massTable45229 q (lineTable45229 q k)) ∧
    (∀ x, populationPlus45229 q x > 0 → populationMinus45229 q x = 0) ∧
    (∀ x, populationMinus45229 q x > 0 → populationPlus45229 q x = 0) ∧
    populationPlus45229 q ≠ populationMinus45229 q

end MathlibPlus.Open.ProjectsResearch
