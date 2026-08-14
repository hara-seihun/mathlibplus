import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

open scoped BigOperators
noncomputable section

/-- The colors carried by a vertex across all incident target triangles. -/
def colorSupport
    {V : Type} [Fintype V]
    (triangles : Finset (Finset V))
    (colour : Finset V → V → Fin 3)
    (v : V) : Finset (Fin 3) := by
  classical
  exact Finset.univ.filter (fun k =>
    ∃ t ∈ triangles, v ∈ t ∧ colour t v = k)

/-- The explicit finite-set predicate for a coatom-colored descendant packing. -/
def coatomColoredPacking
    {V : Type} [Fintype V]
    (triangles : Finset (Finset V)) (D : Finset V)
    (colour : Finset V → V → Fin 3)
    (P : ℕ) : Prop := by
  classical
  exact
    triangles.card = P ∧
      (∀ t ∈ triangles,
        t.card = 3 ∧
          Function.Bijective
            (fun v : {x // x ∈ t} => colour t v.1)) ∧
      (∀ t₁ ∈ triangles, ∀ t₂ ∈ triangles,
        t₁ ≠ t₂ → (t₁ ∩ t₂).card ≤ 1) ∧
      (∀ v : V,
        v ∈ D ↔ ∃ t ∈ triangles, v ∈ t)

/-- Claim 26087: the coatom-colored packing data and its vertex color support. -/
def claim26087
    {V : Type} [Fintype V]
    (triangles : Finset (Finset V)) (D : Finset V)
    (colour : Finset V → V → Fin 3)
    (P : ℕ) : Prop :=
  coatomColoredPacking triangles D colour P

/-- Extra color support above the one-color-per-used-vertex floor. -/
def extraCoatomSupportDebt
    {V : Type} [Fintype V]
    (triangles : Finset (Finset V)) (D : Finset V)
    (colour : Finset V → V → Fin 3) : ℕ := by
  classical
  exact Finset.sum D (fun v => (colorSupport triangles colour v).card - 1)

/-- Total vertex-color incidence mass. -/
def colorIncidenceMass
    {V : Type} [Fintype V]
    (triangles : Finset (Finset V)) (D : Finset V)
    (colour : Finset V → V → Fin 3) : ℕ := by
  classical
  exact Finset.sum D (fun v => (colorSupport triangles colour v).card)

/-- Claim 26088: the debt is the excess incidence mass over the used-vertex
floor. -/
def claim26088
    {V : Type} [Fintype V]
    (triangles : Finset (Finset V)) (D : Finset V)
    (colour : Finset V → V → Fin 3)
    (P e : ℕ) : Prop :=
  coatomColoredPacking triangles D colour P →
    e = extraCoatomSupportDebt triangles D colour ∧
      colorIncidenceMass triangles D colour = D.card + e

/-- The monochromatic class of a used vertex for a given color. -/
def colorClass
    {V : Type} [Fintype V]
    (triangles : Finset (Finset V)) (D : Finset V)
    (colour : Finset V → V → Fin 3)
    (i : Fin 3) : Finset V := by
  classical
  exact D.filter (fun v => colorSupport triangles colour v = {i})

/-- Claim 26091: monochromatic vertices and rainbow triangles form a genuine
tripartition. -/
def claim26091
    {V : Type} [Fintype V]
    (triangles : Finset (Finset V)) (D : Finset V)
    (colour : Finset V → V → Fin 3)
    (P : ℕ) : Prop := by
  classical
  exact
    coatomColoredPacking triangles D colour P →
      (∀ v ∈ D, (colorSupport triangles colour v).card = 1) →
        (D = colorClass triangles D colour (0 : Fin 3) ∪
              colorClass triangles D colour (1 : Fin 3) ∪
              colorClass triangles D colour (2 : Fin 3)) ∧
          (∀ i j : Fin 3, i ≠ j →
            Disjoint (colorClass triangles D colour i)
              (colorClass triangles D colour j)) ∧
          (∀ t ∈ triangles, ∀ i : Fin 3,
            (t.filter (fun v => v ∈ colorClass triangles D colour i)).card = 1)

end
end MathlibPlus.Open.ResearchFormalization
