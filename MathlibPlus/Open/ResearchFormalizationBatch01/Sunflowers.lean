import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalizationBatch01

noncomputable section

abbrev Vertex6 := Fin 6

abbrev Edge6 := {e : Vertex6 × Vertex6 // e.1 < e.2}

def mkEdge6 (a b : Vertex6) (h : a < b) : Edge6 := ⟨(a, b), h⟩

def incident6 (e : Edge6) (v : Vertex6) : Prop :=
  e.1.1 = v ∨ e.1.2 = v

abbrev Graph6 := Finset Edge6

def memberSupport6 (G : Graph6) (v : Vertex6) : Finset Edge6 := by
  classical
  exact G.filter (fun e => incident6 e v)

def incidenceFamily6 (G : Graph6) : Finset (Finset Edge6) := by
  classical
  exact Finset.univ.image (memberSupport6 G)

def supportRow6 (e : Edge6) : Finset Vertex6 := by
  classical
  exact Finset.univ.filter (incident6 e)

def isThreeRegular6 (G : Graph6) : Prop :=
  ∀ v : Vertex6, (memberSupport6 G v).card = 3

def pairIntersectionCount6 (G : Graph6) (k : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun p : Vertex6 × Vertex6 =>
    p.1 < p.2 ∧
      (memberSupport6 G p.1 ∩ memberSupport6 G p.2).card = k)).card

def supportRowCount6 (G : Graph6) (k : ℕ) : ℕ := by
  classical
  exact (G.filter (fun e => (supportRow6 e).card = k)).card

def independentSet6 (G : Graph6) (S : Finset Vertex6) : Prop :=
  ∀ ⦃e : Edge6⦄, e ∈ G → ∀ ⦃u v : Vertex6⦄,
    u ∈ S → v ∈ S → incident6 e u → incident6 e v → u = v

def independentTriple6 (G : Graph6) (a b c : Vertex6) : Prop :=
  ∀ ⦃e : Edge6⦄, e ∈ G →
    ¬ (incident6 e a ∧ incident6 e b) ∧
    ¬ (incident6 e a ∧ incident6 e c) ∧
    ¬ (incident6 e b ∧ incident6 e c)

def sunflower3 (A B C : Finset Edge6) : Prop :=
  A ∩ B = A ∩ C ∧ A ∩ B = B ∩ C

/-- The incidence-family characterization of three-sunflowers. -/
def claim47346 : Prop :=
  ∀ G : Graph6, isThreeRegular6 G →
    G.card = 9 ∧
    (incidenceFamily6 G).card = 6 ∧
    (∀ v : Vertex6, (memberSupport6 G v).card = 3) ∧
    (∀ e ∈ G, (supportRow6 e).card = 2) ∧
    supportRowCount6 G 2 = 9 ∧
    (∀ k : ℕ, k ≠ 2 → supportRowCount6 G k = 0) ∧
    pairIntersectionCount6 G 1 = 9 ∧
    pairIntersectionCount6 G 0 = 6 ∧
    (∀ a b c : Vertex6, a ≠ b → a ≠ c → b ≠ c →
      (sunflower3 (memberSupport6 G a) (memberSupport6 G b)
        (memberSupport6 G c) ↔ independentTriple6 G a b c))

def prismGraph6 : Graph6 :=
  { mkEdge6 0 1 (by decide),
    mkEdge6 1 2 (by decide),
    mkEdge6 0 2 (by decide),
    mkEdge6 3 4 (by decide),
    mkEdge6 4 5 (by decide),
    mkEdge6 3 5 (by decide),
    mkEdge6 0 3 (by decide),
    mkEdge6 1 4 (by decide),
    mkEdge6 2 5 (by decide) }

def completeBipartiteGraph6 : Graph6 :=
  { mkEdge6 0 3 (by decide),
    mkEdge6 0 4 (by decide),
    mkEdge6 0 5 (by decide),
    mkEdge6 1 3 (by decide),
    mkEdge6 1 4 (by decide),
    mkEdge6 1 5 (by decide),
    mkEdge6 2 3 (by decide),
    mkEdge6 2 4 (by decide),
    mkEdge6 2 5 (by decide) }

/-- The two explicit 3-regular incidence families agree on the listed scalar
statistics but have different independent triples. -/
def claim47347 : Prop :=
  let G₁ := prismGraph6
  let G₂ := completeBipartiteGraph6
  G₁.card = 9 ∧ G₂.card = 9 ∧
  isThreeRegular6 G₁ ∧ isThreeRegular6 G₂ ∧
  (incidenceFamily6 G₁).card = 6 ∧ (incidenceFamily6 G₂).card = 6 ∧
  (∀ v : Vertex6,
    (memberSupport6 G₁ v).card = 3 ∧ (memberSupport6 G₂ v).card = 3) ∧
  (∀ k : ℕ, supportRowCount6 G₁ k = supportRowCount6 G₂ k ∧
    ((k = 2 → supportRowCount6 G₁ k = 9) ∧
     (k ≠ 2 → supportRowCount6 G₁ k = 0))) ∧
  (∀ k : ℕ, pairIntersectionCount6 G₁ k = pairIntersectionCount6 G₂ k) ∧
  pairIntersectionCount6 G₁ 1 = 9 ∧ pairIntersectionCount6 G₁ 0 = 6 ∧
  (∀ S : Finset Vertex6, independentSet6 G₁ S → S.card ≤ 2) ∧
  (∃ S : Finset Vertex6, independentSet6 G₁ S ∧ S.card = 2) ∧
  independentTriple6 G₂ 0 1 2 ∧
  (memberSupport6 G₂ 0 ∩ memberSupport6 G₂ 1 = ∅) ∧
  (memberSupport6 G₂ 0 ∩ memberSupport6 G₂ 2 = ∅) ∧
  (memberSupport6 G₂ 1 ∩ memberSupport6 G₂ 2 = ∅) ∧
  sunflower3 (memberSupport6 G₂ 0) (memberSupport6 G₂ 1)
    (memberSupport6 G₂ 2)

end
end MathlibPlus.Open.ResearchFormalizationBatch01
