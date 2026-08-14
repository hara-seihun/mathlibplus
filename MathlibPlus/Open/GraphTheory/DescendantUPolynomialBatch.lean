import Mathlib

open scoped Classical BigOperators
noncomputable section

namespace MathlibPlus.Open.GraphTheory.DescendantUPolynomial

section UPolynomial

/-- One copy of every undirected edge, oriented by the vertex order. -/
def edgePairs {n : ℕ} (G : SimpleGraph (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun e => e.1.val < e.2.val ∧ G.Adj e.1 e.2)

def selectedAdj {n : ℕ} (E : Finset (Fin n × Fin n))
    (u v : Fin n) : Prop :=
  (u.val < v.val ∧ (u, v) ∈ E) ∨ (v.val < u.val ∧ (v, u) ∈ E)

def componentRelation {n : ℕ} (E : Finset (Fin n × Fin n)) :
    Fin n → Fin n → Prop :=
  Relation.ReflTransGen (selectedAdj E)

def isComponentPartition {n : ℕ} (E : Finset (Fin n × Fin n))
    (P : Finset (Finset (Fin n))) : Prop :=
  (∀ C ∈ P, C.Nonempty) ∧
    P.biUnion id = Finset.univ ∧
    (∀ C ∈ P, ∀ D ∈ P, C ≠ D → Disjoint C D) ∧
    (∀ u v, componentRelation E u v →
      ∃ C ∈ P, u ∈ C ∧ v ∈ C) ∧
    (∀ C ∈ P, ∀ u ∈ C, ∀ v ∈ C, componentRelation E u v)

def componentMonomial {n : ℕ} (P : Finset (Finset (Fin n))) :
    MvPolynomial ℕ ℤ :=
  ∏ C ∈ P, MvPolynomial.X C.card

/-- The standard edge-subset/component-partition definition of the
multivariate U-polynomial. -/
def uPolynomial {n : ℕ} (G : SimpleGraph (Fin n)) : MvPolynomial ℕ ℤ :=
  ∑ E ∈ (Finset.univ : Finset (Finset (Fin n × Fin n))).filter
      (fun E => E ⊆ edgePairs G),
    ∑ P ∈ (Finset.univ : Finset (Finset (Finset (Fin n)))).filter
      (fun P => isComponentPartition E P),
      componentMonomial P

end UPolynomial

section Spider

def spiderEdgePairs : Finset (Fin 8 × Fin 8) :=
  {(0, 1), (0, 2), (2, 3), (0, 4), (4, 5), (5, 6), (6, 7)}

def spiderAdj (i j : Fin 8) : Prop :=
  (i, j) ∈ spiderEdgePairs ∨ (j, i) ∈ spiderEdgePairs

def spiderGraph : SimpleGraph (Fin 8) :=
  { Adj := spiderAdj
    symm := ⟨fun i j h => by
      rcases h with h | h
      · exact Or.inr h
      · exact Or.inl h⟩
    loopless := ⟨fun i h => by
      fin_cases i <;> simp [spiderAdj, spiderEdgePairs] at h⟩ }

def embed8 (i : Fin 8) : Fin 10 :=
  ⟨i.val, by omega⟩

def descendantAdj (p : Fin 8) (i j : Fin 10) : Prop :=
  (∃ hi : i.val < 8, ∃ hj : j.val < 8,
      spiderAdj ⟨i.val, hi⟩ ⟨j.val, hj⟩) ∨
    (i = embed8 p ∧ j = 8) ∨ (j = embed8 p ∧ i = 8) ∨
    (i = 8 ∧ j = 9) ∨ (j = 8 ∧ i = 9)

def descendantGraph (p : Fin 8) : SimpleGraph (Fin 10) :=
  { Adj := descendantAdj p
    symm := ⟨fun i j h => by
      rcases h with h | h | h | h | h
      · rcases h with ⟨hi, hj, hadj⟩
        exact Or.inl ⟨hj, hi, by simpa [spiderAdj, or_comm] using hadj⟩
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))⟩
    loopless := ⟨fun i h => by
      rcases h with h | h | h | h | h
      · rcases h with ⟨hi, hj, hadj⟩
        exact spiderGraph.loopless.irrefl ⟨i.val, hi⟩ hadj
      · rcases h with ⟨h₁, h₂⟩
        have hi := congrArg Fin.val h₁
        have h8 := congrArg Fin.val h₂
        change i.val = p.val at hi
        omega
      · rcases h with ⟨h₁, h₂⟩
        have hi := congrArg Fin.val h₁
        have h8 := congrArg Fin.val h₂
        change i.val = p.val at hi
        omega
      · omega
      · omega⟩ }

def a₁ : Fin 8 := 4
def a₂ : Fin 8 := 5
def a₃ : Fin 8 := 6
def b₁ : Fin 8 := 2
def markedSpiderVertices : Finset (Fin 8) := {a₁, a₂, a₃, b₁}

def descendantFamily : Fin 4 → SimpleGraph (Fin 10)
  | 0 => descendantGraph a₁
  | 1 => descendantGraph a₂
  | 2 => descendantGraph a₃
  | 3 => descendantGraph b₁

/-- Claim 6165. -/
def claim6165 : Prop :=
  spiderGraph.IsTree ∧
    (∀ i : Fin 4, (descendantFamily i).IsTree)

/-- Claim 6166. -/
def claim6166 : Prop :=
  uPolynomial (descendantFamily 0) - uPolynomial (descendantFamily 1) +
      uPolynomial (descendantFamily 2) - uPolynomial (descendantFamily 3) = 0

end Spider

end MathlibPlus.Open.GraphTheory.DescendantUPolynomial
