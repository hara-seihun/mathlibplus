import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R4220.Claim53348

noncomputable section

abbrev Vertex53348 (n : ℕ) := Fin n
abbrev EdgeSet53348 (n : ℕ) := Finset (Vertex53348 n × Vertex53348 n)

/-- The undirected adjacency relation used by the component-size forest
polynomial. -/
def edgeRelation53348 {n : ℕ} (E : EdgeSet53348 n) : Vertex53348 n →
    Vertex53348 n → Prop :=
  fun u v => (u, v) ∈ E ∨ (v, u) ∈ E

def reachable53348 {n : ℕ} (E : EdgeSet53348 n)
    (u v : Vertex53348 n) : Prop :=
  Relation.ReflTransGen (edgeRelation53348 E) u v

def component53348 {n : ℕ} (E : EdgeSet53348 n) (V : Finset (Vertex53348 n))
    (u : Vertex53348 n) : Finset (Vertex53348 n) := by
  classical
  exact V.filter (fun v => reachable53348 E u v)

def representatives53348 {n : ℕ} (E : EdgeSet53348 n)
    (V : Finset (Vertex53348 n)) : Finset (Vertex53348 n) := by
  classical
  exact V.filter (fun u => ∀ v ∈ V, reachable53348 E u v → u.val ≤ v.val)

def componentSize53348 {n : ℕ} (E : EdgeSet53348 n)
    (V : Finset (Vertex53348 n)) (u : Vertex53348 n) : ℕ :=
  (component53348 E V u).card

/-- The scalar forest polynomial `U_H`, with one variable for each component
size and one summand for each edge-subset forest. -/
def forestPolynomial53348 {n : ℕ} (E : EdgeSet53348 n)
    (V : Finset (Vertex53348 n)) : MvPolynomial ℕ ℤ := by
  classical
  let E₀ := E.filter (fun e => e.1 ∈ V ∧ e.2 ∈ V)
  exact Finset.sum E₀.powerset (fun A =>
    Finset.prod (representatives53348 A V)
      (fun u => MvPolynomial.X (componentSize53348 A V u)))

def U53348 {n : ℕ} (E : EdgeSet53348 n) : MvPolynomial ℕ ℤ :=
  forestPolynomial53348 E Finset.univ

/-- The card obtained by deleting the vertices in a connected marked set. -/
def deleteCardEdges53348 {n : ℕ} (E : EdgeSet53348 n)
    (C : Finset (Vertex53348 n)) : EdgeSet53348 n :=
  E.filter (fun e => e.1 ∉ C ∧ e.2 ∉ C)

def cardPolynomial53348 {n : ℕ} (E : EdgeSet53348 n)
    (C : Finset (Vertex53348 n)) : MvPolynomial ℕ ℤ :=
  forestPolynomial53348 (deleteCardEdges53348 E C) (Finset.univ \ C)

def path6Edges53348 : EdgeSet53348 6 :=
  {(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)}

def centralSet53348 : Finset (Vertex53348 6) := {1, 2}
def noncentralSet53348 : Finset (Vertex53348 6) := {0, 1}

def centralCard53348 : MvPolynomial ℕ ℤ :=
  cardPolynomial53348 path6Edges53348 centralSet53348

def noncentralCard53348 : MvPolynomial ℕ ℤ :=
  cardPolynomial53348 path6Edges53348 noncentralSet53348

def x1_53348 : MvPolynomial ℕ ℤ := MvPolynomial.X 1
def x2_53348 : MvPolynomial ℕ ℤ := MvPolynomial.X 2
def x3_53348 : MvPolynomial ℕ ℤ := MvPolynomial.X 3

def centralFormula53348 : MvPolynomial ℕ ℤ :=
  (x2_53348 + x1_53348 ^ 2) ^ 2

def noncentralFormula53348 : MvPolynomial ℕ ℤ :=
  x1_53348 * (x3_53348 + 2 * x1_53348 * x2_53348 + x1_53348 ^ 3)

/-- Evaluation at zero of every variable whose index is at least `h`, while
retaining the lower-index variables in the same polynomial carrier. -/
def scalarSpecializationAbove53348 (h : ℕ)
    (p : MvPolynomial ℕ ℤ) : MvPolynomial ℕ ℤ :=
  (MvPolynomial.eval₂Hom (MvPolynomial.C : ℤ →+* MvPolynomial ℕ ℤ)
    (fun j => if j < h then MvPolynomial.X j else 0)) p

def x1Fourth53348 : ℕ →₀ ℕ := Finsupp.single 1 4

def coefficientAtX1Fourth53348 (p : MvPolynomial ℕ ℤ) : ℤ :=
  MvPolynomial.coeff x1Fourth53348 p

/-- Claim 53348: the central P6 card and the noncentral {1,2} card have the
same surviving `x₁⁴` coefficient under the threshold-three specialization. -/
def claim_53348 : Prop :=
  centralSet53348 = {1, 2} ∧
    noncentralSet53348 = {0, 1} ∧
    centralCard53348 = centralFormula53348 ∧
      noncentralCard53348 = noncentralFormula53348 ∧
        coefficientAtX1Fourth53348 centralCard53348 = 1 ∧
          coefficientAtX1Fourth53348 noncentralCard53348 = 1 ∧
            coefficientAtX1Fourth53348
                (scalarSpecializationAbove53348 3 centralCard53348) = 1 ∧
              coefficientAtX1Fourth53348
                  (scalarSpecializationAbove53348 3 noncentralCard53348) = 1

end

end MathlibPlus.Open.ResearchFormalization.R4220.Claim53348
