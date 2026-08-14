import Mathlib

namespace MathlibPlus.Open.FormalizationBatch

section SpiderFormula

variable {V : Type*} [Fintype V] [DecidableEq V]

def pathAdj (n : Nat) (a b : Fin n) : Prop :=
  a.1 + 1 = b.1 ∨ b.1 + 1 = a.1

def pathGraph (n : Nat) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (pathAdj n)

def SpiderVertex (s : Nat) (lengths : Fin s → Nat) :=
  Unit ⊕ (Σ i : Fin s, Fin (lengths i))

def spiderAdj {s : Nat} (lengths : Fin s → Nat)
    (x y : SpiderVertex s lengths) : Prop :=
  match x, y with
  | Sum.inl _, Sum.inl _ => False
  | Sum.inl _, Sum.inr ⟨_, d⟩ => d.1 = 0
  | Sum.inr ⟨_, d⟩, Sum.inl _ => d.1 = 0
  | Sum.inr ⟨i, d⟩, Sum.inr ⟨j, e⟩ =>
      i = j ∧ (d.1 + 1 = e.1 ∨ e.1 + 1 = d.1)

def spiderGraph {s : Nat} (lengths : Fin s → Nat) :
    SimpleGraph (SpiderVertex s lengths) :=
  SimpleGraph.fromRel (spiderAdj lengths)

def independentSet (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ¬G.Adj x y

noncomputable def independencePolynomial (G : SimpleGraph V) : Polynomial ℤ := by
  classical
  exact ∑ S : Finset V,
    if independentSet G S then Polynomial.X ^ S.card else 0

noncomputable def spiderIndependencePolynomial {s : Nat}
    (lengths : Fin s → Nat) : Polynomial ℤ := by
  classical
  letI : Fintype (SpiderVertex s lengths) := by
    unfold SpiderVertex
    infer_instance
  exact independencePolynomial (spiderGraph lengths)

noncomputable def pathIndependencePolynomial (n : Nat) : Polynomial ℤ :=
  independencePolynomial (pathGraph n)

/-- Claim 48247: center-excluded/center-included torso conditioning gives the
independence polynomial of every finite spider. -/
def claim48247 : Prop :=
  pathIndependencePolynomial 0 = 1 ∧
    ∀ (s : Nat) (lengths : Fin s → Nat),
      (∀ i, 0 < lengths i) →
        spiderIndependencePolynomial lengths =
          (∏ i : Fin s, pathIndependencePolynomial (lengths i)) +
            Polynomial.X *
              (∏ i : Fin s, pathIndependencePolynomial (lengths i - 1))

end SpiderFormula

end MathlibPlus.Open.FormalizationBatch
