import Mathlib

namespace MathlibPlus.GraphTheory

/-- Two finite subsets of an ambient finite set satisfy the integer-valued
inclusion--exclusion lower bound used by the induced-edge obstruction. -/
theorem intersection_card_lower_bound
    {E : Type*} [Fintype E] [DecidableEq E]
    (A₀ A₁ B : Finset E) (h₀ : A₀ ⊆ B) (h₁ : A₁ ⊆ B) :
    (A₀.card : ℤ) + (A₁.card : ℤ) - (B.card : ℤ) ≤
      ((A₀ ∩ A₁).card : ℤ) := by
  have hu : A₀ ∪ A₁ ⊆ B := Finset.union_subset h₀ h₁
  have hc : (A₀ ∪ A₁).card ≤ B.card := Finset.card_le_card hu
  have hi := Finset.card_union_add_card_inter A₀ A₁
  have hci : ((A₀ ∪ A₁).card : ℤ) + ((A₀ ∩ A₁).card : ℤ) =
      (A₀.card : ℤ) + (A₁.card : ℤ) := by
    exact_mod_cast hi
  omega

end MathlibPlus.GraphTheory

namespace MathlibPlus.Open.GraphTheory

/-!
Statement-fidelity formalization of admitted claim 48558.  The first clause
uses the standard hypercube on Boolean words of length `m`; `incidentEdges`
means all hypercube edges having at least one endpoint in the chosen vertex
set, while the subtracted term is the edge count of the induced subgraph.
The `C` upper bound is stated for every edge set contained in that incident
set, preserving the source's link between `C_i` and `E_Qm(V_i)`.  The second
clause states the independent finite-set intersection bound with integer
subtraction, retaining the source's ambient base-edge-set parameter.
-/

/-- The induced-edge capacity identity and upper bound for the `m`-cube,
together with the set-theoretic lower bound for two subsets of an ambient base
edge set. -/
def inducedEdgeCapacityAndIntersection : Prop :=
  (∀ (m : ℕ),
    let V := Fin m → Bool
    let Qm : SimpleGraph V :=
      SimpleGraph.fromRel (fun x y =>
        ∃ i : Fin m, x i ≠ y i ∧ ∀ j : Fin m, j ≠ i → x j = y j)
    let incidentEdges : Finset V → Finset (Sym2 V) := fun U =>
      Qm.edgeFinset.filter (fun e => (e.toFinset ∩ U).Nonempty)
    ∀ U : Finset V,
      (incidentEdges U).card =
        m * U.card - (Qm.induce (↑U : Set V)).edgeFinset.card ∧
      ∀ C : Finset (Sym2 V),
        C ⊆ incidentEdges U →
        C.card ≤ m * U.card - (Qm.induce (↑U : Set V)).edgeFinset.card) ∧
  (∀ {E : Type*} [Fintype E] [DecidableEq E]
      (A₀ A₁ B C : Finset E) (M : ℕ),
    C = A₀ ∩ A₁ →
    A₀ ⊆ B →
    A₁ ⊆ B →
    B.card = M →
    (A₀.card : ℤ) + (A₁.card : ℤ) - (M : ℤ) ≤ (C.card : ℤ))

end MathlibPlus.Open.GraphTheory
