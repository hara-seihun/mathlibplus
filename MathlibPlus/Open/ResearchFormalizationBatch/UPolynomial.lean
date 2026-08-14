import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalizationBatch

noncomputable section

/-- The graph on the original vertex set obtained from a selected set of original edges. -/
def selectedSpanningGraph {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A : Finset (↥G.edgeSet)) : SimpleGraph V :=
  SimpleGraph.fromRel (fun v w => ∃ e ∈ A, (e : Sym2 V) = s(v, w))

/-- The size of a connected component of a selected spanning subgraph. -/
def selectedComponentSize {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A : Finset (↥G.edgeSet))
    (C : (selectedSpanningGraph G A).ConnectedComponent) : ℕ :=
  Set.ncard {v : V | SimpleGraph.connectedComponentMk (selectedSpanningGraph G A) v = C}

/-- A monomial recording the sizes of all connected components of a spanning subgraph. -/
noncomputable def spanningComponentMonomial {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : Finset (↥G.edgeSet)) : MvPolynomial ℕ ℕ := by
  classical
  letI : Finite (selectedSpanningGraph G A).ConnectedComponent :=
    Finite.of_surjective (SimpleGraph.connectedComponentMk (selectedSpanningGraph G A)) (by
      intro C
      change ∃ a, Quot.mk _ a = C
      exact Quot.exists_rep C)
  letI := Fintype.ofFinite (selectedSpanningGraph G A).ConnectedComponent
  exact ∏ C, MvPolynomial.X (selectedComponentSize G A C)

/-- The U-polynomial as a sum over edge subsets of the spanning graph. -/
noncomputable def graphUPolynomial {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [Fintype (↥G.edgeSet)] : MvPolynomial ℕ ℕ :=
  ∑ A ∈ (Finset.univ : Finset (↥G.edgeSet)).powerset,
    spanningComponentMonomial G A

/-- Claim 38429: the U-polynomial is the spanning-subgraph component-size sum. -/
def claim_38429_spanning_subgraph_definition : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [Fintype (↥G.edgeSet)],
    graphUPolynomial G =
      ∑ A ∈ (Finset.univ : Finset (↥G.edgeSet)).powerset,
        ∏ C : (selectedSpanningGraph G A).ConnectedComponent,
          MvPolynomial.X (selectedComponentSize G A C)

/-- The two spin values on an unordered graph edge agree. -/
def spinsAgreeOnEdge {V : Type*} (σ : V → Fin 2) : Sym2 V → Prop :=
  Sym2.lift ⟨fun v w => σ v = σ w, by
    intro v w
    simp [eq_comm]⟩

/-- The number of monochromatic original edges for a spin assignment. -/
def monochromaticEdgeCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [Fintype (↥G.edgeSet)] (σ : V → Fin 2) : ℕ := by
  classical
  exact Fintype.card {e : ↥G.edgeSet // spinsAgreeOnEdge σ e}

/-- The number of vertices carrying one specified spin. -/
def spinClassSize {V : Type*} [Fintype V] (σ : V → Fin 2) (c : Fin 2) : ℕ :=
  Fintype.card {v : V // σ v = c}

/-- A spin assignment is proper precisely when no original edge is monochromatic. -/
def properTwoSpin {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (σ : V → Fin 2) : Prop :=
  ∀ e : ↥G.edgeSet, ¬ spinsAgreeOnEdge σ e

/-- The two-spin substitution of the U-polynomial. -/
noncomputable def twoSpinSubstitution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [Fintype (↥G.edgeSet)] : MvPolynomial (Fin 2) ℕ :=
  MvPolynomial.eval₂Hom (R := ℕ) (S₁ := MvPolynomial (Fin 2) ℕ) (MvPolynomial.C : ℕ →+* MvPolynomial (Fin 2) ℕ)
    (fun k : ℕ => MvPolynomial.X (0 : Fin 2) ^ k + MvPolynomial.X (1 : Fin 2) ^ k)
    (graphUPolynomial G)

/-- Claim 38439: the exact two-spin expansion of the U-polynomial. -/
def claim_38439_exact_two_spin_expansion : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [Fintype (↥G.edgeSet)],
    twoSpinSubstitution G =
      ∑ σ : V → Fin 2,
        (2 : MvPolynomial (Fin 2) ℕ) ^ monochromaticEdgeCount G σ *
          MvPolynomial.X (0 : Fin 2) ^ spinClassSize σ 0 *
          MvPolynomial.X (1 : Fin 2) ^ spinClassSize σ 1

/-- The coefficientwise characteristic-two specialization. -/
noncomputable def twoSpinSubstitutionModTwo {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [Fintype (↥G.edgeSet)] : MvPolynomial (Fin 2) (ZMod 2) :=
  MvPolynomial.eval₂Hom
      (MvPolynomial.C : ZMod 2 →+* MvPolynomial (Fin 2) (ZMod 2))
      (fun k : ℕ => MvPolynomial.X (0 : Fin 2) ^ k + MvPolynomial.X (1 : Fin 2) ^ k)
      (MvPolynomial.map (Nat.castRingHom (ZMod 2)) (graphUPolynomial G))

/-- The proper-coloring support polynomial over characteristic two. -/
noncomputable def properTwoSpinPolynomialModTwo {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [Fintype (↥G.edgeSet)] : MvPolynomial (Fin 2) (ZMod 2) := by
  classical
  exact ∑ σ : {σ : V → Fin 2 // properTwoSpin G σ},
    MvPolynomial.X (0 : Fin 2) ^ spinClassSize σ.1 0 *
      MvPolynomial.X (1 : Fin 2) ^ spinClassSize σ.1 1

/-- Claim 38472: characteristic-two support is exactly proper two-colorings. -/
def claim_38472_characteristic_two_support : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [Fintype (↥G.edgeSet)],
    (∀ σ : V → Fin 2,
      ((2 : ZMod 2) ^ monochromaticEdgeCount G σ = 0) ↔
        ∃ e : ↥G.edgeSet, spinsAgreeOnEdge σ e) ∧
    twoSpinSubstitutionModTwo G = properTwoSpinPolynomialModTwo G ∧
    (G.Connected ∧ (¬ ∃ σ : V → Fin 2, properTwoSpin G σ) →
      twoSpinSubstitutionModTwo G = 0)

/-- Swapping the two colors in a two-spin assignment. -/
def swapTwoSpin {V : Type*} (σ : V → Fin 2) : V → Fin 2 :=
  fun v => if σ v = 0 then 1 else 0

/-- Claim 38508: the two-coloring and characteristic-two formula for a tree. -/
def claim_38508_connected_tree_bipartition_formula : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [Fintype (↥T.edgeSet)],
    T.IsTree →
      ∃ (σ : V → Fin 2) (p q : ℕ),
        (∀ τ : V → Fin 2,
          properTwoSpin T τ ↔ τ = σ ∨ τ = swapTwoSpin σ) ∧
        p = spinClassSize σ 0 ∧ q = spinClassSize σ 1 ∧
        twoSpinSubstitutionModTwo T =
          MvPolynomial.X (0 : Fin 2) ^ p * MvPolynomial.X (1 : Fin 2) ^ q +
            MvPolynomial.X (0 : Fin 2) ^ q * MvPolynomial.X (1 : Fin 2) ^ p

end
end MathlibPlus.Open.ResearchFormalizationBatch
