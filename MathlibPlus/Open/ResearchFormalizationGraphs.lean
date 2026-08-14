import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationGraphs

/-- Variables of the generalized-degree partition polynomial. -/
inductive PartitionVariable (m : ℕ)
  | vertex (i : Fin m)
  | edge (i : Fin m)
  | disagreement
  deriving DecidableEq

open MvPolynomial

/-- The vertex weight specified by the generalized-degree partition polynomial. -/
noncomputable def vertexWeight {m : ℕ} (s : Fin (m + 1)) :
    MvPolynomial (PartitionVariable m) ℕ :=
  if h : s = 0 then 1 else X (.vertex (s.pred h))

/-- The edge weight specified by the generalized-degree partition polynomial. -/
noncomputable def edgeWeight {m : ℕ} (s t : Fin (m + 1)) :
    MvPolynomial (PartitionVariable m) ℕ :=
  if hs : s = 0 then
    if ht : t = 0 then 1 else X .disagreement
  else if ht : t = 0 then
    X .disagreement
  else if hst : s = t then
    X (.edge (s.pred hs))
  else
    X .disagreement

/-- The weight of an unordered edge, obtained from its two endpoint states. -/
noncomputable def edgeWeightOn {V : Type*} {m : ℕ} (state : V → Fin (m + 1))
    (e : Sym2 V) : MvPolynomial (PartitionVariable m) ℕ :=
  Sym2.lift
    ⟨fun v w => edgeWeight (state v) (state w), by
      intro v w
      change edgeWeight (state v) (state w) = edgeWeight (state w) (state v)
      unfold edgeWeight
      split_ifs <;> simp_all [eq_comm]⟩ e

/-- The generalized-degree partition polynomial with the weights in the packet. -/
noncomputable def generalizedDegreePartitionPolynomial {V : Type*} [Fintype V]
    (G : SimpleGraph V) (m : ℕ) : MvPolynomial (PartitionVariable m) ℕ := by
  classical
  exact ∑ state : V → Fin (m + 1),
    (∏ v : V, vertexWeight (state v)) *
      (Finset.prod G.edgeFinset (fun e => edgeWeightOn state e))

/-- Vertices of the uniform leaf corona. -/
abbrev CoronaVertex (V : Type*) (k : ℕ) := V ⊕ (V × Fin k)

/-- Adjacency in the uniform leaf corona. -/
def leafCoronaAdj {V : Type*} {k : ℕ} (G : SimpleGraph V) :
    CoronaVertex V k → CoronaVertex V k → Prop
  | Sum.inl v, Sum.inl w => G.Adj v w
  | Sum.inl v, Sum.inr (w, _) => v = w
  | Sum.inr (v, _), Sum.inl w => v = w
  | Sum.inr _, Sum.inr _ => False

/-- Adjoining exactly k new degree-one vertices to every old vertex. -/
def leafCorona {V : Type*} (G : SimpleGraph V) (k : ℕ) :
    SimpleGraph (CoronaVertex V k) :=
  SimpleGraph.mk (leafCoronaAdj G)
    ⟨by
      intro a b hab
      cases a with
      | inl v =>
          cases b with
          | inl w => exact G.symm.symm _ _ hab
          | inr p => exact hab.symm
      | inr p =>
          cases b with
          | inl w => exact hab.symm
          | inr q => exact False.elim hab⟩
    ⟨by
      intro a haa
      cases a with
      | inl v => exact G.loopless.irrefl v haa
      | inr p => exact False.elim haa⟩

/-- Isomorphism of simple graphs on possibly different finite carriers. -/
def GraphIso {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ e : V ≃ W, ∀ v w, G.Adj v w ↔ H.Adj (e v) (e w)

/-- Claim 6524: equality of the fixed-state invariant propagates through every corona. -/
def fixedStateEqualityPropagatesThroughEveryUniformCorona : Prop :=
  ∀ (m : ℕ), 1 ≤ m →
    ∀ {V W : Type*} [Fintype V] [Fintype W]
      (T : SimpleGraph V) (T' : SimpleGraph W),
      T.IsTree → T'.IsTree →
      generalizedDegreePartitionPolynomial T m =
        generalizedDegreePartitionPolynomial T' m →
      ∀ k : ℕ,
        generalizedDegreePartitionPolynomial (leafCorona T k) m =
          generalizedDegreePartitionPolynomial (leafCorona T' k) m

/-- Claim 6526: positive uniform corona depth preserves nonisomorphism. -/
def nonisomorphismIsPreservedByPositiveUniformCorona : Prop :=
  ∀ {V W : Type*} [Fintype V] [Fintype W]
    (T : SimpleGraph V) (T' : SimpleGraph W),
    T.IsTree → T'.IsTree → ¬ GraphIso T T' →
    ∀ k : ℕ, 1 ≤ k → ¬ GraphIso (leafCorona T k) (leafCorona T' k)

end MathlibPlus.Open.ResearchFormalizationGraphs
