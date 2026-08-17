import MathlibPlus.Open.ResearchFormalizationGraphs

namespace MathlibPlus.Open.ResearchFormalizationGraphs

/-- Claim 6525: positive uniform leaf coronas expose exactly their old vertices
through the degree threshold, and every corona isomorphism restricts along
that exposed summand to an isomorphism of the original trees. -/
def originalVertexCoreOfNontrivialCorona_claim6525 : Prop :=
  (∀ {V : Type*} [Fintype V] [Nontrivial V]
      (T : SimpleGraph V),
      T.IsTree →
      ∀ k : ℕ, 1 ≤ k →
        ∀ x : CoronaVertex V k,
          Nat.card ((leafCorona T k).neighborSet x) ≥ 2 ↔
            ∃ v : V, x = Sum.inl v) ∧
    (∀ {V W : Type*} [Fintype V] [Fintype W]
        [Nontrivial V] [Nontrivial W]
        (T : SimpleGraph V) (T' : SimpleGraph W),
        T.IsTree → T'.IsTree →
        ∀ k : ℕ, 1 ≤ k →
          ∀ (e : CoronaVertex V k ≃ CoronaVertex W k),
            (∀ x y,
              (leafCorona T k).Adj x y ↔
                (leafCorona T' k).Adj (e x) (e y)) →
              ∃ f : V ≃ W,
                (∀ v : V, e (Sum.inl v) = Sum.inl (f v)) ∧
                  ∀ v w : V,
                    T.Adj v w ↔ T'.Adj (f v) (f w))

end MathlibPlus.Open.ResearchFormalizationGraphs
