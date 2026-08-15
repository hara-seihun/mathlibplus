import MathlibPlus.Open.FormalizationBatch

namespace MathlibPlus.Open.FormalizationBatch

private noncomputable def colorOneLeftCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : GammaVertex V → Bool) : ℕ := by
  classical
  letI : Fintype (Edge V) := by
    unfold Edge
    exact Fintype.ofFinite _
  exact (Finset.univ.filter (fun e : Edge V => c (Sum.inl e) = true)).card

private noncomputable def colorOneRightCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : GammaVertex V → Bool) : ℕ := by
  classical
  letI : Fintype (Edge V) := by
    unfold Edge
    exact Fintype.ofFinite _
  exact (Finset.univ.filter (fun e : Edge V => c (Sum.inr e) = true)).card

/-- For `n ≥ 3`, a union of constraint components contains equally many
left and right edge variables, and every compatible pair has equal edge
cardinality. -/
def componentColoringsHaveEqualProjectedEdgeCounts : Prop := by
  classical
  exact ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (π : PointedLocalPermutations V),
    letI : Fintype (Edge V) := by
      unfold Edge
      exact Fintype.ofFinite _
    Fintype.card V ≥ 3 →
      (∀ c : GammaVertex V → Bool,
        IsGammaComponentColoring π c →
          colorOneLeftCount c = colorOneRightCount c) ∧
      (∀ p : SimpleLabeledGraph V × SimpleLabeledGraph V,
        RealizesPrescribedCardIsomorphisms π p.1 p.2 →
          (Finset.univ.filter (fun e : Edge V => p.1 e = true)).card =
            (Finset.univ.filter (fun e : Edge V => p.2 e = true)).card)

end MathlibPlus.Open.FormalizationBatch
