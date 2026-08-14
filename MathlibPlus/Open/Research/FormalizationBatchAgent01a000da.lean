import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatchAgent01a000da

private def xorGraph {V : Type*} (G H : SimpleGraph V) : SimpleGraph V :=
  { Adj := fun u v => Xor (G.Adj u v) (H.Adj u v)
    symm := ⟨by
      intro u v huv
      rcases huv with ⟨hG, hH⟩ | ⟨hH, hG⟩
      · exact Or.inl ⟨(G.adj_comm u v).mp hG,
          fun h => hH ((H.adj_comm v u).mp h)⟩
      · exact Or.inr ⟨(H.adj_comm u v).mp hH,
          fun h => hG ((G.adj_comm v u).mp h)⟩⟩
    loopless := ⟨by
      intro u huv
      rcases huv with ⟨hG, _⟩ | ⟨hH, _⟩
      · exact G.loopless.irrefl u hG
      · exact H.loopless.irrefl u hH⟩ }

private def starAt {V : Type*} (G : SimpleGraph V) (v : V) : SimpleGraph V :=
  { Adj := fun x y => G.Adj x y ∧ (x = v ∨ y = v)
    symm := ⟨by
      intro x y h
      refine ⟨(G.adj_comm x y).mp h.1, ?_⟩
      exact h.2.elim (fun hx => Or.inr hx) (fun hy => Or.inl hy)⟩
    loopless := ⟨by
      intro x h
      exact G.loopless.irrefl x h.1⟩ }

private def remainingAt {V : Type*} (G : SimpleGraph V) (v : V) : SimpleGraph V :=
  { Adj := fun x y => G.Adj x y ∧ x ≠ v ∧ y ≠ v
    symm := ⟨by
      intro x y h
      exact ⟨(G.adj_comm x y).mp h.1, h.2.2, h.2.1⟩⟩
    loopless := ⟨by
      intro x h
      exact G.loopless.irrefl x h.1⟩ }

/-- Claim 21220: common-mask factorization of a target. -/
def commonMaskFactorization : Prop :=
  ∀ (n : ℕ) (C : SimpleGraph (Fin n)) (u v : Fin n),
    (∀ w, ∃ z, C.Adj w z) →
    (∃ x y, x ≠ y ∧ ¬ C.Adj x y) →
    (u ≠ v ∧ ¬ C.Adj u v) →
    ∀ (M : SimpleGraph (Fin n)),
      (∀ x y, M.Adj x y →
        x ≠ u ∧ x ≠ v ∧ y ≠ u ∧ y ≠ v) →
      let A := xorGraph (starAt C v) M
      let B := xorGraph (remainingAt C v) M
      (∃ w, ∀ z, ¬ A.Adj w z) ∧
        (∃ w, ∀ z, ¬ B.Adj w z) ∧
        xorGraph A B = C

end MathlibPlus.Open.Research.FormalizationBatchAgent01a000da
