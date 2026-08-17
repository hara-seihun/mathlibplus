import MathlibPlus.Open.Combinatorics.R0392BooleanTrade

open Classical
open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0392BooleanMobiusClaim20827

noncomputable section

/-- Claim 20827: after the proper Boolean margins are fixed, the exact
nonempty cells are the integral Möbius transforms of those margins and the
single top parameter `t = m_[r] = x_[r]`. -/
def claim20827 : Prop :=
  ∀ (r q : ℕ)
    (x : MathlibPlus.Open.Combinatorics.R0392.BooleanTable r)
    (m : Finset (Fin r) → ℕ) (t : ℕ),
    MathlibPlus.Open.Combinatorics.R0392.naturalTotal x = q →
      (∀ T : Finset (Fin r),
        T.Nonempty →
          T ≠ (Finset.univ : Finset (Fin r)) →
            m T = MathlibPlus.Open.Combinatorics.R0392.naturalMargin x T) →
        m (Finset.univ : Finset (Fin r)) = t →
          (x (Finset.univ : Finset (Fin r)) : ℤ) = t →
            ∀ S : Finset (Fin r),
              S.Nonempty →
                (x S : ℤ) =
                  Finset.sum
                    ((MathlibPlus.Open.Combinatorics.R0392.booleanCells r).filter
                      (fun T => S ⊆ T))
                    (fun T =>
                      (-1 : ℤ) ^ (T.card - S.card) *
                        (if T = (Finset.univ : Finset (Fin r)) then
                          (t : ℤ)
                        else
                          (m T : ℤ)))

end

end MathlibPlus.Open.ResearchFormalization.R0392BooleanMobiusClaim20827
