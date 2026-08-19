import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0088Claim17841

open scoped BigOperators

private def sortedMaximalMinor {r n : ℕ} {K : Type*} [Field K]
    (M : Matrix (Fin r) (Fin n) K) (J : Fin r → Fin n) : K :=
  Matrix.det (M.submatrix id J)

private def fourDistinct (a b c d : Fin n) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d

/-- Claim 17841: for the four sorted maximal minors obtained from a common
`(r-2)`-set and four distinct outside columns, the balanced Plücker ratio is
unchanged by an invertible left row transformation and arbitrary nonzero
column scalings. -/
def balancedPluckerRatioInvariant_claim17841 : Prop :=
  ∀ (r n : ℕ) (K : Type*) [Field K]
    (A : Matrix (Fin r) (Fin r) K) (M : Matrix (Fin r) (Fin n) K)
    (w : Fin n → K)
    (I : Finset (Fin n)) (a b c d : Fin n)
    (J₁ J₂ J₃ J₄ : Fin r → Fin n),
    I.card = r - 2 →
    fourDistinct a b c d →
    a ∉ I → b ∉ I → c ∉ I → d ∉ I →
    StrictMono J₁ → StrictMono J₂ → StrictMono J₃ → StrictMono J₄ →
    Finset.image J₁ Finset.univ = insert a (insert c I) →
    Finset.image J₂ Finset.univ = insert b (insert d I) →
    Finset.image J₃ Finset.univ = insert a (insert b I) →
    Finset.image J₄ Finset.univ = insert c (insert d I) →
    Matrix.det A ≠ 0 →
    (∀ j : Fin n, w j ≠ 0) →
    Multiset.map J₁ (Finset.univ : Finset (Fin r)).1 +
          Multiset.map J₂ (Finset.univ : Finset (Fin r)).1 =
        Multiset.map J₃ (Finset.univ : Finset (Fin r)).1 +
          Multiset.map J₄ (Finset.univ : Finset (Fin r)).1 ∧
    (let Δ : Matrix (Fin r) (Fin n) K → (Fin r → Fin n) → K :=
      fun N J => sortedMaximalMinor N J
     Δ (A * (M * Matrix.diagonal w)) J₁ *
          Δ (A * (M * Matrix.diagonal w)) J₂ /
          (Δ (A * (M * Matrix.diagonal w)) J₃ *
            Δ (A * (M * Matrix.diagonal w)) J₄) =
       Δ M J₁ * Δ M J₂ /
          (Δ M J₃ * Δ M J₄))

end MathlibPlus.Open.ResearchFormalization.R0088Claim17841
