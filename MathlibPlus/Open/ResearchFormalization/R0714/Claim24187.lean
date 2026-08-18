import MathlibPlus.Open.ResearchFormalization.R0714.Claim24184

namespace MathlibPlus.Open.ResearchFormalization.R0714

open scoped Classical

noncomputable section

private noncomputable def ordinaryQuadraticMatrix (n : ℕ) (F : GraphType n) :
    Matrix (GraphType n × GraphType n) (ExtensionFiber n F) ℚ :=
  fun KP G =>
    (oneCard n KP.1 G.1 : ℚ) * (oneCard n KP.2 G.1 : ℚ)

private noncomputable def ordinaryQuadraticFullColumnRank
    (n : ℕ) (F : GraphType n) : Prop :=
  letI : Fintype (ExtensionFiber n F) := Fintype.ofFinite _
  fullColumnRank (ordinaryQuadraticMatrix n F)

/-- Claim 24187: the complete ordinary quadratic deck-product matrix has full
rational column rank on every one-vertex extension fibre for card orders two
through seven. -/
def claim24187 : Prop :=
  ∀ n : ℕ, 2 ≤ n → n ≤ 7 → ∀ F : GraphType n,
    ordinaryQuadraticFullColumnRank n F

end

end MathlibPlus.Open.ResearchFormalization.R0714
