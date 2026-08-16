import MathlibPlus.AffineGap.ProjectivePeano

/-!
# All-rank projective Peano identity

Registry statement for admitted claim 85 from source record `C-0005`.
-/

namespace MathlibPlus.Open.AffineGap

/-- All-rank projective Peano identity: the affine determinant at strictly ordered
knots is the consecutive-gap integral of the transversal tangent determinant. -/
def allRankProjectivePeano : Prop :=
  ∀ (n : ℕ) (γ : ℝ → Fin n → ℝ) (q : Fin (n + 1) → ℝ),
    ContDiffOn ℝ 1 γ (Set.Icc (q 0) (q (Fin.last n))) → StrictMono q →
      MathlibPlus.AffineGap.ProjectivePeano.affineSampleDet γ q =
        MathlibPlus.AffineGap.ProjectivePeano.consecutiveGapTangentIntegral γ q

end MathlibPlus.Open.AffineGap
