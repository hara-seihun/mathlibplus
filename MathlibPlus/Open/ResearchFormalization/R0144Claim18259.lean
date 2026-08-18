import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0144Claim18259

noncomputable section

private def rankPartition (r : ℕ) (part : YoungDiagram) : Prop :=
  part.colLen 0 ≤ r

private def exteriorJetIndex
    (r : ℕ) (part : YoungDiagram) (j : Fin r) : ℕ :=
  j.1 + part.rowLen (r - 1 - j.1)

private def evenIndexAdmissible
    (r : ℕ) (part : YoungDiagram) : Prop :=
  ∀ j : Fin r, Even (exteriorJetIndex r part j)

private noncomputable def exteriorPacket
    (c : ℕ → ℝ → ℕ → ℝ) (r : ℕ) (part : YoungDiagram)
    (t : ℝ) (I : Fin r → ℕ) : ℝ :=
  Matrix.det (fun i j : Fin r => c (exteriorJetIndex r part j) t (I i))

private def staircaseSize (r : ℕ) : ℕ :=
  r * (r - 1) / 2

private def staircaseShape (r : ℕ) (part : YoungDiagram) : Prop :=
  ∀ i : ℕ,
    part.rowLen i = if i < r then r - (i + 1) else 0

private def gaugeNormalizedJet (c : ℕ → ℝ → ℕ → ℝ) : Prop :=
  ∀ j : ℕ, ∀ t : ℝ, ∀ n : ℕ,
    HasDerivAt (fun s : ℝ => c j s n) (c (j + 1) t n) t

private def packetVanishingOrInadmissible
    (c : ℕ → ℝ → ℕ → ℝ) (r : ℕ) (part : YoungDiagram)
    (I : Fin r → ℕ) : Prop :=
  ¬ evenIndexAdmissible r part ∨ exteriorPacket c r part 0 I = 0

/-- Claim 18259: the even-index packet support starts at the staircase of
    size `r(r-1)/2`, with lower rank-compatible shapes either inadmissible or
    represented by a vanishing concrete exterior determinant. -/
def claim18259_firstAdmissibleSurvivingStaircase
    (c : ℕ → ℝ → ℕ → ℝ) : Prop :=
  gaugeNormalizedJet c →
    ∀ r : ℕ, 1 ≤ r →
      (∀ (I : Fin r → ℕ) (part : YoungDiagram),
        rankPartition r part →
        part.card < staircaseSize r →
        packetVanishingOrInadmissible c r part I) ∧
      ∃ δ : YoungDiagram,
        staircaseShape r δ ∧
          rankPartition r δ ∧
          evenIndexAdmissible r δ ∧
          δ.card = staircaseSize r

end

end MathlibPlus.Open.ResearchFormalization.R0144Claim18259
