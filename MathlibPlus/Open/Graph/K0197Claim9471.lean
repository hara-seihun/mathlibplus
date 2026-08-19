import MathlibPlus.Open.Graph.Claim9464

namespace MathlibPlus.Open.Graph.K0197Claim9471

open MathlibPlus.Open.Graph.Claim9464
open MathlibPlus.Open.Graph.AdmittedClaim9463
open Classical

noncomputable section

/-- Being a star of maximum size in the ambient spanning edge carrier. -/
def starOfMaximumSize9471 {n : ℕ}
    (Y : SimpleGraph (Fin n)) (A : Finset (Sym2 (Fin n))) : Prop :=
  ∃ c : Fin n,
    A = MathlibPlus.Open.Graph.AdmittedClaim9463.edgeStar Y c ∧
      A.card = Y.maxDegree

/-- Claim 9471: under the non-universal maximum-degree bound, every valid
maximum-size star-first pair is the maximum-degree star and its deleted card. -/
def topStarLayerIsPure_claim9471 : Prop :=
  ∀ {n : ℕ} (Y : SimpleGraph (Fin n)),
    Y.maxDegree ≤ n - 2 →
      ∀ A : Finset (Sym2 (Fin n)),
        validPart Y A →
          starOfMaximumSize9471 Y A →
            ∃ c : Fin n,
              Y.degree c = Y.maxDegree ∧
                A = MathlibPlus.Open.Graph.AdmittedClaim9463.edgeStar Y c ∧
                thetaPair Y A =
                  (edgePartType
                      (MathlibPlus.Open.Graph.AdmittedClaim9463.edgeStar Y c),
                    deletedCardType Y c)

end

end MathlibPlus.Open.Graph.K0197Claim9471
