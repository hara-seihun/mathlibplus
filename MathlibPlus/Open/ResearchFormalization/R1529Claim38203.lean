import MathlibPlus.Open.ResearchFormalization.R1529Claim38235

namespace MathlibPlus.Open.ResearchFormalization.R1529Claim38203

open MathlibPlus.Open.ResearchFormalization.R1529Claim38235

/-- Claim 38203: after the exact global normalization of every odd-prime
    blockwise affine chart, the only equal-copy profiles are the nonzero
    alternating translations, and every other normalized chart lies in the
    ordered binary two-closure. -/
def claim38203 : Prop :=
  ∀ (q : ℕ) [NeZero q],
    Nat.Prime q →
      q % 2 = 1 →
        Nat.card (NormalizedAffineProfile q) =
            (q * (q - 1)) ^ 7 ∧
          Nat.card {p : NormalizedAffineProfile q // equalCopyProfile q p} =
            q - 1 ∧
            (∀ p : NormalizedAffineProfile q,
              equalCopyProfile q p ↔ alternatingTranslationProfile q p) ∧
            (∀ p : NormalizedAffineProfile q,
              ¬ equalCopyProfile q p → inOrderedTwoClosure q p.1)

end MathlibPlus.Open.ResearchFormalization.R1529Claim38203
