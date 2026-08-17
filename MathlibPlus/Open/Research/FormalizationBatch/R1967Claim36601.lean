import MathlibPlus.Open.Research.LiteralQuotientFormalizationBatch

namespace MathlibPlus.Open.Research.FormalizationBatch.R1967Claim36601

open MathlibPlus.Open.Research.LiteralQuotient
open scoped BigOperators

noncomputable def translationStabilizer {n : ℕ} {i : Fin n}
    (g : Omega n i → Bool) : AddSubgroup (Omega n i) :=
  sSup {K : AddSubgroup (Omega n i) |
    ∀ k ∈ K, ∀ x : Omega n i, g (x + k) = g x}

def affineHyperplane {r : ℕ} (A : Set (Fin r → F2)) : Prop :=
  ∃ ell : (Fin r → F2) →ₗ[F2] F2,
    ∃ b : F2, ell ≠ 0 ∧ A = {x | ell x = b}

def hyperplanePlusOneQuotientTier {n r : ℕ}
    (f : EdgeFunctions n) (H : Finset (Fin n)) : Prop :=
  ∀ i : {i : Fin n // i ∈ H},
    ∃ g : (Omega n i.1 ⧸ translationStabilizer (f i.1)) → Bool,
      ∃ e : (Omega n i.1 ⧸ translationStabilizer (f i.1)) ≃+
          (Fin r → F2),
        ∃ A : Set (Fin r → F2),
          ∃ m : Fin r → F2,
            affineHyperplane A ∧
              m ∉ A ∧
              (∀ x : Omega n i.1,
                f i.1 x =
                  g (QuotientAddGroup.mk
                    (s := translationStabilizer (f i.1)) x)) ∧
              (∀ y, g y = true ↔ e y ∈ A ∪ {m})

noncomputable def tierExcess {n : ℕ} (f : EdgeFunctions n)
    (H : Finset (Fin n)) : ℝ :=
  ∑ i ∈ H, (density (f i) - (1 / 2 : ℝ))

/-- Claim 36601: the literal hypercube direction functions on their omitted-
coordinate basepoint spaces, in a lossless hyperplane-plus-one translation
quotient tier, have per-direction excess `1/q`; the tier sum and its exact
source bound are stated together. -/
noncomputable def claim36601 : Prop :=
  ∀ (n r : ℕ),
    2 ≤ r →
      ∀ f : EdgeFunctions n,
        literalC4Free f →
          ∀ H : Finset (Fin n),
            hyperplanePlusOneQuotientTier (r := r) f H →
              let q : ℕ := 2 ^ r
              (∀ i ∈ H,
                density (f i) - (1 / 2 : ℝ) = 1 / (q : ℝ)) ∧
                tierExcess f H = (H.card : ℝ) / (q : ℝ) ∧
                (H.card : ℝ) / (q : ℝ) ≤
                  ((q : ℝ) ^ 2 - 2 * (q : ℝ) + 2) / 2 ∧
                tierExcess f H ≤
                  ((q : ℝ) ^ 2 - 2 * (q : ℝ) + 2) / 2

end MathlibPlus.Open.Research.FormalizationBatch.R1967Claim36601
