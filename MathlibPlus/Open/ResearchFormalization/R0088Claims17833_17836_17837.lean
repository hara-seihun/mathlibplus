import MathlibPlus.Open.ResearchFormalization.R0088Claim17838

namespace MathlibPlus.Open.ResearchFormalization.R0088Claims17833_17836_17837

open MathlibPlus.Open.ResearchFormalization.R0088Claim17838

/-- Claim 17833: normalized derivatives of the product curve act on the
length-`m` jet block by right multiplication by the normalized upper-triangular
Leibniz block. -/
def normalizedLeibnizAction_claim17833 : Prop :=
  ∀ (d m : ℕ) (q : ℝ → ℝ) (v : ℝ → (Fin d → ℝ)) (a : ℝ),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v →
    normalizedJetBlock (scalarMultiplyCurve q v) m a =
      normalizedJetBlock v m a * leibnizBlock q m a

/-- Claim 17836: for a smooth scalar factor positive at every confluent
anchor, the exact canonical confluent determinant has the displayed positive
scale and preserves both full determinant signs. -/
def positiveScalarPreservesConfluentOrientation_claim17836 : Prop :=
  ∀ (d r : ℕ) (q : ℝ → ℝ) (v : ℝ → (Fin d → ℝ))
    (anchors : Fin r → ℝ) (μ : Fin r → ℕ)
    (e : ConfluentIndex r μ ≃ Fin d),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v →
    (∀ i : Fin r, 0 < q (anchors i)) →
    preservesConfluentOrientation q v anchors μ e

/-- Claim 17837: the exact spectral change has `z + 1/4 = p(1-p)`;
the Green factor is positive on the open unit interval, its actual Leibniz
blocks are upper triangular with the displayed positive diagonal, and the
resulting scalar multiplication preserves the relevant osculating flags and
full confluent determinant signs. -/
def greenPolynomialFlagPreservation_claim17837 : Prop :=
  (∀ p : ℝ,
    let z := p * (1 - p) - 1 / 4
    z + 1 / 4 = p * (1 - p)) ∧
  (∀ p : ℝ, 0 < p → p < 1 → 0 < p * (1 - p)) ∧
  (∀ (m : ℕ) (a : ℝ), 0 < a → a < 1 →
    (∀ i j : Fin m, j < i →
      leibnizBlock (fun p : ℝ => p * (1 - p)) m a i j = 0) ∧
    (∀ i : Fin m,
      leibnizBlock (fun p : ℝ => p * (1 - p)) m a i i = a * (1 - a) ∧
        0 < leibnizBlock (fun p : ℝ => p * (1 - p)) m a i i)) ∧
  (∀ (d m : ℕ) (v : ℝ → (Fin d → ℝ)) (a : ℝ),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v →
    0 < a → a < 1 →
    ∀ k : ℕ, k ≤ m →
      osculatingSubspace
          (scalarMultiplyCurve (fun p : ℝ => p * (1 - p)) v) k a =
        osculatingSubspace v k a) ∧
  (∀ (d r : ℕ) (v : ℝ → (Fin d → ℝ))
      (anchors : Fin r → ℝ) (μ : Fin r → ℕ)
      (e : ConfluentIndex r μ ≃ Fin d),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v →
    (∀ i : Fin r, 0 < anchors i ∧ anchors i < 1) →
    preservesConfluentOrientation (fun p : ℝ => p * (1 - p))
      v anchors μ e)

end MathlibPlus.Open.ResearchFormalization.R0088Claims17833_17836_17837
