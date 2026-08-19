import MathlibPlus.Open.NumberTheory.ResearchMovingGap019ffe64

namespace MathlibPlus.Open.ResearchFormalization.R3870Claim50526

open MathlibPlus.Open.NumberTheory.ResearchFormalizationBatch019ffe64

noncomputable section

/-- The first-fold realization at the unique parity selected by the nonzero
modulo-three residues of d and v. -/
def firstFoldRealization_claim50526 : Prop :=
  ∀ d v : ℕ,
    2 ≤ d →
    3 ≤ v →
    d % 3 ≠ 0 →
    v % 3 ≠ 0 →
    ∃ p : Fin 2,
      (∀ k : ℕ,
        ((2 ^ k * d + v) % 3 = 0 ↔ k % 2 = p.val)) ∧
      (∀ q : Fin 2,
        (∀ k : ℕ,
          ((2 ^ k * d + v) % 3 = 0 ↔ k % 2 = q.val) → q = p)) ∧
      ∃ r L : ℕ,
        r % 2 = p.val ∧
        2 ^ r * d > v ∧
        (2 ^ r * d + v) / 3 - r - 3 ≥ 0 ∧
        L = (2 ^ r * d + v) / 3 - r - 3 ∧
        3 * (L + r + 3) = 2 ^ r * d + v ∧
        (∀ i : ℕ, i < r → noFoldAt d L i) ∧
        foldAt d L r ∧
        gapAt d L (r + 1) = 2 * v

end

end MathlibPlus.Open.ResearchFormalization.R3870Claim50526
