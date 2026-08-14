import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatch019ffedd3a89746fb3037ba0172c78b8

section PairedNorm

noncomputable def pairedNorm (a A B : ℝ) : ℝ :=
  (1 - a) * sSup {r : ℝ | ∃ z : ℂ, ‖z‖ = 1 ∧
    r = ‖(B : ℂ) + z * (A : ℂ)‖ / ‖(1 : ℂ) + z * (a : ℂ)‖}

def claim_21397 : Prop :=
  ∀ (A B a : ℝ), 0 ≤ a → a < 1 →
    pairedNorm a A B =
      max |B - A| (((1 - a) / (1 + a)) * |B + A|)

def claim_21398 : Prop :=
  ∀ (A B a t : ℝ), 0 ≤ a → a < 1 →
    pairedNorm a (t * A) (t * B) = |t| * pairedNorm a A B

def claim_21399 : Prop :=
  ∀ (A₁ B₁ A₂ B₂ a : ℝ), 0 ≤ a → a < 1 →
    pairedNorm a (A₁ + A₂) (B₁ + B₂) ≤
      pairedNorm a A₁ B₁ + pairedNorm a A₂ B₂

end PairedNorm

end MathlibPlus.Open.Research.FormalizationBatch019ffedd3a89746fb3037ba0172c78b8
