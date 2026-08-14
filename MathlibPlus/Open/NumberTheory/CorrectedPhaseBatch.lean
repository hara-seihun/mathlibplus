import Mathlib

noncomputable section

namespace MathlibPlus.Open.NumberTheory

/-- Claim 21984: the primary first-range phase and real-part enclosure. -/
def claim21984 (K : ℝ) (T σ : ℝ → ℝ) : Prop :=
  ∀ R : ℝ, K ≤ R → R ≤ 2 * K →
    2999997404217 < T R ∧ T R < 11999989616869 ∧ σ R > 1.003584

/-- Claim 21986: the first three signed activation-moment ceilings. -/
def claim21986
    (K : ℝ) (ΔM₀ ΔM₁ ΔM₂ : ℤ → ℝ → ℝ) : Prop :=
  ∀ (R : ℝ) (N : ℤ), K ≤ R → R ≤ 2 * K → K < N → N < 2 * K →
    |ΔM₀ N R| < 4.078655 ∧
      |ΔM₁ N R| < 55.965896 ∧
      |ΔM₂ N R| < 768.110505 ∧
      |ΔM₀ N R| ≤ 4.078654179728205 ∧
      |ΔM₁ N R| ≤ 55.96589498553439 ∧
      |ΔM₂ N R| ≤ 768.1105039652219

/-- Claim 21988: corrected reciprocal propagation under the source lower hypothesis. -/
def claim21988 (a theta₂ T : ℝ) : Prop :=
  0 < a ∧ 0 < theta₂ ∧ 0 < T ∧
    theta₂ * T ^ (7 / 17 : ℝ) < a →
      a ^ (-36 / 41 : ℝ) * T ^ (11 / 41 : ℝ) <
        theta₂ ^ (-36 / 41 : ℝ) * T ^ (-65 / 697 : ℝ)

/-- Claim 21989: the corrected `q₀` and `E₁` denominator. -/
def claim21989
    (theta₁ theta₂ Tminus a T : ℝ) (q : ℕ) (q₀sharp dsharp : ℝ) : Prop :=
  q = Nat.floor (theta₁ * a ^ (36 / 41 : ℝ) * T ^ (-11 / 41 : ℝ)) ∧
    q₀sharp = theta₁ * theta₂ ^ (36 / 41 : ℝ) * Tminus ^ (65 / 697 : ℝ) ∧
    dsharp = theta₁ - theta₂ ^ (-36 / 41 : ℝ) * Tminus ^ (-65 / 697 : ℝ)

/-- Claim 21992: the corrected long/short-prefix bridge gives one all-prefix envelope. -/
def claim21992
    (internal : Fin 5 → ℕ) (majorant : Fin 5 → ℝ)
    (phaseBound : Fin 5 → ℕ → ℝ) (length : Fin 5 → ℕ) : Prop :=
  (∀ s : Fin 5, internal s < 128 ∧ majorant s > 60000) ∧
    (∀ s n, n ≤ length s → internal s ≤ n →
      phaseBound s n ≤ majorant s) ∧
    (∀ s n, n ≤ length s → n < internal s →
      phaseBound s n ≤ (n : ℝ)) ∧
    (∀ s n, n ≤ length s → phaseBound s n ≤ majorant s)

end MathlibPlus.Open.NumberTheory
