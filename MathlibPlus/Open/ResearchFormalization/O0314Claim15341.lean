import Mathlib

open scoped BigOperators ComplexConjugate

namespace MathlibPlus.Open.ResearchFormalization.O0314

noncomputable section

/-- The explicit symmetric-divisor counterfeit: the exact functional-equation,
real-type, order-one, counting, phase, and normal-flux data agree for the line
and off-line completed pair, while their nontrivial divisors differ. -/
def claim15341 : Prop :=
  ∀ (a b : ℝ),
    0 < a → a < 1 / 2 → 0 < b →
    (∀ k : ℤ, b ≠ (k : ℝ) + 1 / 2) →
    let Eline : ℂ → ℂ := fun z =>
      (z ^ 2 + (b : ℂ) ^ 2) ^ 2
    let Eoff : ℂ → ℂ := fun z =>
      (z ^ 2 - ((a : ℂ) + (b : ℂ) * Complex.I) ^ 2) *
        (z ^ 2 - ((a : ℂ) - (b : ℂ) * Complex.I) ^ 2)
    let Xline : ℂ → ℂ := fun s =>
      Complex.cosh (Real.pi * (s - (1 / 2 : ℂ))) *
        Eline (s - (1 / 2 : ℂ))
    let Xoff : ℂ → ℂ := fun s =>
      Complex.cosh (Real.pi * (s - (1 / 2 : ℂ))) *
        Eoff (s - (1 / 2 : ℂ))
    let C : ℂ → ℂ := fun s =>
      (1 / 2 : ℂ) * s * (s - 1) *
        (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)
    let χ : ℂ → ℂ := fun s =>
      (Real.pi : ℂ) ^ (s - (1 / 2 : ℂ)) *
        Complex.Gamma ((1 - s) / 2) / Complex.Gamma (s / 2)
    let Fline : ℂ → ℂ := fun s => Xline s / C s
    let Foff : ℂ → ℂ := fun s => Xoff s / C s
    let thetaPrime : ℝ → ℝ := fun t =>
      (1 / 2 : ℝ) *
          (Complex.digamma ((1 / 4 : ℂ) + (t : ℂ) * Complex.I / 2)).re -
        (1 / 2 : ℝ) * Real.log Real.pi
    let orderOne : (ℂ → ℂ) → Prop := fun f =>
      (∃ K : ℝ, 0 < K ∧
        ∀ s : ℂ, ‖f s‖ ≤ K * Real.exp (K * ‖s‖)) ∧
      (∀ ρ : ℝ, 0 ≤ ρ → ρ < 1 →
        ∀ K : ℝ, 0 < K →
          ∃ s : ℂ,
            K * Real.exp (K * Real.rpow ‖s‖ ρ) < ‖f s‖)
    let upperStrip : (ℂ → ℂ) → ℝ → Set ℂ := fun f T =>
      {s | f s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 < s.im ∧ s.im ≤ T}
    let zeroMultiplicity : (ℂ → ℂ) → ℂ → ℕ := fun f s =>
      sInf {n : ℕ | iteratedDeriv n f s ≠ 0}
    let zeroCount : (ℂ → ℂ) → ℝ → ℕ := fun f T =>
      ∑' s : {s : ℂ // s ∈ upperStrip f T}, zeroMultiplicity f s.1
    let Ncosh : ℝ → ℕ := fun T =>
      zeroCount (fun s : ℂ => Complex.cosh (Real.pi * (s - (1 / 2 : ℂ)))) T
    (Differentiable ℂ Xline ∧ Differentiable ℂ Xoff) ∧
      (Meromorphic Fline ∧ Meromorphic Foff) ∧
      (∀ s : ℂ,
        Xline (star s) = star (Xline s) ∧
        Xoff (star s) = star (Xoff s) ∧
        Fline (star s) = star (Fline s) ∧
        Foff (star s) = star (Foff s)) ∧
      (∀ s : ℂ,
        Xline s = Xline (1 - s) ∧
        Xoff s = Xoff (1 - s)) ∧
      (∀ s : ℂ, C (1 - s) = χ s * C s) ∧
      (∀ s : ℂ,
        Fline s = χ s * Fline (1 - s) ∧
        Foff s = χ s * Foff (1 - s)) ∧
      (orderOne Xline ∧ orderOne Xoff) ∧
      (∀ T : ℝ, 0 ≤ T →
        zeroCount Fline T = zeroCount Foff T ∧
        zeroCount Fline T = Ncosh T + 2 * (if T ≥ b then 1 else 0)) ∧
      (∀ s : ℂ,
        Fline s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2) ∧
      (Foff ((1 / 2 + a : ℂ) + (b : ℂ) * Complex.I) = 0 ∧
        Foff ((1 / 2 - a : ℂ) + (b : ℂ) * Complex.I) = 0 ∧
        ((1 / 2 + a : ℂ) + (b : ℂ) * Complex.I).re ≠ 1 / 2 ∧
        ((1 / 2 - a : ℂ) + (b : ℂ) * Complex.I).re ≠ 1 / 2) ∧
      (∀ t : ℝ,
        Fline (1 / 2 + (t : ℂ) * Complex.I) ≠ 0 →
        Foff (1 / 2 + (t : ℂ) * Complex.I) ≠ 0 →
        (deriv Fline (1 / 2 + (t : ℂ) * Complex.I) /
            Fline (1 / 2 + (t : ℂ) * Complex.I)).re = -thetaPrime t ∧
        (deriv Foff (1 / 2 + (t : ℂ) * Complex.I) /
            Foff (1 / 2 + (t : ℂ) * Complex.I)).re = -thetaPrime t ∧
        (deriv (fun u : ℝ =>
              Fline (1 / 2 + (u : ℂ) * Complex.I)) t /
            Fline (1 / 2 + (t : ℂ) * Complex.I)).im = -thetaPrime t ∧
        (deriv (fun u : ℝ =>
              Foff (1 / 2 + (u : ℂ) * Complex.I)) t /
            Foff (1 / 2 + (t : ℂ) * Complex.I)).im = -thetaPrime t)

end
end MathlibPlus.Open.ResearchFormalization.O0314
