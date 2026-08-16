import Mathlib
import MathlibPlus.Open.ResearchFormalization.AdmittedBatch01a0015c.DiscreteStructures

namespace MathlibPlus.Open.ResearchFormalization

/-- Claim 14197: a right-of-critical-line strip point maps inside the Cayley disk,
with the corresponding inverse shell coefficient having radial rate above one. -/
def claim14197 : Prop :=
  ∀ (β γ : ℝ),
    1 / 2 < β → β < 1 →
      let ρ : ℂ := (β : ℂ) + (γ : ℂ) * Complex.I
      let wρ : ℂ := 1 - 1 / ρ
      ‖wρ‖ < 1 ∧
        ‖wρ‖⁻¹ > 1 ∧
        (∀ n : ℕ, ‖wρ⁻¹ ^ n‖ = (‖wρ‖⁻¹) ^ n)

/-- Claim 14201: the explicit conjugate-paired Cayley shell has four-step
positive spikes, intervening negative phases, and zero odd phases. -/
def claim14201 : Prop :=
  let ρ : ℂ := (4 / 5 : ℂ) - (2 / 5 : ℂ) * Complex.I
  let wρ : ℂ := 1 - 1 / ρ
  let z : ℕ → ℂ := fun n => (2 * Complex.I) ^ n + ((-2 : ℂ) * Complex.I) ^ n
  let u : ℕ → ℝ := fun n => (z n).re
  wρ = -(1 / 2 : ℂ) * Complex.I ∧
    1 / wρ = 2 * Complex.I ∧
    (∀ n : ℕ, (z n).im = 0) ∧
    (∀ k : ℕ, u (4 * k) = (2 : ℝ) ^ (4 * k + 1)) ∧
    (∀ k : ℕ, u (4 * k + 2) = -(2 : ℝ) ^ (4 * k + 3)) ∧
    (∀ k : ℕ, u (2 * k + 1) = 0) ∧
    (∀ k : ℕ, 0 < u (4 * k))

/-- Claim 14224: on the nonempty global-pairing region, pairing count is
exactly stabilizer size; its singleton value is separated from the empty
value and certifies a trivial component stabilizer. -/
def claim14224 {V C : Type*} (R S : C → Set V) : Prop :=
  let P := {σ : Equiv.Perm V // ∀ component, σ '' R component = S component}
  let Aut := {ρ : Equiv.Perm V // ∀ component, ρ '' R component = R component}
  (Nonempty P → Cardinal.mk P = Cardinal.mk Aut) ∧
    (¬ Nonempty P → Cardinal.mk P = 0) ∧
    (Cardinal.mk Aut = 1 →
      (Cardinal.mk P = 1 ↔ Nonempty P)) ∧
    (Cardinal.mk P = 1 →
      Cardinal.mk Aut = 1 ∧
        (∀ ρ : Equiv.Perm V,
          (∀ component, ρ '' R component = R component) →
            ρ = Equiv.refl V))

/-- Claim 14977: a nonzero even smooth compactly supported source away from
zero generates the stated modulation family. -/
def claim14977 (bandwidth : ℝ) : Prop :=
  ∃ η : ℝ → ℝ,
    (∃ x : ℝ, η x ≠ 0) ∧
      Function.Even η ∧
      ContDiff ℝ (⊤ : WithTop ℕ∞) η ∧
      HasCompactSupport η ∧
      Function.support η ⊆ Set.Ioo (-bandwidth) bandwidth ∧
      (∃ δ : ℝ,
        0 < δ ∧ δ < bandwidth ∧
          Function.support η ⊆
            (Set.Ioo (-bandwidth) (-δ) ∪ Set.Ioo δ bandwidth)) ∧
      (∀ ω : ℝ,
        let uω : ℝ → ℝ := fun x => η x * Real.cos (ω * x)
        Function.Even uω ∧
          ContDiff ℝ (⊤ : WithTop ℕ∞) uω ∧
          HasCompactSupport uω ∧
          uω 0 = 0)

end MathlibPlus.Open.ResearchFormalization
