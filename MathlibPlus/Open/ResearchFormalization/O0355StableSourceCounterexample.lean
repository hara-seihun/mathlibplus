import Mathlib

open scoped BigOperators
open Filter Topology Set

namespace MathlibPlus.Open.ResearchFormalization

noncomputable section

/--
Claim 15633: the complete-multiplicative degree-one Euler-product family from
O-0355 has arbitrarily long literal zeta prefixes, positive prime-power
weights, convergent signed source data with zero total mass, natural-order
convergence, and a Vinogradov--Korobov prime-number theorem, while its fixed
symmetric quartet remains off the critical line with order `m`.
-/
def completeMultiplicativityPlusStableSourceDataDoesNotControlDivisor15633 : Prop :=
  let PrimeIndex := {p : ℕ // Nat.Prime p}
  let PositiveExponent := {k : ℕ // 1 ≤ k}
  let PrimePowerIndex := PrimeIndex × PositiveExponent
  let sourceTerm : (ℕ → ℝ) → PrimePowerIndex → ℝ := fun a q =>
    ((a q.1.1) ^ q.2.1 - 1) * Real.log (q.1.1 : ℝ) /
      (q.1.1 : ℝ) ^ q.2.1
  let primePowerWeight : (ℕ → ℝ) → PrimePowerIndex → ℝ := fun a q =>
    (a q.1.1) ^ q.2.1 * Real.log (q.1.1 : ℝ)
  let weightedPrimeCountReal : (ℕ → ℝ) → ℝ → ℝ := fun a x =>
    ∑' q : PrimePowerIndex,
      if (q.1.1 : ℝ) ^ q.2.1 ≤ x then primePowerWeight a q else 0
  let zetaPrimeCountReal : ℝ → ℝ := fun x =>
    ∑' q : PrimePowerIndex,
      if (q.1.1 : ℝ) ^ q.2.1 ≤ x then Real.log (q.1.1 : ℝ) else 0
  let degreeOneEulerProduct : (ℕ → ℝ) → ℂ → ℂ := fun a s =>
    ∏' p : PrimeIndex,
      (1 - (a p.1 : ℂ) *
        Complex.exp (-(s * (Real.log (p.1 : ℝ) : ℂ))))⁻¹
  let vkError : ℝ → ℝ → ℝ := fun c x =>
    x * Real.exp (-(c * Real.rpow (Real.log x) ((3 : ℝ) / 5) *
      Real.rpow (Real.log (Real.log x)) (-(1 : ℝ) / 5)))
  let criticalLinePure : (ℂ → ℂ) → Prop := fun F =>
    ∀ s : ℂ, 0 < s.re → s.re < 1 → F s = 0 → s.re = (1 : ℝ) / 2
  ∀ (α : ℝ),
    Irrational α →
    0 < α →
    α < (1 : ℝ) / 2 →
    ∃ E : Set ℝ,
      E.Countable ∧
        E ⊆ {t : ℝ | 0 < t} ∧
        ∀ (τ : ℝ),
          0 < τ →
          τ ∉ E →
          ∀ (m : ℕ),
            1 ≤ m →
            ∃ (Y₀ : ℕ) (a : ℕ → ℕ → ℝ) (L : ℕ → ℂ → ℂ)
                (u : ℕ → ℝ) (Cᵤ Ctv : ℝ),
              1 ≤ Y₀ ∧
                0 < Cᵤ ∧
                0 < Ctv ∧
                let η : ℂ := (α : ℂ) - (τ : ℂ) * Complex.I
                let ρ : ℂ := 1 - η
                let shifts : Fin 4 → ℂ :=
                  ![η, (starRingEnd ℂ) η, ρ, (starRingEnd ℂ) ρ]
                let A : Set ℂ :=
                  {η, (starRingEnd ℂ) η, ρ, (starRingEnd ℂ) ρ}
                let baseline : PrimeIndex → ℝ := fun p =>
                  1 - 2 * (m : ℝ) *
                    (Real.rpow (p.1 : ℝ) (-α) +
                      Real.rpow (p.1 : ℝ) (-(1 - α))) *
                    Real.cos (τ * Real.log (p.1 : ℝ))
                A.ncard = 4 ∧
                  Set.range shifts = A ∧
                  (∀ z ∈ A, (starRingEnd ℂ) z ∈ A) ∧
                  (∀ z ∈ A, 1 - z ∈ A) ∧
                  (∀ z ∈ A,
                    0 < z.re ∧ z.re < 1 ∧ z.re ≠ (1 : ℝ) / 2) ∧
                  (Tendsto
                    (fun Y : ℕ =>
                      ∑' q : PrimePowerIndex, |sourceTerm (a Y) q|)
                    atTop (𝓝 0)) ∧
                  (∀ Y : ℕ, Y₀ ≤ Y →
                    |u Y| ≤ Cᵤ * Real.rpow (Y : ℝ) (-α) ∧
                    (∀ n : ℕ, 0 < a Y n) ∧
                    a Y 1 = 1 ∧
                    (∀ r s : ℕ, a Y (r * s) = a Y r * a Y s) ∧
                    (∀ p : PrimeIndex, a Y p.1 =
                      if Y < p.1 ∧ p.1 ≤ 2 * Y then baseline p + u Y
                      else if p.1 ≤ Y then 1 else baseline p) ∧
                    (∀ p : PrimeIndex, p.1 ≤ Y → a Y p.1 = 1) ∧
                    (∀ p : PrimeIndex, ∀ k : PositiveExponent,
                      a Y (p.1 ^ k.1) = (a Y p.1) ^ k.1 ∧
                        0 < primePowerWeight (a Y) (p, k)) ∧
                    (∀ s : ℂ, 1 < s.re →
                      L Y s = degreeOneEulerProduct (a Y) s) ∧
                    MeromorphicOn (L Y) {s : ℂ | 0 < s.re} ∧
                    Summable
                      (fun q : PrimePowerIndex => |sourceTerm (a Y) q|) ∧
                    (∑' q : PrimePowerIndex, |sourceTerm (a Y) q|) ≤
                      Ctv * Real.rpow (Y : ℝ) (-α) ∧
                    (∑' q : PrimePowerIndex, sourceTerm (a Y) q) = 0 ∧
                    Tendsto
                      (fun X : ℕ =>
                        ∑' q : PrimePowerIndex,
                          if q.1.1 ^ q.2.1 ≤ X then
                            sourceTerm (a Y) q else 0)
                      atTop (𝓝 0) ∧
                    (∃ Cψ Xψ : ℝ,
                      0 < Cψ ∧
                        1 ≤ Xψ ∧
                        ∀ x : ℝ, Xψ ≤ x →
                          |weightedPrimeCountReal (a Y) x -
                              zetaPrimeCountReal x| ≤
                            Cψ * Real.rpow x (1 - α)) ∧
                    (∃ cvk Cvk Xvk : ℝ,
                      0 < cvk ∧
                        0 < Cvk ∧
                        Real.exp 1 < Xvk ∧
                        ∀ x : ℝ, Xvk ≤ x →
                          |weightedPrimeCountReal (a Y) x - x| ≤
                            Cvk * vkError cvk x) ∧
                    (∀ s₀ : ℂ, s₀ ∈ A →
                      L Y s₀ = 0 ∧
                        ∃ g : ℂ → ℂ,
                          AnalyticAt ℂ g s₀ ∧
                            g s₀ ≠ 0 ∧
                            ∀ᶠ s in 𝓝 s₀,
                              L Y s = (s - s₀) ^ m * g s) ∧
                    ¬ criticalLinePure (L Y))

end

end MathlibPlus.Open.ResearchFormalization
