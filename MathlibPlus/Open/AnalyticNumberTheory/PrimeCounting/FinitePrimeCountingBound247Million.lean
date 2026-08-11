import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

noncomputable section

/-!
# Finite prime-counting bound through 247 million

Statement-fidelity registry node for admitted claim 756.  The 26,501
consecutive blocks are represented by one-based prime-index endpoints, and the
reported least slack is written as an exact rational.
-/

/-- The finite-range C-0048 bound and its 26,501-block certificate. -/
def finitePrimeCountingBound247Million : Prop :=
  let primeAtIndex : ℕ → ℕ := fun i => Nat.nth Nat.Prime (i - 1)
  let primeCountingReal : ℝ → ℕ := fun x => Nat.primeCounting (Nat.floor x)
  let F : ℝ → ℝ := fun x =>
    let L := Real.log x
    x / L + x / L ^ 2 + 2 * x / L ^ 3 +
      ((3012167 : ℝ) / 500000) * x / L ^ 4 +
      24 * x / L ^ 5 + 120 * x / L ^ 6 +
      720 * x / L ^ 7 + ((30486 : ℝ) / 5) * x / L ^ 8
  (∀ x : ℝ, 1 < x → x ≤ 247000000 →
      (primeCountingReal x : ℝ) < F x) ∧
    ∃ firstIndex lastIndex : Fin 26501 → ℕ,
      primeAtIndex 15 = 47 ∧
      firstIndex 0 = 15 ∧
      (∀ k : Fin 26501, 1 ≤ firstIndex k ∧ firstIndex k ≤ lastIndex k) ∧
      (∀ k : Fin 26500,
        firstIndex k.succ = lastIndex k.castSucc + 1) ∧
      (∀ k : Fin 26501,
        F (primeAtIndex (firstIndex k)) - lastIndex k >
            (2500108 : ℝ) / 10000000 ∧
          ∀ x : ℝ,
            (primeAtIndex (firstIndex k) : ℝ) ≤ x →
            x < primeAtIndex (lastIndex k + 1) →
            (primeCountingReal x : ℝ) < F x) ∧
      (primeAtIndex (firstIndex (Fin.last 26500)) : ℝ) ≤ 247000000 ∧
      (247000000 : ℝ) < primeAtIndex (lastIndex (Fin.last 26500) + 1) ∧
      (∀ x : ℝ, 2 ≤ x → x ≤ 47 →
        (primeCountingReal x : ℝ) < F x)

end

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
