import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Verified-height transfer to finite Pólya frequency

Formal statement aligned with admitted claim 454.
-/

namespace MathlibPlus.Open.NumberTheory.VerifiedHeightTransfer

/--
If every nontrivial zeta zero through height `T > 1/2` lies on the critical
line, then the square-variable centered xi function is `PF_m` for every
positive order satisfying the exact sector inequality from claim 454.

The coefficients of `ξ₁` are the even Taylor coefficients of centered xi;
`PF m` means nonnegativity of every Toeplitz minor of order at most `m`.
-/
def generalFinitePFTransfer : Prop :=
  ∀ T : ℝ, 1 / 2 < T →
    let xi : ℂ → ℂ := fun s ↦
      (1 + s * (s - 1) * completedRiemannZeta₀ s) / 2
    let coeff : ℕ → ℂ := fun n ↦
      iteratedDeriv (2 * n) (fun z ↦ xi ((1 / 2 : ℂ) + z)) 0 /
        (Nat.factorial (2 * n) : ℂ)
    let PF : ℕ → Prop := fun m ↦
      ∀ r : ℕ, 1 ≤ r → r ≤ m →
        ∀ rows cols : Fin r → ℕ, StrictMono rows → StrictMono cols →
          let minor : ℂ := Matrix.det fun i j ↦
            if rows i ≤ cols j then coeff (cols j - rows i) else 0
          minor.im = 0 ∧ 0 ≤ minor.re
    (∀ ρ : ℂ, xi ρ = 0 → 0 < |ρ.im| → |ρ.im| ≤ T → ρ.re = 1 / 2) →
      ∀ m : ℕ, 0 < m →
        Real.pi / ((m + 1 : ℕ) : ℝ) ≥
          2 * Real.arctan (1 / (2 * T)) →
        PF m

end MathlibPlus.Open.NumberTheory.VerifiedHeightTransfer
