import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Analytic.Order
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Verified-height finite Pólya-frequency transfer

Formal statement aligned with admitted claim 456.
-/

namespace MathlibPlus.Open.NumberTheory.VerifiedHeight

/--
At the verified endpoint `T₀ = 3000175332800`, the worst-case zero-sector ratio lies
strictly between the displayed consecutive integers.  The centered completed-zeta
square-root transform is represented canonically by its even Taylor coefficients;
`PF m` means that every Toeplitz minor of order at most `m` is nonnegative.
-/
def endpointTransferOrder : Prop :=
  let T₀ : ℝ := 3000175332800
  let sectorRatio : ℝ := Real.pi / (2 * Real.arctan (1 / (2 * T₀)))
  let xi : ℂ → ℂ := fun s ↦ (1 / 2) * s * (s - 1) * completedRiemannZeta s
  let coeff : ℕ → ℂ := fun n ↦
    iteratedDeriv (2 * n) (fun z ↦ xi (1 / 2 + z)) 0 / (Nat.factorial (2 * n) : ℂ)
  let PF : ℕ → Prop := fun m ↦
    ∀ r : ℕ, 1 ≤ r → r ≤ m →
      ∀ rows cols : Fin r → ℕ, StrictMono rows → StrictMono cols →
        let minor : ℂ := Matrix.det fun i j ↦
          if rows i ≤ cols j then coeff (cols j - rows i) else 0
        minor.im = 0 ∧ 0 ≤ minor.re
  9425328785005 < sectorRatio ∧
    sectorRatio < 9425328785006 ∧
    PF 9425328785004 ∧
    ∀ m : ℕ, 0 < m → (((m + 1 : ℕ) : ℝ) ≤ sectorRatio ↔ m ≤ 9425328785004)

end MathlibPlus.Open.NumberTheory.VerifiedHeight
