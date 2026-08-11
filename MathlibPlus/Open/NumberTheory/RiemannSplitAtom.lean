import Mathlib

open scoped BigOperators ComplexConjugate

namespace MathlibPlus.Open.NumberTheory.CompletedZeta

/--
Registry obligation for admitted claim 244.  `upperGamma z x` is the upper
incomplete gamma integral `Γ(z,x)`.  Naturals are indexed by `k + 1`, so no
zero term is introduced into the packet's sum over `n ≥ 1`.
-/
def riemannSplitIncompleteGammaAtom : Prop :=
  let upperGamma : ℂ → ℝ → ℂ := fun z x =>
    ∫ t in Set.Ici x,
      Complex.exp (-(t : ℂ)) * Complex.cpow (t : ℂ) (z - 1)
  let xi : ℂ → ℂ := fun s =>
    (1 + s * (s - 1) * completedRiemannZeta₀ s) / 2
  let atom : ℕ → ℂ → ℂ := fun n s =>
    s * (s - 1) / 2 *
      (((Real.pi : ℂ) ^ (-s / 2)) *
          upperGamma (s / 2) (Real.pi * n ^ 2) * (n : ℂ) ^ (-s) +
        ((Real.pi : ℂ) ^ (-(1 - s) / 2)) *
          upperGamma ((1 - s) / 2) (Real.pi * n ^ 2) *
            (n : ℂ) ^ (s - 1)) +
      (((4 * Real.pi * n ^ 2 - 1 : ℝ) *
        Real.exp (-Real.pi * n ^ 2) : ℝ) : ℂ)
  (∀ s : ℂ, Summable (fun k : ℕ => atom (k + 1) s) ∧
      ∑' k : ℕ, atom (k + 1) s = xi s) ∧
    Summable (fun k : ℕ =>
      (4 * Real.pi * (k + 1) ^ 2 - 1) *
        Real.exp (-Real.pi * (k + 1) ^ 2)) ∧
    (∑' k : ℕ,
      (4 * Real.pi * (k + 1) ^ 2 - 1) *
        Real.exp (-Real.pi * (k + 1) ^ 2)) = 1 / 2

end MathlibPlus.Open.NumberTheory.CompletedZeta
