import Mathlib

namespace MathlibPlus.Open.Analysis.Claim13426

open MeasureTheory
noncomputable section

/-- The primes at or below a finite cutoff. -/
def primeCutoff (y : ℕ) : Finset ℕ :=
  (Finset.range (y + 1)).filter Nat.Prime

/-- The primorial attached to the sharp prime prefix. -/
def primorial (y : ℕ) : ℕ :=
  Finset.prod (primeCutoff y) (fun p => p)

/-- The differentiated sharp-prefix kernel from the admitted construction. -/
def sharpKernel (y : ℕ) (x : ℝ) : ℝ :=
  Finset.sum (Nat.divisors (primorial y)) (fun d =>
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        Real.rpow (d : ℝ) (-2) * Real.exp (-x / (d : ℝ)))

/-- The weighted square energy `E_y(c) = ∫₀∞ |K_y(x)|² x^(2c-1) dx`. -/
noncomputable def sharpEnergy (y : ℕ) (c : ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ),
    (sharpKernel y x) ^ 2 * Real.rpow x (2 * c - 1)

/-- The independent-phase Bohr-torus energy, in its admitted product form. -/
def bohrEnergy (y : ℕ) (c : ℝ) : ℝ :=
  Finset.prod (primeCutoff y)
    (fun p => 1 + Real.rpow (p : ℝ) (2 * c - 4))

/--
The Bohr energy stays bounded for every `c < 3/2`, while the sharp
energy diverges for `1 < c < 3/2`; hence no cutoff-independent
comparison constant exists in that edge range.
-/
def noUniformBohrDomination : Prop :=
  (∀ c : ℝ, c < (3 / 2 : ℝ) →
    ∃ M : ℝ,
      Filter.Eventually (fun y : ℕ => bohrEnergy y c ≤ M) Filter.atTop) ∧
  (∀ c : ℝ, 1 < c → c < (3 / 2 : ℝ) →
    Filter.Tendsto (fun y : ℕ => sharpEnergy y c)
      Filter.atTop Filter.atTop) ∧
  (∀ c : ℝ, 1 < c → c < (3 / 2 : ℝ) →
    ¬ ∃ C_c : ℝ,
      ∀ y : ℕ, sharpEnergy y c ≤ C_c * bohrEnergy y c)

end
end MathlibPlus.Open.Analysis.Claim13426
