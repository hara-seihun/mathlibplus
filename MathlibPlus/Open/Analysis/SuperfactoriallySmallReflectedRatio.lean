import Mathlib

namespace MathlibPlus.Open.Analysis

open Filter

noncomputable section

/-- The Mellin transform of the two-step source, continued through its removable
singularity at zero. -/
def mellin (s : ℂ) : ℂ :=
  if s = 0 then
    Complex.log (4 : ℂ) - Complex.log (3 : ℂ)
  else
    (2 * Complex.cpow (2 : ℂ) s - Complex.cpow (3 : ℂ) s - 1) / s

/-- The reflected quotient in the admitted asymptotic claim. -/
def reflectedRatio (s : ℂ) : ℂ :=
  Complex.cpow ((2 * Real.pi : ℝ) : ℂ) s / (2 * Complex.Gamma s) *
    (mellin s / mellin (1 - s))

/-- Values of the reflected ratio on the closed complex disk of radius `1/3`
centered at the natural number `m`. -/
def reflectedDiskImage (m : ℕ) : Set ℝ :=
  {y | ∃ s : ℂ,
    ‖s - (m : ℂ)‖ ≤ (1 : ℝ) / 3 ∧ y = ‖reflectedRatio s‖}

noncomputable def reflectedDiskSup (m : ℕ) : ℝ :=
  sSup (reflectedDiskImage m)

abbrev OddNat := {m : ℕ // Odd m}

/-- The claim that the reflected ratio is uniformly superfactorially small on
large odd-centered disks. The constant `C` is the upper-bound meaning of the
`O(m)` term in the exponent. -/
def superfactoriallySmallReflectedRatio : Prop :=
  ∃ C : ℝ,
    (∀ᶠ m : OddNat in atTop,
      BddAbove (reflectedDiskImage m.1) ∧
        reflectedDiskSup m.1 ≤
          Real.exp (-(m.1 : ℝ) * Real.log (m.1 : ℝ) + C * (m.1 : ℝ))) ∧
    Tendsto
      (fun m : OddNat =>
        Real.exp (-(m.1 : ℝ) * Real.log (m.1 : ℝ) + C * (m.1 : ℝ)))
      atTop (nhds 0)

end
end MathlibPlus.Open.Analysis
