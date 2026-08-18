import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0327Claim19896

noncomputable section

def exponentialWeightParameter (U t y : ℝ) : ℝ :=
  (1 + y) / 2 + (t / 4) * Real.log U

def reflectedLowerIndex (U : ℝ) : ℕ :=
  ⌈U / (175000000 : ℝ)⌉₊

def reflectedUpperIndex (U : ℝ) : ℕ :=
  ⌊U / (30000000 : ℝ)⌋₊

def reflectedSourceRange (U : ℝ) (c : ℕ) : Prop :=
  reflectedLowerIndex U ≤ c ∧ c ≤ reflectedUpperIndex U

def reflectedSummand (U t y : ℝ) (k : ℕ) : ℂ :=
  ((Real.sqrt U / (k : ℝ)) : ℂ) *
    Complex.exp
      (((t / 4) * (Real.log (U / (k : ℝ))) ^ 2 -
          exponentialWeightParameter U t y * Real.log (U / (k : ℝ))) : ℂ) *
    Complex.exp
      (-2 * Real.pi * Complex.I * (U : ℂ) *
        (Real.log (k : ℝ) : ℂ))

/-- The displayed reflected prefix, defined on the reflected index range by
its exact finite sum. -/
def reflectedDualPrefix (U t y : ℝ) (c : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc (reflectedLowerIndex U) c,
    reflectedSummand U t y k

/-- Claim 19896: on the positive reflected source range, the named prefix has
`k₀ = ceil(U/(1.75·10^8))` and the displayed complex summand. -/
def claim19896_reflectedDualPrefix : Prop :=
  ∀ (U t y : ℝ) (c : ℕ),
    0 < U →
    reflectedSourceRange U c →
      reflectedDualPrefix U t y c =
        ∑ k ∈ Finset.Icc (⌈U / (175000000 : ℝ)⌉₊) c,
          reflectedSummand U t y k

end

end MathlibPlus.Open.ResearchFormalization.R0327Claim19896
