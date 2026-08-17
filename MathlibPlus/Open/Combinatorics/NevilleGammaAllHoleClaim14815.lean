import MathlibPlus.Open.Combinatorics.GammaDarbouxFirstVerticalRatioClaim14814

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.Combinatorics.NevilleGamma

/-- The real rising factorial used for the all-hole closed form. -/
def risingFactorialReal14815 (x : ℝ) (k : ℕ) : ℝ :=
  Finset.prod (Finset.range k) (fun j => x + (j : ℝ))

/-- The odd double factorial `(2 n - 1)!!`. -/
def oddDoubleFactorial14815 (n : ℕ) : ℝ :=
  Finset.prod (Finset.range n) (fun j => ((2 * j + 1 : ℕ) : ℝ))

/-- The vertical ratio formed from the exact gamma--Darboux Neville
multiplier. -/
def gammaVerticalRatio14815 (α : ℝ) (c : ℕ) : ℝ :=
  gammaDarbouxNevilleMultiplier α (c + 2) c /
    gammaDarbouxNevilleMultiplier α (c + 1) c

/-- The all-hole interaction as the finite product of inverse vertical ratios,
with the exact range `c = 0, ..., n - 2`. -/
def gammaAllHoleInteraction14815 (α : ℝ) (n : ℕ) : ℝ :=
  Finset.prod (Finset.range (n - 1))
    (fun c => (gammaVerticalRatio14815 α c)⁻¹ ^ (n - 1 - c))

/-- The displayed factorization of the gamma--Darboux all-hole interaction. -/
def gammaAllHoleFormula14815 (α : ℝ) (n : ℕ) : ℝ :=
  (((Nat.factorial n : ℝ) * (4 : ℝ) ^ (n - 1) *
      risingFactorialReal14815 ((5 : ℝ) / 4) (n - 1)) /
    oddDoubleFactorial14815 n) *
    (((α + 1) ^ (n - 1) * Real.Gamma (α + 2)) /
      Real.Gamma (α + (n : ℝ) + 1))

/-- Claim 14815: the exact all-hole vertical-ratio product telescopes to the
stated gamma--Darboux closed form. -/
def claim14815 : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    ∀ (α : ℝ), -1 < α →
      gammaAllHoleInteraction14815 α n = gammaAllHoleFormula14815 α n

end MathlibPlus.Open.Combinatorics.NevilleGamma

end
