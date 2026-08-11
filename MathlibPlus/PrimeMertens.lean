import Mathlib

/-!
# Reciprocal-prime Mertens error

Exact definitions from Record 1 of legacy extraction bundle `C-0039`.  The
computational extremum and tail-certificate claims from later records are not
asserted here.
-/

namespace MathlibPlus.PrimeMertens

noncomputable section

/-- The finite reciprocal-prime sum `∑_{p ≤ x} 1 / p`.

For negative `x`, `Nat.floor x = 0`, so the sum is empty. -/
def reciprocalPrimeSum (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.range (Nat.floor x + 1)).filter Nat.Prime, ((p : ℝ)⁻¹)

/-- A real number is the Meissel--Mertens constant when it is the limiting
constant in the reciprocal-prime asymptotic. -/
def IsMeisselMertensConstant (B : ℝ) : Prop :=
  Filter.Tendsto
    (fun n : ℕ => reciprocalPrimeSum n - Real.log (Real.log n))
    Filter.atTop (nhds B)

/-- The reciprocal-prime Mertens error `A₁(x)`. -/
def mertensError (B x : ℝ) : ℝ :=
  reciprocalPrimeSum x - Real.log (Real.log x) - B

/-- The scale-normalized error `E₁(x) = A₁(x) log² x`. -/
def normalizedUpperError (B x : ℝ) : ℝ :=
  mertensError B x * Real.log x ^ 2

/-- The packet's candidate sharp same-range upper coefficient, sampled at
`x = 286`. -/
def sharpCoefficient (B : ℝ) : ℝ :=
  normalizedUpperError B 286

/-- The defining formula for the coefficient at the packet's cutoff. -/
theorem sharpCoefficient_formula (B : ℝ) :
    sharpCoefficient B =
      (reciprocalPrimeSum 286 - Real.log (Real.log 286) - B) *
        Real.log 286 ^ 2 := rfl

end

end MathlibPlus.PrimeMertens
