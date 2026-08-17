import Mathlib

namespace MathlibPlus.Open.NumberTheory.R2023Claim35347

noncomputable section
open scoped BigOperators
open Classical

/-- The pronic image `S_X` in the admitted restricted residue family. -/
def pronicImage (X : ℕ) : Finset ℕ :=
  (Finset.Icc 0 X).image (fun u => u * (u + 1))

/-- The real prime-counting function, with the usual floor extension. -/
def primeCountingReal (x : ℝ) : ℝ :=
  Nat.primeCounting ⌊x⌋₊

/-- Finite prime intervals with real endpoints. -/
def primeInterval (a b : ℝ) : Finset ℕ :=
  (Finset.range (⌊b⌋₊ + 1)).filter (fun p =>
    Nat.Prime p ∧ a < (p : ℝ) ∧ (p : ℝ) ≤ b)

/-- Points of `S_X` lying in one selected residue class for at least one tail
prime.  The dependent residue family keeps the modulus attached to its prime. -/
def coveredPoints (X : ℕ) (z w : ℝ)
    (b : ∀ p : ℕ, ZMod p) : Finset ℕ :=
  (pronicImage X).filter (fun y =>
    ∃ p ∈ primeInterval z w, (y : ZMod p) = b p)

/-- The exact right-hand side of the arbitrary-tail union bound. -/
def tailUnionBound (X : ℕ) (z w : ℝ) : ℝ :=
  2 * (X + 1 : ℝ) *
      (∑ p ∈ primeInterval z (2 * (X : ℝ) + 1), (1 : ℝ) / p) +
    2 * primeCountingReal (2 * (X : ℝ) + 1) +
    primeCountingReal w - primeCountingReal (2 * (X : ℝ) + 1)

/-- Claim 35347: with `N=X(X+1)+1` and
`z=sqrt(N/log N)`, every choice of one residue class modulo each prime
`z<p≤w` covers at most the stated low-prime quadratic-fibre contribution,
the absorbed additive term, and the large-prime contribution. -/
def arbitraryTailUnionBound_claim35347 : Prop :=
  ∀ X : ℕ, 1 ≤ X →
    let N : ℕ := X * (X + 1) + 1
    let z : ℝ := Real.sqrt ((N : ℝ) / Real.log (N : ℝ))
    ∀ w : ℝ, 0 ≤ w →
      ∀ b : ∀ p : ℕ, ZMod p,
        ((coveredPoints X z w b).card : ℝ) ≤
          tailUnionBound X z w

end

end MathlibPlus.Open.NumberTheory.R2023Claim35347
