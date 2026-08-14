import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2.O0084

noncomputable section

def squarefree (n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → ¬p ^ 2 ∣ n

local instance : DecidablePred squarefree := fun n => Classical.propDecidable (squarefree n)

def mobiusValue (n : ℕ) : ℤ :=
  if squarefree n then (-1 : ℤ) ^ (n.primeFactors.card) else 0

/-- The finite prime set `P_y` from the admitted statement. -/
def primeCutoff (y : ℕ) : Finset ℕ :=
  (Finset.range (y + 1)).filter Nat.Prime

/-- The primorial `Q_y`. -/
def primorial (y : ℕ) : ℕ :=
  ∏ p ∈ primeCutoff y, p

/-- The rank `r_y = |P_y|`. -/
def primorialRank (y : ℕ) : ℕ :=
  (primeCutoff y).card

/-- Divisors of a positive natural, written without relying on a divisor API. -/
def divisorsOf (q : ℕ) : Finset ℕ :=
  (Finset.range (q + 1)).filter (fun d => d ∣ q)

/-- The finite Möbius complement sum. -/
def primorialComplement (y : ℕ) (t : ℝ) : ℝ :=
  ∑ d ∈ divisorsOf (primorial y),
    (mobiusValue d : ℝ) * Real.exp (-((d : ℝ) * t))

/-- The action of the finite product of `(I-D_p)` on `e^{-t}`, expanded over
subsets.  The subset expansion is the exact finite operator product. -/
def differenceProductOnExponential (y : ℕ) (t : ℝ) : ℝ :=
  ∑ S ∈ (primeCutoff y).powerset,
    (-1 : ℝ) ^ S.card *
      Real.exp (-((∏ p ∈ S, p : ℕ) : ℝ) * t)

/-- Claim 13384: the primorial, its rank, and its finite complement data are
represented on the exact finite prime/divisor carriers, with the Möbius sum
agreeing with the `(I-D_p)` product. -/
def claim13384 : Prop :=
  ∀ (y : ℕ) (t : ℝ),
    primorialRank y = (primeCutoff y).card ∧
      primorial y = ∏ p ∈ primeCutoff y, p ∧
      primorialComplement y t = differenceProductOnExponential y t

end

end MathlibPlus.Open.NewResearch2.O0084
