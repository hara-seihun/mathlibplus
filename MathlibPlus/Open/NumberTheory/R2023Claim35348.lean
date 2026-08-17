import Mathlib

namespace MathlibPlus.Open.NumberTheory.R2023Claim35348

noncomputable section
open scoped BigOperators
open Classical
open Filter

/-- The same explicit pronic image used by the restricted anti-cover theorem. -/
def pronicImage (X : ℕ) : Finset ℕ :=
  (Finset.Icc 0 X).image (fun u => u * (u + 1))

def primeCountingReal (x : ℝ) : ℝ :=
  Nat.primeCounting ⌊x⌋₊

def primeInterval (a b : ℝ) : Finset ℕ :=
  (Finset.range (⌊b⌋₊ + 1)).filter (fun p =>
    Nat.Prime p ∧ a < (p : ℝ) ∧ (p : ℝ) ≤ b)

def coveredPoints (X : ℕ) (z w : ℝ)
    (b : ∀ p : ℕ, ZMod p) : Finset ℕ :=
  (pronicImage X).filter (fun y =>
    ∃ p ∈ primeInterval z w, (y : ZMod p) = b p)

def tailUnionBound (X : ℕ) (z w : ℝ) : ℝ :=
  2 * (X + 1 : ℝ) *
      (∑ p ∈ primeInterval z (2 * (X : ℝ) + 1), (1 : ℝ) / p) +
    2 * primeCountingReal (2 * (X : ℝ) + 1) +
    primeCountingReal w - primeCountingReal (2 * (X : ℝ) + 1)

/-- Claim 35348: for every fixed `0<c<1/2`, with
`N=X(X+1)+1`, `z=sqrt(N/log N)`, and `w=c X log N`, the low-prime
reciprocal sum is `o(1)`, the threshold prime count is `o(X)`, and the
large-prime count differs from `2cX` by `o(X)`.  Consequently the exact
union bound is eventually below the `X+1` points of `S_X`, uniformly over
all dependent families of one tail residue class per prime. -/
def fixedCRestrictedAntiCover_claim35348 : Prop :=
  ∀ c : ℝ, 0 < c → c < (1 / 2 : ℝ) →
    let N : ℕ → ℕ := fun X => X * (X + 1) + 1
    let z : ℕ → ℝ := fun X =>
      Real.sqrt ((N X : ℝ) / Real.log (N X : ℝ))
    let w : ℕ → ℝ := fun X =>
      c * (X : ℝ) * Real.log (N X : ℝ)
    let lowSum : ℕ → ℝ := fun X =>
      ∑ p ∈ primeInterval (z X) (2 * (X : ℝ) + 1), (1 : ℝ) / p
    let thresholdCount : ℕ → ℝ := fun X =>
      primeCountingReal (2 * (X : ℝ) + 1)
    let tailCount : ℕ → ℝ := fun X => primeCountingReal (w X)
    let bound : ℕ → ℝ := fun X =>
      tailUnionBound X (z X) (w X)
    Asymptotics.IsLittleO Filter.atTop lowSum
      (fun _ : ℕ => (1 : ℝ)) ∧
    Asymptotics.IsLittleO Filter.atTop thresholdCount
      (fun X => (X : ℝ)) ∧
    Asymptotics.IsLittleO Filter.atTop
      (fun X => tailCount X - 2 * c * (X : ℝ))
      (fun X => (X : ℝ)) ∧
    (∀ ε : ℝ, 0 < ε →
      ∀ᶠ X : ℕ in Filter.atTop,
        bound X ≤ (2 * c + ε) * (X : ℝ)) ∧
    (∀ᶠ X : ℕ in Filter.atTop,
      (pronicImage X).card = X + 1 ∧
      ∀ b : ∀ p : ℕ, ZMod p,
        ((coveredPoints X (z X) (w X) b).card : ℝ) <
          ((pronicImage X).card : ℝ) ∧
        coveredPoints X (z X) (w X) b ≠ pronicImage X)

end

end MathlibPlus.Open.NumberTheory.R2023Claim35348
