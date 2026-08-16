import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open

/-- The three-dimensional vector space over `𝔽_p`, with the cyclic index set
`ZMod 3` making the indices modulo `3` explicit. -/
abbrev Fp3 (p : ℕ) := ZMod 3 → ZMod p

/-- The scalar function `δ(t) = t^(p-1)` from the admitted claim. -/
def delta (p : ℕ) (t : ZMod p) : ZMod p :=
  t ^ (p - 1)

/-- The cyclic map in Claim 60722. -/
def F_cyc (p : ℕ) (x : Fp3 p) : Fp3 p :=
  fun i => delta p (x i) * x (i + 1)

/-- The all-other-coordinates map in Claim 60722. -/
def F_all (p : ℕ) (x : Fp3 p) : Fp3 p :=
  fun i =>
    ∑ j ∈ (Finset.univ.filter (fun j : ZMod 3 => j ≠ i)),
      delta p (x i) * x j

/-- The weighted map in Claim 60722. -/
def F_wt (p : ℕ) (x : Fp3 p) : Fp3 p :=
  fun i => delta p (x i) * (x (i + 1) + 2 * x (i + 2))

/-- Coordinate polynomials for the displayed maps. -/
abbrev Poly3 (p : ℕ) := MvPolynomial (ZMod 3) (ZMod p)

noncomputable def cycPolynomial (p : ℕ) (i : ZMod 3) : Poly3 p :=
  (MvPolynomial.X i) ^ (p - 1) * MvPolynomial.X (i + 1)

noncomputable def allPolynomial (p : ℕ) (i : ZMod 3) : Poly3 p :=
  ∑ j ∈ (Finset.univ.filter (fun j : ZMod 3 => j ≠ i)),
    (MvPolynomial.X i) ^ (p - 1) * MvPolynomial.X j

noncomputable def wtPolynomial (p : ℕ) (i : ZMod 3) : Poly3 p :=
  (MvPolynomial.X i) ^ (p - 1) *
    (MvPolynomial.X (i + 1) + 2 * MvPolynomial.X (i + 2))

/-- Oddness of a map on the additive vector space `𝔽_p^3`. -/
def IsOddMap {p : ℕ} (F : Fp3 p → Fp3 p) : Prop :=
  ∀ x, F (-x) = -F x

/-- Exact degree `p` of a displayed coordinate-polynomial map. -/
def HasCoordinateDegreeP (p : ℕ) (F : Fp3 p → Fp3 p)
    (q : ZMod 3 → Poly3 p) : Prop :=
  (∀ x i, F x i = MvPolynomial.eval x (q i)) ∧
    ∀ i, (q i).totalDegree = p

/-- The stated zero/nonzero values of `δ`. -/
def DeltaHasFrobeniusValues (p : ℕ) : Prop :=
  delta p 0 = 0 ∧ ∀ t : ZMod p, t ≠ 0 → delta p t = 1

/--
Claim 60722: for `p ∈ {5, 7}`, the three displayed maps on
`A = B = 𝔽_p^3` are odd degree-`p` maps fixing `0`.
-/
def claim_60722 : Prop :=
  ∀ p : ℕ, (p = 5 ∨ p = 7) →
    DeltaHasFrobeniusValues p ∧
      IsOddMap (F_cyc p) ∧
      HasCoordinateDegreeP p (F_cyc p) (fun i => cycPolynomial p i) ∧
      F_cyc p 0 = 0 ∧
      IsOddMap (F_all p) ∧
      HasCoordinateDegreeP p (F_all p) (fun i => allPolynomial p i) ∧
      F_all p 0 = 0 ∧
      IsOddMap (F_wt p) ∧
      HasCoordinateDegreeP p (F_wt p) (fun i => wtPolynomial p i) ∧
      F_wt p 0 = 0

end MathlibPlus.Open
