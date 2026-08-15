import Mathlib

namespace MathlibPlus.Open.Analysis

/-- The one-sided Toeplitz extension of a coefficient sequence, including its
negative-index zero convention. -/
def extendedCoefficient8195 (f : ℕ → ℝ) (n : ℤ) : ℝ :=
  if 0 ≤ n then f n.toNat else 0

/-- A one-sided Toeplitz matrix entry. -/
def toeplitzEntry8195 (f : ℕ → ℝ) (r c : ℕ) : ℝ :=
  extendedCoefficient8195 f (Int.ofNat c - Int.ofNat r)

/-- The first `p - 1` rows viewed as rows of a `p` by `p` minor. -/
def predecessorRow8195 {p : ℕ} (i : Fin (p - 1)) : Fin p :=
  ⟨i.1, lt_of_lt_of_le i.2 (Nat.sub_le p 1)⟩

/-- The columns consisting of the first `p - 1` selected columns followed by
an arbitrary future column `N`. -/
def columnsWithFuture8195 {p : ℕ} (c : Fin (p - 1) → ℕ)
    (N : ℕ) (j : Fin p) : ℕ :=
  if h : j.1 < p - 1 then c ⟨j.1, h⟩ else N

/-- The nested order `p - 1` Toeplitz minor. -/
def nestedMinor8195 {p : ℕ} (f : ℕ → ℝ) (r : Fin p → ℕ)
    (c : Fin (p - 1) → ℕ) : ℝ :=
  Matrix.det (fun i j =>
    toeplitzEntry8195 f (r (predecessorRow8195 i)) (c j))

/-- The future order `p` Toeplitz minor `D_N`. -/
def futureMinor8195 {p : ℕ} (f : ℕ → ℝ) (r : Fin p → ℕ)
    (c : Fin (p - 1) → ℕ) (N : ℕ) : ℝ :=
  Matrix.det (fun i j =>
    toeplitzEntry8195 f (r i) (columnsWithFuture8195 c N j))

/-- The column indexed by `N`, restricted to the selected rows `R`. -/
def restrictedFutureColumn8195 {p : ℕ} (f : ℕ → ℝ)
    (r : Fin p → ℕ) (N : ℕ) : Fin p → ℝ :=
  fun i => toeplitzEntry8195 f (r i) N

/-- A concrete analytic meaning of the generating function in the claim. -/
def generatingFunction8195 (f : ℕ → ℝ) (F : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, HasSum (fun n : ℕ => (f n : ℂ) * z ^ n) (F z)

/-- A concrete meaning of a rational complex-valued function. -/
def rationalFunction8195 (F : ℂ → ℂ) : Prop :=
  ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧ ∀ z : ℂ, Q.eval z * F z = P.eval z

/-- A concrete meaning of a polynomial complex-valued function. -/
def polynomialFunction8195 (F : ℂ → ℂ) : Prop :=
  ∃ P : Polynomial ℂ, ∀ z : ℂ, F z = P.eval z

/--
If all future minors vanish while the nested minor is positive, the future
columns restricted to `R` occupy one fixed `(p - 1)`-dimensional subspace,
which supplies a nonzero constant-coefficient eventual recurrence.  That
recurrence makes the generating function rational, and an entire such
function is polynomial.
-/
def eventualRecurrenceForcesRationality8195 : Prop :=
  ∀ (f : ℕ → ℝ) (F : ℂ → ℂ) (p : ℕ)
    (r : Fin p → ℕ) (c : Fin (p - 1) → ℕ) (c_p : ℕ),
    0 < p →
    StrictMono r →
    StrictMono c →
    (∀ j : Fin (p - 1), c j < c_p) →
    0 < nestedMinor8195 f r c →
    (∀ N : ℕ, c_p < N → futureMinor8195 f r c N = 0) →
    ∃ V : Submodule ℝ (Fin p → ℝ),
      Module.finrank ℝ V = p - 1 ∧
      (∀ N : ℕ, c_p < N → restrictedFutureColumn8195 f r N ∈ V) ∧
      (∃ lambda : Fin p → ℝ,
        lambda ≠ 0 ∧
        ∀ N : ℕ, c_p < N →
          ∑ j : Fin p, lambda j *
            extendedCoefficient8195 f
              (Int.ofNat N - Int.ofNat (r j)) = 0) ∧
      (generatingFunction8195 f F →
        rationalFunction8195 F ∧
          (Differentiable ℂ F → polynomialFunction8195 F))

end MathlibPlus.Open.Analysis
