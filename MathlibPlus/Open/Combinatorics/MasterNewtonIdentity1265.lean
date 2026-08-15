import Mathlib

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.Combinatorics

/-- The nodes used by the master Newton identity. -/
def newtonNode1265 (a : ℝ) (n : ℕ) : ℝ := a + n

/-- The rising factorial `(y)_k` used in the Newton identity. -/
def risingFactorial1265 (y : ℝ) (k : ℕ) : ℝ :=
  Finset.prod (Finset.range k) (fun j => y + (j : ℝ))

/-- The polynomial `Q_e(x) = ∏_{n<e}(x^2-x_n^2)`. -/
def newtonPolynomial1265 (a : ℝ) (e : ℕ) : Polynomial ℝ :=
  Finset.prod (Finset.range e)
    (fun n => Polynomial.X ^ 2 -
      Polynomial.C (newtonNode1265 a n) ^ 2)

/-- The polynomial `F_e = Q_e-Q_e(0)`. -/
def newtonRemainder1265 (a : ℝ) (e : ℕ) : Polynomial ℝ :=
  newtonPolynomial1265 a e -
    Polynomial.C ((newtonPolynomial1265 a e).eval 0)

/-- Divided difference on the successive nodes supplied by `nodes`. -/
def dividedDifference1265 (f : ℝ → ℝ) (nodes : ℕ → ℝ) (m : ℕ) : ℝ :=
  match m with
  | 0 => f (nodes 0)
  | m + 1 =>
      (dividedDifference1265 f (fun n => nodes (n + 1)) m -
          dividedDifference1265 f nodes m) /
        (nodes (m + 1) - nodes 0)
  termination_by m
  decreasing_by simp_wf; omega

/-- The divided difference `L_m` on `x_0,...,x_m`. -/
def newtonDividedDifference1265 (a : ℝ) (e m : ℕ) : ℝ :=
  dividedDifference1265
    (fun x => (newtonRemainder1265 a e).eval x)
    (newtonNode1265 a) m

/-- Master Newton identity and its normalized tail formula. -/
def masterNewtonIdentity1265 (a Y : ℝ) : Prop :=
  (∀ (e t : ℕ),
      ((0 ≤ t ∧ t ≤ e) →
        newtonDividedDifference1265 a e (e + t) =
          (Nat.choose e t : ℝ) *
            risingFactorial1265
              (2 * a + (e : ℝ) + (t : ℝ)) (e - t)) ∧
      (e < t →
        newtonDividedDifference1265 a e (e + t) = 0)) ∧
  (∀ (c d s : ℕ),
    c ≤ d →
      let e := d - c
      newtonDividedDifference1265 a e (d + s) /
          newtonDividedDifference1265 a e e =
        (Nat.choose e (c + s) : ℝ) /
          risingFactorial1265 (Y - (c : ℝ)) (c + s))

end MathlibPlus.Open.Combinatorics

end
