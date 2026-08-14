import Mathlib

open scoped BigOperators
open MeasureTheory

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.BatchFormalize2965And2999

/-- The coefficient of a power series at an integer Laurent index, with the
negative coefficients understood to be zero. -/
def coefficientAt (f : ℕ → ℂ) (n : ℤ) : ℂ :=
  if 0 ≤ n then (f n.toNat : ℂ) else 0

/-- The row of `{0, ..., r} \ {m}` represented by a `Fin r` index. -/
def deletedRow (r m : ℕ) (hm : m ≤ r) (i : Fin r) : Fin (r + 1) :=
  if i.1 < m then
    ⟨i.1, by omega⟩
  else
    ⟨i.1 + 1, by omega⟩

/-- The ordered source set `S_ell` from the exterior transfer. -/
def sourceColumn (r k ell : ℕ) (j : Fin r) : ℕ :=
  if j.1 < r - 1 then k + 1 + j.1 else k + r + ell

/-- Entry `(i,j)` of the exterior column `D_j` of `F(z)/(z-1/4)`. -/
def exteriorEntry (f : ℕ → ℂ) (r j : ℕ) (i : Fin (r + 1)) : ℂ :=
  ∑' q : ℕ,
    if j + 1 ≤ q then
      ((1 / 4 : ℂ) ^ (q - j - 1)) *
        coefficientAt f ((q : ℤ) - (i.1 : ℤ))
    else 0

/-- The endpoint cofactor obtained by deleting row `m`. -/
def endpointCofactor (f : ℕ → ℂ) (r k m : ℕ) (hm : m ≤ r) : ℂ :=
  Matrix.det (fun i j : Fin r =>
    exteriorEntry f r (k + j.1) (deletedRow r m hm i))

/-- The source maximal minor indexed by `S_ell`. -/
def sourceMinor (f : ℕ → ℂ) (r k ell m : ℕ) (hm : m ≤ r) : ℂ :=
  Matrix.det (fun i j : Fin r =>
    coefficientAt f
      ((sourceColumn r k ell j : ℤ) -
        (deletedRow r m hm i).1))

/-- Endpoint cofactor Cauchy--Binet expansion. -/
def claim2999 (f : ℕ → ℂ) (r k m : ℕ) (hm : m ≤ r) : Prop :=
  f 0 = 1 →
    endpointCofactor f r k m hm =
      ∑' ell : ℕ, (1 / 4 : ℂ) ^ ell * sourceMinor f r k ell m hm

/-- The first-shell function supplied by the `n = 0` case of the derivative
recurrence in the repair context. -/
def firstShellFunction (u : ℝ) : ℝ :=
  let y := Real.pi * Real.exp (2 * u)
  2 * Real.rpow Real.pi (-1 / 4) * Real.rpow y (5 / 4) * Real.exp (-y) * (2 * y - 3)

/-- The integrated first-shell transform. -/
def firstShellTransform (w : ℂ) : ℂ :=
  2 * ∫ u : ℝ in Set.Ici 0,
    (firstShellFunction u : ℂ) * Complex.cosh (w * (u : ℂ))

/-- The center of the disk in the off-axis zero claim. -/
def firstShellCenter : ℂ :=
  ((2.697151842339519632505936434737308603769 : ℝ) : ℂ) +
    ((20.62534600592171760132994578980489712729 : ℝ) : ℂ) * Complex.I

/-- The radius `10⁻²⁰` in the off-axis zero claim. -/
def firstShellRadius : ℝ :=
  (10 : ℝ) ^ (-20 : ℤ)

/-- The reported square of the center. -/
def firstShellSquareCenter : ℂ :=
  ((-418.1302698033554839499747508592091827703 : ℝ) : ℂ) +
    ((111.2593799575236268649384206820066215298 : ℝ) : ℂ) * Complex.I

/-- Off-axis zero of the integrated first shell. -/
def claim2965 : Prop :=
  Set.ncard {w : ℂ |
    w ∈ Metric.closedBall firstShellCenter firstShellRadius ∧
      firstShellTransform w = 0} = 1 ∧
    ∃ w : ℂ,
      w ∈ Metric.closedBall firstShellCenter firstShellRadius ∧
        firstShellTransform w = 0 ∧
        ∃ z : ℂ,
          z = w ^ 2 ∧
            z.im ≠ 0 ∧
              firstShellTransform (Complex.sqrt z) = 0 ∧
              dist z firstShellSquareCenter ≤
                dist (firstShellCenter ^ 2) firstShellSquareCenter +
                  (2 * ‖firstShellCenter‖ + firstShellRadius) * firstShellRadius

end MathlibPlus.Open.ResearchFormalization.BatchFormalize2965And2999

end
