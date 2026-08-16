import Mathlib

namespace MathlibPlus.Open

noncomputable section

/-- The reversal of a polynomial, viewed at the origin as a formal power series. -/
noncomputable def reversedSeries {K : Type*} [Field K]
    (F : Polynomial K) : PowerSeries K :=
  Polynomial.toPowerSeries (Polynomial.reverse F)

/-- The ordinary degree bound `deg P ≤ m - 2`, with its negative cases explicit. -/
def degreeAtMostSubTwo {K : Type*} [Field K]
    (m : ℕ) (P : Polynomial K) : Prop :=
  match m with
  | 0 => P = 0
  | 1 => P = 0
  | n + 2 => P.degree ≤ (n : WithBot ℕ)

/-- Formal-power-series meaning of `1 + O(t^n)`. -/
def agreesThrough {K : Type*} [Field K]
    (n : ℕ) (S : PowerSeries K) : Prop :=
  PowerSeries.order (S - 1) ≥ n

/-- The all-order reversal/Padé degree-drop equivalence. -/
def reversalDegreeDropIff {K : Type*} [Field K]
    (m : ℕ) (F G : Polynomial K) : Prop :=
  F.Monic ∧ G.Monic ∧
    F.natDegree = 2 * m ∧ G.natDegree = 2 * m →
      (degreeAtMostSubTwo m (F - G) ↔
        agreesThrough (m + 2)
          (reversedSeries F * PowerSeries.inv (reversedSeries G)))

end
end MathlibPlus.Open
