import Mathlib

namespace MathlibPlus.Open

open scoped BigOperators

/-- The complete homogeneous symmetric polynomial `h_n` evaluated on a finite list.
The value is zero for a positive degree on the empty list. -/
def completeHomogeneous1186 (n : ℕ) : List ℚ → ℚ
  | [] => if n = 0 then 1 else 0
  | x :: tail =>
      (Finset.range (n + 1)).sum (fun i =>
        x ^ i * completeHomogeneous1186 (n - i) tail)
termination_by xs => xs.length

/-- The flagged array from the admitted `(2,1)` minor claim. -/
def flaggedArray1186 (d : ℕ) (a : ℚ) (k : Fin (2 * d)) (j : Fin d) : ℚ :=
  let degree := 2 * (j.1 + 1)
  let width := k.1 + 1
  let vals := (List.range (k.1 + 2)).map (fun i => a + (i : ℚ))
  (width : ℚ) *
    if width ≤ degree then
      completeHomogeneous1186 (degree - width) vals
    else 0

/-- The principal row set `K_∅ = (0, ..., d-1)`. -/
def principalRows1186 (d : ℕ) (hd : 2 ≤ d) (i : Fin d) : Fin (2 * d) :=
  ⟨i.1, by omega⟩

/-- The padded partition row set `K_(2,1)`. -/
def twoOneRows1186 (d : ℕ) (hd : 2 ≤ d) (i : Fin d) : Fin (2 * d) :=
  if h : i.1 < d - 2 then
    ⟨i.1, by omega⟩
  else if h : i.1 = d - 2 then
    ⟨d - 1, by omega⟩
  else
    ⟨d + 1, by omega⟩

/-- A flagged determinant obtained by selecting a row set. -/
def flaggedDeterminant1186 (d : ℕ) (a : ℚ)
    (rows : Fin d → Fin (2 * d)) : ℚ :=
  Matrix.det (fun i j => flaggedArray1186 d a (rows i) j)

/-- The principal flagged determinant `H_∅`. -/
def principalMinor1186 (d : ℕ) (hd : 2 ≤ d) (a : ℚ) : ℚ :=
  flaggedDeterminant1186 d a (principalRows1186 d hd)

/-- The neighboring flagged minor `H_(2,1)`. -/
def twoOneMinor1186 (d : ℕ) (hd : 2 ≤ d) (a : ℚ) : ℚ :=
  flaggedDeterminant1186 d a (twoOneRows1186 d hd)

/-- The normalized variable `Y = 2a+d`. -/
def normalizedY1186 (d : ℕ) (a : ℚ) : ℚ :=
  2 * a + (d : ℚ)

/--
The admitted `(2,1)` neighboring-minor ratio, including its stated `d=2`
and `d=3` specializations.
-/
def claim1186 : Prop :=
  (∀ (d : ℕ) (hd : 2 ≤ d) (a : ℚ),
    twoOneMinor1186 d hd a / principalMinor1186 d hd a =
      ((d : ℚ) + 2) * ((d : ℚ) ^ 2 + (d : ℚ) - 3) /
        (3 * (normalizedY1186 d a - 1) * normalizedY1186 d a *
          (normalizedY1186 d a + 1))) ∧
  (∀ (a : ℚ),
    twoOneMinor1186 2 (by omega) a / principalMinor1186 2 (by omega) a =
      4 / ((normalizedY1186 2 a - 1) * normalizedY1186 2 a *
        (normalizedY1186 2 a + 1))) ∧
  (∀ (a : ℚ),
    twoOneMinor1186 3 (by omega) a / principalMinor1186 3 (by omega) a =
      15 / ((normalizedY1186 3 a - 1) * normalizedY1186 3 a *
        (normalizedY1186 3 a + 1)))

end MathlibPlus.Open
