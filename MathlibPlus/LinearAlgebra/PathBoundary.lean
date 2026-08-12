import Mathlib

namespace MathlibPlus.LinearAlgebra

/-- Claim 54880: on a simple path of positive length, the edge-boundary
coefficient vector is a scalar multiple of the endpoint boundary exactly when
all edge coefficients are that scalar.  The coordinates are those of the free
rational module on the distinct path vertices; a path of length `n + 1` has
`n + 2` vertex coordinates. -/
theorem pathBoundary_coefficients_claim54880
    (n : ℕ) (q : Fin (n + 1) → ℚ) (c : ℚ) (hc : 0 ≤ c) :
    let boundary : Fin (n + 2) → ℚ :=
      Fin.cases (q 0) (fun j : Fin (n + 1) =>
        Fin.lastCases (-q (Fin.last n))
          (fun i : Fin n => q i.succ - q i.castSucc) j)
    let endpoint : Fin (n + 2) → ℚ :=
      Fin.cases 1 (fun j : Fin (n + 1) =>
        Fin.lastCases (-1) (fun _ : Fin n => 0) j)
    (∀ j, boundary j = c * endpoint j) ↔ ∀ i, q i = c := by
  dsimp
  constructor
  · intro h i
    induction i using Fin.inductionOn with
    | zero =>
        have h0 := h 0
        simpa using h0
    | @succ i hi =>
        have hstep := h (Fin.succ i.castSucc)
        have hdiff : q i.succ - q i.castSucc = 0 := by
          simpa using hstep
        linarith
  · intro hq j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [hq]
    · refine Fin.lastCases ?_ (fun i => ?_) k
      · rw [Fin.cases_succ]
        rw [Fin.cases_succ]
        rw [Fin.lastCases_last]
        rw [Fin.lastCases_last]
        rw [hq (Fin.last n)]
        ring
      · simp [hq]

end MathlibPlus.LinearAlgebra
