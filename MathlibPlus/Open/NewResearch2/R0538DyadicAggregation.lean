import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2.R0538

/-- Claim 22426: the aligned-block hypotheses give the signed dyadic prefix bound,
with the stated fixed value of the number of scales. -/
def claim22426 : Prop :=
  (∀ (M J : ℕ),
      J = Nat.ceil (Real.log ((M : ℝ) + 1) / Real.log 2) →
        ∀ (a : Fin M → ℝ) (B : Fin J → ℝ),
          (∀ (j : Fin J) (k : ℕ)
              (hblock : k * 2 ^ (j : ℕ) + 2 ^ (j : ℕ) ≤ M),
                Finset.sum Finset.univ
                  (fun r : Fin (2 ^ (j : ℕ)) =>
                    a ⟨k * 2 ^ (j : ℕ) + r, by
                      have hr : (r : ℕ) < 2 ^ (j : ℕ) := r.isLt
                      exact Nat.lt_of_lt_of_le
                        (Nat.add_lt_add_left hr _) hblock⟩) ≤ B j) →
            ∀ (n : Fin (M + 1)),
              Finset.sum Finset.univ
                  (fun r : Fin (n : ℕ) => a ⟨r, by
                    exact Nat.lt_of_lt_of_le r.isLt
                      (Nat.lt_succ_iff.mp n.isLt)⟩) ≤
                Finset.sum Finset.univ (fun j : Fin J => max (B j) 0)) ∧
    Nat.ceil (Real.log ((139309012 : ℝ) + 1) / Real.log 2) = 28

/-- Claim 22427: one selected dyadic block per scale is bounded in a
positive-semidefinite Gram seminorm by the stated Hilbert/Gram remainder bound.
This proposition concerns the Hessian remainder; it makes no replacement of a
signed directional linear contraction. -/
def claim22427 : Prop :=
  ∀ (d J : ℕ), 0 < J →
    ∀ (G : Matrix (Fin d) (Fin d) ℝ),
      (∀ v : Fin d → ℝ, 0 ≤ ∑ i : Fin d, v i * (G.mulVec v) i) →
        ∀ (E : Fin J → ℝ) (selected : Finset (Fin J))
          (block : Fin J → (Fin d → ℝ)),
          (∀ j : Fin J, 0 ≤ E j) →
            (∀ j ∈ selected,
                (Real.sqrt (∑ i : Fin d, block j i * (G.mulVec (block j)) i)) ^ 2 ≤ E j) →
              Real.sqrt
                  (∑ i : Fin d,
                    (Finset.sum selected (fun j => block j)) i *
                      (G.mulVec (Finset.sum selected (fun j => block j))) i) ≤
                Real.sqrt (J : ℝ) *
                  Real.sqrt (Finset.sum Finset.univ (fun j : Fin J => E j))

end MathlibPlus.Open.NewResearch2.R0538
