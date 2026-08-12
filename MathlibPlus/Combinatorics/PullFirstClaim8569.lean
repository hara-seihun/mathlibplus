import Mathlib

open scoped BigOperators

namespace MathlibPlus.Combinatorics.Claim8569

/-- The Vandermonde product on a finite selected set of nodes. -/
def vandermondeOn {n : ℕ} (x : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  S.prod (fun i => (S.filter (fun j => i < j)).prod (fun j => x j - x i))

/-- The discrete OPE partition function from claim 8569. -/
noncomputable def partitionFunction (n k : ℕ) (x u : Fin n → ℝ) : ℝ :=
  ((Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card = k)).sum
    (fun S => vandermondeOn x S ^ 2 * S.prod u)

/-- The empty-sector normalization `Z₀(u)=1`. -/
theorem partitionFunction_zero_claim8569 (n : ℕ) (x u : Fin n → ℝ) :
    partitionFunction n 0 x u = 1 := by
  classical
  have hfilter :
      ((Finset.univ : Finset (Finset (Fin n))).filter
          (fun S => S.card = 0)) = {∅} := by
    ext S
    simp
  unfold partitionFunction
  rw [hfilter]
  simp [vandermondeOn]

end MathlibPlus.Combinatorics.Claim8569
