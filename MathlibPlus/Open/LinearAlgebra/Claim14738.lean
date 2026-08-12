import MathlibPlus.Open.Basic

open scoped BigOperators Matrix

namespace MathlibPlus.Open.LinearAlgebra.Claim14738

/--
Claim 14738.  This closed node uses the concrete real-variable families from
the packet, with complex coefficients.  The two spans are represented by the
three displayed basis functions; separated rank is the exact Nat infimum of
finite rank-one summand decompositions.  The final clause records invariance
under invertible coefficient-basis changes.  No unspecified analytic
function-space object is introduced.
-/
def separationRankEqualsCoefficientMatrixRank : Prop :=
  let u : Fin 3 → ℝ → ℂ := fun i =>
    if i = 0 then (fun _ => 1)
    else if i = 1 then (fun x => Real.cosh x)
    else fun x => Real.sinh x
  let v : Fin 3 → ℝ → ℂ := fun i =>
    if i = 0 then (fun _ => 1)
    else if i = 1 then (fun x => Real.cos x)
    else fun x => Real.sin x
  LinearIndependent ℂ u ∧ LinearIndependent ℂ v ∧
    ∀ M : Matrix (Fin 3) (Fin 3) ℂ,
      let R : ℝ → ℝ → ℂ := fun x y =>
        ∑ i, ∑ j, u i x * M i j * v j y
      (sInf {n : ℕ | ∃ f : Fin n → ℝ → ℂ, ∃ g : Fin n → ℝ → ℂ,
        ∀ x y, R x y = ∑ r, f r x * g r y} = Matrix.rank M) ∧
      (∀ P Q : Matrix (Fin 3) (Fin 3) ℂ,
        IsUnit P.det → IsUnit Q.det →
        Matrix.rank (P * M * Q) = Matrix.rank M)

end MathlibPlus.Open.LinearAlgebra.Claim14738
