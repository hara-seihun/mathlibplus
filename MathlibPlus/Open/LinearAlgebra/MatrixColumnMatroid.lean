import Mathlib

namespace MathlibPlus.Open.LinearAlgebra

/-- A square matrix represents the column matroid of its columns, whose full
rank is the finite dimension of the span of all columns and agrees with the
matrix rank. -/
def matrixColumnMatroidFullRank
    (K : Type*) [Field K] (ι : Type*) [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) : Prop :=
  ∃ M : Matroid ι,
    M.E = Set.univ ∧
      (∀ S : Set ι,
        M.Indep S ↔
          LinearIndependent K (fun j : S => fun i : ι => A i j)) ∧
      Module.finrank K
          (Submodule.span K (Set.range (fun j : ι => fun i : ι => A i j))) =
        A.rank

end MathlibPlus.Open.LinearAlgebra
