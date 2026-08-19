import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim31498

/--
A nonzero coordinate of a right-kernel vector excludes the corresponding
coordinate row from the row span of a finite matrix.
-/
def coordinateRow_not_mem_rowSpan : Prop :=
  ∀ {ι κ K : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] [Field K]
    (M : Matrix ι κ K) (w : κ → K) (j : κ),
    Matrix.mulVec M w = 0 →
    w j ≠ 0 →
    Pi.single j (1 : K) ∉
      Submodule.span K (Set.range (fun i => M i))

end MathlibPlus.LinearAlgebra.Claim31498
