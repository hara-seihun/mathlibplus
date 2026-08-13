import Mathlib

namespace MathlibPlus.Algebra

/-- The entry of the mixed Gram matrix in admitted claim 18397. -/
def mixedGramEntry_claim18397
    {α R : Type*} [Mul α] (C : α → R) (π : ℕ → α) (i j : ℕ) : R :=
  C (π i * π j)

/-- The mixed Gram determinant field, with the `k` by `k` minor indexed by
consecutive rows and columns. -/
def mixedGramField_claim18397
    {α R : Type*} [Mul α] [CommRing R]
    (C : α → R) (π : ℕ → α) (i j k : ℕ) : R :=
  Matrix.det (fun r s : Fin k => C (π (i + r.1) * π (j + s.1)))

end MathlibPlus.Algebra
