import Mathlib

namespace MathlibPlus.Open.LinearAlgebra

/--
The arithmetic projective matrix is the projective evaluation matrix of the
logarithmic-derivative curve, with the displayed row formulas and the
projective determinant transformation under reindexing of the sampled points.
-/
def arithmeticProjectiveMatrix_claim4967 : Prop :=
  ∀ {Q R : Type} [Field R] (d : ℕ)
    (K : Q → R) (D : (Q → R) → Q → R)
    (q : Fin (d + 1) → Q) (π : Equiv.Perm (Fin (d + 1))),
    let γK : Q → Fin d → R :=
      fun x j => ((D^[j.1 + 1]) K) x / K x
    let P : Matrix (Fin (d + 1)) (Fin (d + 1)) R :=
      fun r i => Fin.cases 1 (fun j => γK (q i) j) r
    (∀ i, P 0 i = 1) ∧
      (∀ (j : Fin d) i,
        P j.succ i = ((D^[j.1 + 1]) K) (q i) / K (q i)) ∧
      Matrix.det (P.submatrix id π) =
        (↑↑(Equiv.Perm.sign π) : R) * Matrix.det P

end MathlibPlus.Open.LinearAlgebra
