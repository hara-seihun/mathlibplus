import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace MathlibPlus.Algebra.Claim53774

/-- Claim 53774: shifting every input `Y_i` by `u i²` is equivalent to
replacing the coefficient `2` by `2+u` in the displayed evaluation.  The
source writes the vector `1²,…,d²`; this formalization makes its one-based
indexing explicit. -/
theorem shiftSubstitution {R : Type*} [CommRing R] (d : ℕ) (_hd : 1 ≤ d)
    (F : (Fin d → R) → R) (X : Fin d → R) (u : R) :
    let G : (Fin d → R) → R :=
      fun Y => F (fun i => (2 : R) * ((i.1 + 1) ^ 2 : ℕ) + Y i)
    let J : R :=
      F (fun i => (2 + u) * ((i.1 + 1) ^ 2 : ℕ) + X i)
    J = G (fun i => X i + u * ((i.1 + 1) ^ 2 : ℕ)) := by
  dsimp
  congr 1
  funext i
  push_cast
  ring

end MathlibPlus.Algebra.Claim53774
