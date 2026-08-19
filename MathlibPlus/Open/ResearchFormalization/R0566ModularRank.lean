import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0566ModularRank

/-- Claim 22777: a full-column-rank reduction of an integer matrix modulo one
prime supplies a nonzero maximal minor over the integers and hence over the
rationals, as well as full rational column rank. -/
def modularFullColumnRank_claim22777 : Prop :=
  ∀ (r c p : ℕ) (A : Matrix (Fin r) (Fin c) ℤ),
    Nat.Prime p →
      LinearIndependent (ZMod p)
        (fun j : Fin c => fun i : Fin r => (A i j : ZMod p)) →
      (∃ rows : Fin c → Fin r,
        Function.Injective rows ∧
        Matrix.det (fun i j => (A (rows i) j : ZMod p)) ≠ 0 ∧
        Matrix.det (fun i j => A (rows i) j) ≠ 0 ∧
        Matrix.det (fun i j => (A (rows i) j : ℚ)) ≠ 0) ∧
      LinearIndependent ℚ
        (fun j : Fin c => fun i : Fin r => (A i j : ℚ))

end MathlibPlus.Open.ResearchFormalization.R0566ModularRank
