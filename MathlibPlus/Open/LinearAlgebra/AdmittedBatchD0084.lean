import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.LinearAlgebra.AdmittedBatchD0084

noncomputable section

/-- The row-restricted and column-restricted matrix used by local exposure. -/
def blockSubmatrix {R Row Col : Type*} [Field R]
    [Fintype Row] [Fintype Col] [DecidableEq Row] [DecidableEq Col]
    (M : Matrix Row Col R) (Rb : Finset Row) (S : Finset Col) :
    Matrix {r : Row // r ∈ Rb} {v : Col // v ∈ S} R :=
  M.submatrix (fun r => r.1) (fun v => v.1)

def blockRank {R Row Col : Type*} [Field R]
    [Fintype Row] [Fintype Col] [DecidableEq Row] [DecidableEq Col]
    (M : Matrix Row Col R) (Rb : Finset Row) (S : Finset Col) : ℕ :=
  Matrix.rank (blockSubmatrix M Rb S)

/-- A row combination supported on one row block and equal to the coordinate
functional on the surviving columns. -/
def blockRowCertificate {R Row Col : Type*} [Field R]
    [Fintype Row] [Fintype Col] [DecidableEq Row] [DecidableEq Col]
    (M : Matrix Row Col R) (Rb : Finset Row) (S : Finset Col)
    (v : Col) : Prop :=
  ∃ coeff : Row → R,
    (∀ r, r ∉ Rb → coeff r = 0) ∧
    (∀ s, s ∈ S →
      ∑ r : Row, coeff r * M r s = if s = v then 1 else 0)

/-- Claim 5152: the local-coloop rank jump and its row-certificate
characterization. -/
def blockExposureRankAndCertificate : Prop :=
  ∀ {R Row Col : Type*} [Field R]
    [Fintype Row] [Fintype Col] [DecidableEq Row] [DecidableEq Col]
    (M : Matrix Row Col R) (Rb : Finset Row) (S : Finset Col) (v : Col),
    v ∈ S →
      (blockRank M Rb S > blockRank M Rb (S.erase v) ↔
        blockRowCertificate M Rb S v)

end

end MathlibPlus.Open.LinearAlgebra.AdmittedBatchD0084
