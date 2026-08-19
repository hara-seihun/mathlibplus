import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1167

noncomputable section

/-- The coordinate carrier used by the retained `C₇²` rows. -/
abbrev C7Square := ZMod 7 × ZMod 7

/-- A raw `2 × 2` matrix over `𝔽₇`. -/
abbrev Matrix2_7 := Matrix (Fin 2) (Fin 2) (ZMod 7)

/-- The exact predicate for a raw matrix to represent an element of `GL(2,7)`. -/
def IsGL2_7 (M : Matrix2_7) : Prop :=
  IsUnit (Matrix.det M)

/-- The linear action of a raw matrix on the displayed coordinate pair. -/
def matrixAction (M : Matrix2_7) (v : C7Square) : C7Square :=
  (M 0 0 * v.1 + M 0 1 * v.2,
    M 1 0 * v.1 + M 1 1 * v.2)

/-- The row-major matrix tuple used for the source's lexicographic convention. -/
def matrixEntries (M : Matrix2_7) : List (ZMod 7) :=
  [M 0 0, M 0 1, M 1 0, M 1 1]

/-- Lexicographic comparison of matrices through their representatives in `0,…,6`. -/
def matrixLexLE (M N : Matrix2_7) : Prop :=
  M = N ∨
    List.Lex (fun a b : ZMod 7 => a.val < b.val)
      (matrixEntries M) (matrixEntries N)

/-- The source connection set consisting of the nonzero points on the vertical line. -/
def disjointComponentConnection : Set C7Square :=
  {v | v.1 = 0 ∧ v.2 ≠ 0}

/-- The connection set of the complete seven-partite complement model. -/
def complementConnection : Set C7Square :=
  {v | v.1 ≠ 0}

/-- The retained graph-index-3 connection set, literally the disjoint-component model. -/
def graphIndex3Connection : Set C7Square :=
  disjointComponentConnection

/-- The explicit matrix recorded for the retained graph-index-17790 row. -/
def matrix17790 : Matrix2_7 :=
  !![(0 : ZMod 7), 1; 1, 2]

/-- Image of a connection set under a displayed linear coordinate map. -/
def matrixImage (M : Matrix2_7) (S : Set C7Square) : Set C7Square :=
  matrixAction M '' S

/-- The retained graph-index-17790 connection set is the image of the
complete seven-partite model under `[[0,1],[1,2]]`. -/
def graphIndex17790Connection : Set C7Square :=
  matrixImage matrix17790 complementConnection

/-- Matrices carrying one displayed model to one retained row. -/
def linearNormalizations (source target : Set C7Square) : Set Matrix2_7 :=
  {M | IsGL2_7 M ∧ matrixImage M source = target}

/-- A member is lexicographically first in a matrix set. -/
def isLexFirst (M : Matrix2_7) (S : Set Matrix2_7) : Prop :=
  M ∈ S ∧ ∀ N, N ∈ S → matrixLexLE M N

/-- Claim 41539: the two retained C₇-square rows each have exactly 252
linear normalizations, with the displayed first representatives. -/
def exactLinearNormalizationCount_claim41539 : Prop :=
  Set.ncard
      (linearNormalizations disjointComponentConnection graphIndex3Connection) = 252 ∧
    isLexFirst (1 : Matrix2_7)
      (linearNormalizations disjointComponentConnection graphIndex3Connection) ∧
    Set.ncard
        (linearNormalizations complementConnection graphIndex17790Connection) = 252 ∧
      isLexFirst matrix17790
        (linearNormalizations complementConnection graphIndex17790Connection)

end

end MathlibPlus.Open.ResearchFormalization.R1167
