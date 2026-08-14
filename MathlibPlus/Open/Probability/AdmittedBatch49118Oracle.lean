import Mathlib

open scoped BigOperators Classical

namespace MathlibPlus.Open.Probability.AdmittedBatch49118

noncomputable section

abbrev Address := Fin 4
abbrev SignBit := Fin 2
abbrev OracleState :=
  (Fin 4 → Address) × (Fin 4 → Address) × (Fin 4 → SignBit)

inductive OracleCoordinate
  | privateAddress (a : Fin 4) (bit : Fin 2)
  | sharedEntry (j : Fin 4) (bit : Fin 2)
  | dataSign (j : Fin 4)
  deriving Fintype, DecidableEq

def signValue (z : SignBit) : ℚ :=
  if z = 0 then -1 else 1

def oracleS (s : OracleState) (a : Fin 4) : ℚ :=
  signValue (s.2.2 (s.2.1 a))

def oracleT (s : OracleState) (t : Fin 4) : ℚ :=
  oracleS s (s.1 t)

def oracleAverage (s : OracleState) : ℚ :=
  (1 / 4 : ℚ) * ∑ t : Fin 4, oracleT s t

def oracleStateWeight (_s : OracleState) : ℚ :=
  1 / (Fintype.card OracleState : ℚ)

/-- R-3876 S1: four private addresses, four shared two-bit entries, and four signs. -/
def twentyCoordinateOracle : Prop :=
  Fintype.card OracleCoordinate = 20 ∧
    (∀ s : OracleState, 0 < oracleStateWeight s) ∧
    (∀ s t : OracleState, oracleStateWeight s = oracleStateWeight t) ∧
    (∀ s : OracleState, oracleAverage s =
      (oracleT s 0 + oracleT s 1 + oracleT s 2 + oracleT s 3) / 4)

end

end MathlibPlus.Open.Probability.AdmittedBatch49118
