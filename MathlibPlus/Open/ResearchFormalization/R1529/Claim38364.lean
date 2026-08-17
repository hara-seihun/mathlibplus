import MathlibPlus.Open.Research.FormalizationBatch.R1529

namespace MathlibPlus.Open.ResearchFormalization.R1529.Claim38364

open MathlibPlus.Open.Research.FormalizationBatch.R1529

abbrev F7 := ZMod 7
abbrev Z8 := ZMod 8
abbrev SlopeSeven := {a : Z8 → F7ˣ // a 0 = 1}

def slopePeriodic (a : SlopeSeven) (d : Z8) : Prop :=
  ∀ k : Z8, a.1 (k + d) = a.1 k

def paritySign (k : Z8) : F7 :=
  if k.val % 2 = 0 then 1 else -1

def coordinateVector (i : Z8) : Fin 7 → F7 :=
  fun j => if i = (j.1 + 1 : Z8) then 1 else 0

def deltaVector (d k : Z8) : Fin 7 → F7 :=
  coordinateVector (k + d) - coordinateVector k

def gammaVector (d k : Z8) : Fin 7 → F7 :=
  paritySign k • deltaVector d k

def slopeRatio (a : SlopeSeven) (k : Z8) : F7 :=
  (a.1 (k + 1) : F7) * (a.1 k : F7)⁻¹

def shiftVector (a : SlopeSeven) (d k : Z8) : Fin 7 → F7 :=
  gammaVector d (k + 1) -
    slopeRatio a k • gammaVector d k

def allRatiosOne (a : SlopeSeven) : Prop :=
  ∀ k : Z8, slopeRatio a k = 1

noncomputable def commonFixedPointMatrix (a : SlopeSeven) (d : Z8) :
    Matrix (Z8 × Z8) (Fin 7) F7 :=
  letI := Classical.propDecidable
  fun ij j =>
    if allRatiosOne a then
      shiftVector a d ij.1 j
    else
      (1 - slopeRatio a ij.2) * shiftVector a d ij.1 j -
        (1 - slopeRatio a ij.1) * shiftVector a d ij.2 j

def gammaMatrix (d : Z8) : Matrix Z8 (Fin 7) F7 :=
  fun k j => gammaVector d k j

def rankSignature (d : Z8) (commonRank gammaRank rowCount : ℕ) : Prop :=
  Nat.card {a : SlopeSeven // slopePeriodic a d} = rowCount ∧
    ∀ a : SlopeSeven, slopePeriodic a d →
      Matrix.rank (commonFixedPointMatrix a d) = commonRank ∧
        Matrix.rank (gammaMatrix d) = gammaRank

def claim38364 : Prop :=
  rankSignature 1 6 7 1 ∧
    rankSignature 3 6 7 1 ∧
    rankSignature 5 6 7 1 ∧
    rankSignature 7 6 7 1 ∧
    rankSignature 2 6 6 6 ∧
    rankSignature 6 6 6 6 ∧
    rankSignature 4 4 4 216

end MathlibPlus.Open.ResearchFormalization.R1529.Claim38364
