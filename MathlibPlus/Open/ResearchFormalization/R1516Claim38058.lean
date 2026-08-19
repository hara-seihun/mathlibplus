import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1516Claim38058

noncomputable section

open Classical

private def binaryXor8 (i j : Fin 8) : Fin 8 :=
  Fin.ofNat 8 (Nat.xor i.val j.val)

private def linearLabelPermutation (α : Equiv.Perm (Fin 8)) : Prop :=
  α 0 = 0 ∧
    ∀ i j : Fin 8,
      α (binaryXor8 i j) = binaryXor8 (α i) (α j)

private def gl3TwoSet : Finset (Equiv.Perm (Fin 8)) :=
  Finset.univ.filter linearLabelPermutation

private def rhoZero : Equiv.Perm (Fin 8) :=
  Equiv.swap (6 : Fin 8) 7

private def recordSixInvolution : Equiv.Perm (Fin 8) :=
  (Equiv.swap (2 : Fin 8) 3) * Equiv.swap (6 : Fin 8) 7

private def gl3TwoCentralizer : Finset (Equiv.Perm (Fin 8)) :=
  Finset.univ.filter (fun α =>
    linearLabelPermutation α ∧ α * rhoZero = rhoZero * α)

def explicitGL3CentralizerCensus_claim38058 : Prop :=
  gl3TwoSet.card = 168 ∧
    gl3TwoCentralizer.card = 8 ∧
      recordSixInvolution ∈ gl3TwoCentralizer

end

end MathlibPlus.Open.ResearchFormalization.R1516Claim38058
