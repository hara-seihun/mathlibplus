import MathlibPlus.GroupTheory.Claim29775
import MathlibPlus.Open.ResearchFormalization.Claim29701
import MathlibPlus.Open.ResearchFormalizationBatch_01a000fa_cafc_7f26_afad_440b9a41e3b3

namespace MathlibPlus.Open.ResearchFormalization.R1034FiberSupport

noncomputable section

/-- Claim 29777: inverse-pair-separated active fibre profiles fix every
inverse-closed presentation, with arbitrary finite group fibres and arbitrary
permutations. -/
def separatedFiberProfilesFixEveryInverseClosedPresentation_claim29777 : Prop :=
  ∀ {A H : Type*} [Fintype A] [Group A] [Fintype H] [Group H]
    (q : H → Equiv.Perm A),
    MathlibPlus.GroupTheory.Claim29775.activeSupport q ∩
        {h : H | h⁻¹ ∈
          MathlibPlus.GroupTheory.Claim29775.activeSupport q} =
      (∅ : Set H) →
      ∀ S : Set (A × H),
        MathlibPlus.Open.ResearchFormalization.Claim29701.inverseClosed S →
          MathlibPlus.Open.ResearchFormalization.Claim29701.inverseClosed
            (MathlibPlus.GroupTheory.Claim29775.fiberMap q '' S) →
            MathlibPlus.GroupTheory.Claim29775.fiberMap q '' S = S

/-- Claim 29779: the exact inverse-pair-separated support census on
`C₂³ × C₃²`, including attainment of the maximum support size and the
arbitrary-fibre permutation harmlessness clause. -/
def exactC2CubedTimesC3SquaredSeparatedSupportCount_claim29779 : Prop :=
  Fintype.card {
      x : MathlibPlus.Open.ResearchFormalization.Claim29701.C3SquareGroup //
        x ≠ 1} = 8 ∧
    MathlibPlus.Open.ResearchFormalization.Claim29701.inversePairs.card = 4 ∧
    (∀ P ∈
        MathlibPlus.Open.ResearchFormalization.Claim29701.inversePairs,
      P.card = 2) ∧
    MathlibPlus.Open.ResearchFormalization.Claim29701.separatedSupports.card =
      3 ^ 4 ∧
    MathlibPlus.Open.ResearchFormalization.Claim29701.separatedSupports.card =
      81 ∧
    MathlibPlus.Open.ResearchFormalization.Claim29701.nonemptySeparatedSupports.card =
      80 ∧
    (∀ C ∈
        MathlibPlus.Open.ResearchFormalization.Claim29701.separatedSupports,
      C.card ≤ 4) ∧
    (∃ C,
      C ∈
        MathlibPlus.Open.ResearchFormalization.Claim29701.separatedSupports ∧
        C.card = 4) ∧
    (∀ C ∈
        MathlibPlus.Open.ResearchFormalization.Claim29701.separatedSupports,
      ∀ q :
          MathlibPlus.Open.ResearchFormalization.Claim29701.C3SquareGroup →
            Equiv.Perm (Multiplicative (Fin 3 → ZMod 2)),
        MathlibPlus.Open.ResearchFormalization.Claim29701.separatedFiberPermutationsAreHarmless
          C (Multiplicative (Fin 3 → ZMod 2)) q)

end

end MathlibPlus.Open.ResearchFormalization.R1034FiberSupport
