import MathlibPlus.Open.ResearchFormalization.Batch39139

namespace MathlibPlus.Open.Research.R1549Displacement39143

noncomputable section

open MathlibPlus.Open.ResearchFormalization.Batch39139

/-- The displacement subspace of a zero-fixed affine-space permutation. -/
def displacementSubspace (f : Equiv.Perm V5) : Submodule F2 V5 :=
  Submodule.span F2 (Set.range (fun x : V5 => f x + x))

/-- Claim 39143: every literal regular E32 pair has a conjugating element in
its finest unordered-orbital closure that fixes zero and has a proper
displacement quotient; the induced quotient action is pointwise trivial. -/
def claim39143 : Prop :=
  ∀ E F : LiteralE32,
    let H := generatedPairGroup E F
    ∃ f : Equiv.Perm V5,
      f ∈ unorderedOrbitalClosure H ∧
        ConjugateSubgroup f E.1 F.1 ∧
          f 0 = 0 ∧
            displacementSubspace f ≠ ⊤ ∧
              ∀ x : V5,
                Submodule.Quotient.mk (p := displacementSubspace f) (f x) =
                  Submodule.Quotient.mk (p := displacementSubspace f) x

end

end MathlibPlus.Open.Research.R1549Displacement39143
