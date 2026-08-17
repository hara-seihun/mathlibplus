import MathlibPlus.Open.MatroidBatch

namespace MathlibPlus.Open.MatroidBatch

noncomputable section

/-- Every represented basis contains the exact coloop labels; the coloop
vectors are independent, their labelled register has size at most the
represented rank (and hence at most `d`), and the non-coloop core has a basis
of size at most `d`. -/
def boundedColoopAndCoreRepresentation_claim5566 : Prop :=
  ∀ (F ι : Type*) [Field F] [DecidableEq ι]
    (d : ℕ) (E : Finset ι) (v : ι → Fin d → F),
    (∀ A : Finset ι,
      A ⊆ E ∧
        LinearIndependent F (fun k : {k // k ∈ A} => v k) ∧
        Submodule.span F (v '' ((↑A : Set ι))) =
          Submodule.span F (v '' ((↑E : Set ι))) →
      ∀ k, coloopLabel d E v k → k ∈ A) ∧
    LinearIndependent F
      (fun k : {k // coloopLabel d E v k} => v k) ∧
    Set.Finite (coloopCoreC d E v) ∧
    Set.ncard (coloopCoreC d E v) ≤
      Module.finrank F (Submodule.span F (v '' ((↑E : Set ι)))) ∧
    Set.ncard (coloopCoreC d E v) ≤ d ∧
    Module.finrank F (Submodule.span F (v '' ((↑E : Set ι)))) ≤ d ∧
    (∃ B : Set (Fin d → F),
      B.Finite ∧
        B ⊆ coloopCoreN d E v ∧
        LinearIndependent F (fun w : B => (w : Fin d → F)) ∧
        Submodule.span F B = (coloopCoreRegister d E v).1 ∧
        B.ncard ≤ d) ∧
    Set.ncard ((coloopCoreRegister d E v).2) ≤ d

end

end MathlibPlus.Open.MatroidBatch
