import MathlibPlus.Open.ResearchFormalization.R2614Claims42815_42818

namespace MathlibPlus.Open.ResearchFormalization.R2614Claim42814

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R2614Claims42815_42818

/-- The finite row surface used by the exact `R=2` skipped-minor scan.
The ten integer row positions are the nonnegative positions through one
lowering beyond the largest kernel support position. -/
def skippedBaseRows : Finset (Fin 4 → ℤ) :=
  ((Finset.univ : Finset (Fin 4 → Fin 10)).filter
      (fun q => StrictMono (fun i : Fin 4 => (q i : ℤ)))).image
    (fun q i => (q i : ℤ))

/-- The admissibility test used for a nonempty derivative subset in the
finite base scan: the retained bottom row may be lowered only from at least
one, and the resulting row tuple remains strict. -/
def skippedBaseCubeAdmissible (q : Fin 4 → ℤ) (I : Finset (Fin 4)) : Prop :=
  I.Nonempty ∧
    (0 ∉ I ∨ 1 ≤ q 0) ∧
      StrictMono (lowerIntSet q I)

/-- The nonempty derivative-cube surface.  The empty derivative is recorded
separately in `claim42814`, as it is needed by the boundary theorem while the
reported 1,610-cube census is the nonempty base census. -/
def skippedBaseNonemptyCubes :
    Finset ((Fin 4 → ℤ) × Finset (Fin 4)) :=
  @Finset.filter _
    (fun c : (Fin 4 → ℤ) × Finset (Fin 4) =>
      skippedBaseCubeAdmissible c.1 c.2)
    (fun _ => Classical.propDecidable _)
    (skippedBaseRows.product (Finset.univ : Finset (Finset (Fin 4))))

/-- The exact skipped-minor mixed-derivative value on a row/cube pair. -/
def skippedBaseValue (c : (Fin 4 → ℤ) × Finset (Fin 4)) : ℚ :=
  mixedIntPartial 2 c.2
    (fun rows => kernelMinorRows 2 skippedFourOffsets rows) c.1

/-- Claim 42814: the exact `R=2` skipped four-row base, with the empty
cube retained for the boundary statement and the exact nonempty-cube
sign census. -/
def claim42814 : Prop :=
  (∀ q ∈ skippedBaseRows,
    0 ≤ skippedBaseValue (q, (∅ : Finset (Fin 4)))) ∧
    (∀ c ∈ skippedBaseNonemptyCubes,
      0 ≤ skippedBaseValue c) ∧
      skippedBaseRows.card = 210 ∧
        skippedBaseNonemptyCubes.card = 1610 ∧
          (skippedBaseNonemptyCubes.filter
              (fun c => 0 < skippedBaseValue c)).card = 476 ∧
            (skippedBaseNonemptyCubes.filter
                (fun c => skippedBaseValue c = 0)).card = 1134 ∧
              (skippedBaseNonemptyCubes.filter
                  (fun c => skippedBaseValue c < 0)).card = 0

end

end MathlibPlus.Open.ResearchFormalization.R2614Claim42814
