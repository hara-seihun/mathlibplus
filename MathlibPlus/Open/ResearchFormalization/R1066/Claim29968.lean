import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1066Claim29968

noncomputable section

private abbrev Base := Fin 2 → ZMod 3
private abbrev MarkedPair := Equiv.Perm Base × Base

private def isMarkedPair (p : MarkedPair) : Prop :=
  p.1 0 = 0 ∧ p.2 ≠ 0

private noncomputable def markedPairs : Finset MarkedPair := by
  classical
  exact Finset.univ.filter isMarkedPair

private def baseMapIsLinear (p : MarkedPair) : Prop :=
  ∃ L : Base ≃+ Base, p.1 = L.toEquiv

private def markedActionRelation (L R : Base ≃+ Base)
    (p q : MarkedPair) : Prop :=
  q.1 = R.symm.toEquiv.trans (p.1.trans L.toEquiv) ∧
    q.2 = R p.2

private noncomputable def markedOrbit (p : MarkedPair) : Finset MarkedPair := by
  classical
  exact markedPairs.filter (fun q => ∃ L R : Base ≃+ Base,
    markedActionRelation L R p q)

private noncomputable def markedOrbits : Finset (Finset MarkedPair) := by
  classical
  exact markedPairs.image markedOrbit

private noncomputable def orbitCount (n : ℕ) : ℕ :=
  (markedOrbits.filter (fun O => O.card = n)).card

private noncomputable def linearOrbitCount : ℕ := by
  classical
  exact (markedOrbits.filter (fun O => ∃ p ∈ O, baseMapIsLinear p)).card

private noncomputable def nonlinearOrbitCount : ℕ := by
  classical
  exact (markedOrbits.filter (fun O => ∀ p ∈ O, ¬baseMapIsLinear p)).card

/-- Claim 29968: the exact marked `GL(2,3)` double-coset orbit census. -/
def claim_29968_markedOrbitClassification : Prop :=
  markedPairs.card = 322560 ∧
    orbitCount 384 = 6 ∧
      orbitCount 1152 = 18 ∧
        orbitCount 2304 = 130 ∧
          markedOrbits.card = 154 ∧
            linearOrbitCount = 1 ∧
              nonlinearOrbitCount = 153 ∧
                (∀ O ∈ markedOrbits,
                  O.card = 384 ∨ O.card = 1152 ∨ O.card = 2304) ∧
                  (∀ O ∈ markedOrbits,
                    (∃ p ∈ O, baseMapIsLinear p) ∨
                      (∀ p ∈ O, ¬baseMapIsLinear p))

end

end MathlibPlus.Open.ResearchFormalization.R1066Claim29968
