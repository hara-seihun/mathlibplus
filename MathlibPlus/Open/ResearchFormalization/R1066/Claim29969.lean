import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1066Claim29969

noncomputable section

private abbrev ActiveFiber := Fin 3 → ZMod 2
private abbrev Base := Fin 2 → ZMod 3
private abbrev Group := ActiveFiber × Base
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

private noncomputable def nonlinearOrbits : Finset (Finset MarkedPair) := by
  classical
  exact markedOrbits.filter (fun O => ∀ p ∈ O, ¬baseMapIsLinear p)

private abbrev NonlinearMarkedRepresentative :=
  {O : Finset MarkedPair // O ∈ nonlinearOrbits}

private noncomputable def orbitRepresentative (O : Finset MarkedPair) : MarkedPair :=
  O.toList.headD (Equiv.refl Base, 0)

private def oneActiveMap (p : MarkedPair)
    (rho : Equiv.Perm ActiveFiber) : Equiv.Perm Group :=
  ((Equiv.prodComm ActiveFiber Base).trans
    ((Equiv.sigmaEquivProd Base ActiveFiber).symm.trans
      ((Equiv.sigmaCongr p.1 (fun h =>
        if h = p.2 then rho else Equiv.refl ActiveFiber)).trans
        (Equiv.sigmaEquivProd Base ActiveFiber)))).trans
    (Equiv.prodComm Base ActiveFiber)

private noncomputable def retainedActiveFiberPermutations
    (_ : NonlinearMarkedRepresentative) : Finset (Equiv.Perm ActiveFiber) :=
  Finset.univ

private abbrev RetainedMapData :=
  NonlinearMarkedRepresentative × Equiv.Perm ActiveFiber

private def retainedMap (d : RetainedMapData) : Equiv.Perm Group :=
  oneActiveMap (orbitRepresentative d.1.1) d.2

private def retainsAllActiveFiberPermutations
    (O : NonlinearMarkedRepresentative) : Prop :=
  Function.Injective (fun rho : Equiv.Perm ActiveFiber =>
    retainedMap (O, rho))

/-- Claim 29969: every active `C₂³`-fiber permutation is retained for every
nonlinear marked representative, with no quotient on that fiber. -/
def claim_29969_allActiveFiberPermutationsRetained : Prop :=
  Fintype.card NonlinearMarkedRepresentative = 153 ∧
    (∀ O : NonlinearMarkedRepresentative,
      (retainedActiveFiberPermutations O).card = 40320 ∧
        retainsAllActiveFiberPermutations O) ∧
      Fintype.card (Equiv.Perm ActiveFiber) = 40320 ∧
        Fintype.card RetainedMapData = 153 * 40320 ∧
          Fintype.card RetainedMapData = 6168960

end

end MathlibPlus.Open.ResearchFormalization.R1066Claim29969
