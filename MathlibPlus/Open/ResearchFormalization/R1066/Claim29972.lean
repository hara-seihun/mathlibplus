import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1066Claim29972

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

private abbrev RetainedMapData :=
  NonlinearMarkedRepresentative × Equiv.Perm ActiveFiber

private def mapOfData (d : RetainedMapData) : Equiv.Perm Group :=
  oneActiveMap (orbitRepresentative d.1.1) d.2

private def additiveRelativeDerivative (f : Equiv.Perm Group)
    (g : Group) : Equiv.Perm Group :=
  (((Equiv.addRight g).trans f).trans
    (Equiv.addRight (-(f g)))).trans f.symm

private def compatibilityGenerator (f : Equiv.Perm Group)
    (x y : Group) : Prop :=
  (∃ g : Group, additiveRelativeDerivative f g x = y) ∨
    y = -x ∨ y = f.symm (-(f x))

private def compatibilityRelation (f : Equiv.Perm Group)
    (x y : Group) : Prop :=
  Relation.EqvGen (compatibilityGenerator f) x y

private noncomputable def compatibilityBlock (f : Equiv.Perm Group)
    (x : Group) : Finset Group := by
  classical
  exact Finset.univ.filter (compatibilityRelation f x)

private noncomputable def nonidentityCompatibilityBlocks
    (f : Equiv.Perm Group) : Finset (Finset Group) := by
  classical
  exact (Finset.univ.image (compatibilityBlock f)).filter (fun B => 0 ∉ B)

private noncomputable def blockCountOfData (d : RetainedMapData) : ℕ :=
  (nonidentityCompatibilityBlocks (mapOfData d)).card

private noncomputable def blockCountHistogram (n : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun d : RetainedMapData =>
    blockCountOfData d = n)).card

private noncomputable def expectedHistogram (n : ℕ) : ℕ :=
  if n = 2 then 4569600 else
  if n = 3 then 863360 else
  if n = 4 then 519008 else
  if n = 5 then 111384 else
  if n = 6 then 58464 else
  if n = 7 then 27104 else
  if n = 8 then 10024 else
  if n = 9 then 7518 else
  if n = 11 then 980 else
  if n = 12 then 728 else
  if n = 13 then 546 else
  if n = 15 then 231 else
  if n = 23 then 13 else 0

/-- Claim 29972: the exact nonlinear-map histogram by nonidentity
compatibility-block count. -/
def claim_29972_exactCompatibilityBlockHistogram : Prop :=
  Fintype.card RetainedMapData = 153 * 40320 ∧
    Fintype.card RetainedMapData = 6168960 ∧
      ∀ n : ℕ, blockCountHistogram n = expectedHistogram n

end

end MathlibPlus.Open.ResearchFormalization.R1066Claim29972
