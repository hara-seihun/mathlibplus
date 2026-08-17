import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1066Claim29971

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

private def unionOfNonidentityBlocks (f : Equiv.Perm Group)
    (S : Set Group) : Prop :=
  (∀ x, x ∈ S → x ≠ 0) ∧
    ∀ x, x ∈ S → ∀ y,
      compatibilityRelation f x y → y ∈ S

private def blockFixedByMap (f : Equiv.Perm Group)
    (B : Finset Group) : Prop :=
  B.image f.toEmbedding = B

/-- Claim 29971: every nonlinear compatibility block is fixed setwise by its
presentation map, and every union of such blocks is fixed as a connection set. -/
def claim_29971_nonlinearCompatibilityBlocksFixed : Prop :=
  Fintype.card RetainedMapData = 153 * 40320 ∧
    Fintype.card RetainedMapData = 6168960 ∧
      (∑ d : RetainedMapData,
          (nonidentityCompatibilityBlocks (mapOfData d)).card) = 15080976 ∧
        (∀ d : RetainedMapData,
          ∀ B ∈ nonidentityCompatibilityBlocks (mapOfData d),
            blockFixedByMap (mapOfData d) B) ∧
          (∀ d : RetainedMapData, ∀ S : Set Group,
            unionOfNonidentityBlocks (mapOfData d) S →
              Set.image (mapOfData d) S = S)

end

end MathlibPlus.Open.ResearchFormalization.R1066Claim29971
