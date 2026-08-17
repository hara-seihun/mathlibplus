import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.CIMixedAbelianTranslationVoltage

noncomputable section

abbrev H := Fin 2 → ZMod 3
abbrev HSharp := {h : H // h ≠ 0}
abbrev V := HSharp →₀ ℤ
abbrev PointedFiber (B : Type*) := B × H

def hSharpCarrier : Set H := {h | h ≠ 0}

def standardBasis (x : H) : V :=
  if hx : x = 0 then 0 else Finsupp.single ⟨x, hx⟩ 1

def translation (k : H) : Equiv.Perm H := Equiv.addRight k

def qMap (tau : Equiv.Perm H) (k h : H) : H :=
  tau.symm (tau (h + k) - tau k)

def qPerm (tau : Equiv.Perm H) (k : H) : Equiv.Perm H :=
  tau.symm * Equiv.addRight (-(tau k)) * tau * Equiv.addRight k

def pointedPermutationFormula (tau : Equiv.Perm H) : Prop :=
  ∀ (k h : H), qPerm tau k h = qMap tau k h

def deltaGroup (tau : Equiv.Perm H) : Subgroup (Equiv.Perm H) :=
  Subgroup.closure (Set.range (qPerm tau))

def deltaOrbit (tau : Equiv.Perm H) (h : H) : Set H :=
  {x | ∃ g : deltaGroup tau, g.1 h = x}

def projectedOrbit (tau : Equiv.Perm H) (C : Set H) : Prop :=
  ∃ h : H, h ≠ 0 ∧ C = deltaOrbit tau h ∧ C ⊆ hSharpCarrier

def preservesDeltaOrbits (tau : Equiv.Perm H) : Prop :=
  ∀ h : H, h ≠ 0 → ∀ x : H, x ∈ deltaOrbit tau h → tau x ∈ deltaOrbit tau h

def edgeVoltage (tau : Equiv.Perm H) (h k : H) : V :=
  standardBasis (h + k) - standardBasis k - standardBasis (qPerm tau k h)

def treeVertex (C : Set H) := {h : H // h ∈ C}
abbrev TreeEdges (C : Set H) := Sym2 (treeVertex C)

def treeGraph (C : Set H) (E : Set (TreeEdges C)) : SimpleGraph (treeVertex C) :=
  SimpleGraph.fromEdgeSet E

def treeEdgeVoltageCondition (tau : Equiv.Perm H) (C : Set H)
    (E : Set (TreeEdges C)) (potential : H → V) : Prop :=
  ∀ (u v : treeVertex C), s(u, v) ∈ E →
    (∃ k : H,
      v.1 = qPerm tau k u.1 ∧
        potential v.1 - potential u.1 = edgeVoltage tau u.1 k) ∨
    (∃ k : H,
      u.1 = qPerm tau k v.1 ∧
        potential u.1 - potential v.1 = edgeVoltage tau v.1 k)

def treeVoltageData (tau : Equiv.Perm H) (C : Set H)
    (root : treeVertex C) (E : Set (TreeEdges C)) (potential : H → V) : Prop :=
  (treeGraph C E).IsTree ∧
    potential root.1 = 0 ∧
    (∀ h : H, h ∉ C → potential h = 0) ∧
    treeEdgeVoltageCondition tau C E potential

def cycleGenerator (tau : Equiv.Perm H) (C : Set H)
    (potential : H → V) : Set V :=
  {z | ∃ h : H, h ∈ C ∧ ∃ k : H,
    z = potential h + edgeVoltage tau h k - potential (qPerm tau k h)}

def cycleLattice (tau : Equiv.Perm H) (C : Set H)
    (potential : H → V) : AddSubgroup V :=
  AddSubgroup.closure (cycleGenerator tau C potential)

def synchronizationDiscrepancy (tau : Equiv.Perm H)
    (potential : H → V) (h : H) : V :=
  standardBasis h + potential h - potential (tau h)

def exactOrderThreeInQuotient (Lambda : AddSubgroup V) (d : V) : Prop :=
  d ∉ Lambda ∧ 3 • d ∈ Lambda

def treeChoiceIndependent (tau : Equiv.Perm H) (C : Set H)
    (root : treeVertex C) : Prop :=
  ∀ (E₁ E₂ : Set (TreeEdges C)) (v₁ v₂ : H → V),
    treeVoltageData tau C root E₁ v₁ →
      treeVoltageData tau C root E₂ v₂ →
        cycleLattice tau C v₁ = cycleLattice tau C v₂ ∧
          ∀ h : H, h ∈ C → v₁ h - v₂ h ∈ cycleLattice tau C v₁

def coefficientMap {B : Type*} [AddCommGroup B] (c : H → B) : V →+ B :=
  (Finsupp.lsum ℤ
    (fun x : HSharp => LinearMap.toSpanSingleton ℤ B (c x.1))).toAddMonoidHom

def coefficientLatticeImage {B : Type*} [AddCommGroup B]
    (c : H → B) (Lambda : AddSubgroup V) : AddSubgroup B :=
  AddSubgroup.map (coefficientMap c) Lambda

def voltageValue {B : Type*} [AddCommGroup B]
    (tau : Equiv.Perm H) (c : H → B) (h k : H) : B :=
  coefficientMap c (edgeVoltage tau h k)

def liftedBaseStep (tau : Equiv.Perm H) (m : H × Bool) (h : H) : H :=
  if m.2 then (qPerm tau m.1).symm h else qPerm tau m.1 h

def liftedVoltageStep {B : Type*} [AddCommGroup B]
    (tau : Equiv.Perm H) (c : H → B) (m : H × Bool) (h : H) : B :=
  if m.2 then -voltageValue tau c ((qPerm tau m.1).symm h) m.1
  else voltageValue tau c h m.1

def liftedWordBase (tau : Equiv.Perm H) : List (H × Bool) → H → H
  | [], h => h
  | m :: word, h => liftedWordBase tau word (liftedBaseStep tau m h)

def liftedWordVoltage {B : Type*} [AddCommGroup B]
    (tau : Equiv.Perm H) (c : H → B) : List (H × Bool) → H → B
  | [], _ => 0
  | m :: word, h =>
      liftedVoltageStep tau c m h +
        liftedWordVoltage tau c word (liftedBaseStep tau m h)

def liftedWord {B : Type*} [AddCommGroup B]
    (tau : Equiv.Perm H) (c : H → B)
    (word : List (H × Bool)) (x : PointedFiber B) : PointedFiber B :=
  (x.1 + liftedWordVoltage tau c word x.2,
    liftedWordBase tau word x.2)

def liftedOrbit {B : Type*} [AddCommGroup B]
    (tau : Equiv.Perm H) (c : H → B) (x : PointedFiber B) :
    Set (PointedFiber B) :=
  {y | ∃ word : List (H × Bool), liftedWord tau c word x = y}

def literalTranslationChart {B : Type*} [AddCommGroup B]
    (tau : Equiv.Perm H) (c : H → B) : PointedFiber B → PointedFiber B :=
  fun x => (x.1 + c x.2, tau x.2)

def literalChartFixesLiftedOrbits {B : Type*} [AddCommGroup B]
    (tau : Equiv.Perm H) (c : H → B) (C : Set H) : Prop :=
  ∀ (b : B) (h : H), h ∈ C →
    Set.image (literalTranslationChart tau c)
        (liftedOrbit tau c (b, h)) =
      liftedOrbit tau c (b, h)

def claim61169 : Prop :=
  ∀ (tau : Equiv.Perm H),
    tau 0 = 0 →
      preservesDeltaOrbits tau →
        pointedPermutationFormula tau ∧
          (∀ (C : Set H), projectedOrbit tau C →
            ∀ (root : treeVertex C) (E : Set (TreeEdges C))
              (potential : H → V),
              treeVoltageData tau C root E potential →
                (∀ h : H, h ∈ C →
                  exactOrderThreeInQuotient
                    (cycleLattice tau C potential)
                    (synchronizationDiscrepancy tau potential h)) ∧
                treeChoiceIndependent tau C root) ∧
          (∀ (C : Set H), projectedOrbit tau C →
            ∀ (root : treeVertex C) (E : Set (TreeEdges C))
              (potential : H → V),
              treeVoltageData tau C root E potential →
                ∀ (B : Type*) [Fintype B] [AddCommGroup B],
                  ¬ 3 ∣ Fintype.card B →
                    ∀ (c : H → B), c 0 = 0 →
                      (∀ h : H, h ∈ C →
                        coefficientMap c
                            (synchronizationDiscrepancy tau potential h) ∈
                          coefficientLatticeImage c
                            (cycleLattice tau C potential)) ∧
                      literalChartFixesLiftedOrbits tau c C)

end
end MathlibPlus.Open.ResearchFormalization.CIMixedAbelianTranslationVoltage
