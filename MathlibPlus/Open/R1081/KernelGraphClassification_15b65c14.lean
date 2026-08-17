import MathlibPlus.Open.R1081.FactorGraphs_01a000db_a016_792b_b33f_00a9410f47c6

namespace MathlibPlus.Open.R1081

noncomputable section

abbrev KernelPlane7 := Z7 × Z7

def kernelGraphNeighborhood (Q I : Set Z7) (u : KernelPlane7) : Set KernelPlane7 :=
  {v | kernelAdj Q I u v}

def kernelValency (Q I : Set Z7) : Nat :=
  Set.ncard (kernelGraphNeighborhood Q I (0, 0))

def zeroStabilizerCard (Q I : Set Z7) : Nat :=
  Nat.card {σ : Equiv.Perm KernelPlane7 //
    kernelGraphAut Q I σ ∧ σ (0, 0) = (0, 0)}

def kernelGraphIndex (i : Fin 4) : Nat :=
  match i.1 with
  | 0 => 50
  | 1 => 51
  | 2 => 2770
  | _ => 2771

def kernelGraphQ (i : Fin 4) : Set Z7 :=
  match i.1 with
  | 0 => ({1, -1} : Set Z7)
  | 1 => ({1, -1} : Set Z7)
  | _ => ({1, -1, 2, -2} : Set Z7)

def kernelGraphI (i : Fin 4) : Set Z7 :=
  match i.1 with
  | 0 => ({1, -1} : Set Z7)
  | 1 => ({1, -1, 2, -2} : Set Z7)
  | 2 => ({1, -1} : Set Z7)
  | _ => ({1, -1, 2, -2} : Set Z7)

def kernelGraphValency (i : Fin 4) : Nat :=
  match i.1 with
  | 0 => 16
  | 1 => 18
  | 2 => 30
  | _ => 32

def kernelGraphRow (i : Fin 4) : Nat × Set Z7 × Set Z7 × Nat :=
  (kernelGraphIndex i, kernelGraphQ i, kernelGraphI i, kernelGraphValency i)

def listedKernelGraphRows : Set (Nat × Set Z7 × Set Z7 × Nat) :=
  { (50, ({1, -1} : Set Z7), ({1, -1} : Set Z7), 16),
    (51, ({1, -1} : Set Z7), ({1, -1, 2, -2} : Set Z7), 18),
    (2770, ({1, -1, 2, -2} : Set Z7), ({1, -1} : Set Z7), 30),
    (2771, ({1, -1, 2, -2} : Set Z7), ({1, -1, 2, -2} : Set Z7), 32) }

def claim28692 : Prop :=
  Set.range kernelGraphRow = listedKernelGraphRows ∧
    (∀ i : Fin 4,
      kernelValency (kernelGraphQ i) (kernelGraphI i) = kernelGraphValency i) ∧
    (∀ Q I : Set Z7, admissibleQI Q I →
      ∃! i : Fin 4, kernelGraphQ i = Q ∧ kernelGraphI i = I) ∧
    (∀ Q I : Set Z7, admissibleQI Q I →
      zeroStabilizerCard Q I = 2 * 2 * 14 ^ 6)

def lexicographicKernelAdj (Q I : Set Z7)
    (u v : KernelPlane7) : Prop :=
  cyclicAdj Q u.1 v.1 ∨
    (u.1 = v.1 ∧ cyclicAdj I u.2 v.2)

def relationIsomorphism {α β : Type*}
    (r : α → α → Prop) (s : β → β → Prop) (e : α ≃ β) : Prop :=
  ∀ x y, r x y ↔ s (e x) (e y)

def coordinateFiber (x : Z7) : Set KernelPlane7 :=
  {u | u.1 = x}

def claim28693 : Prop :=
  (∀ Q I : Set Z7, admissibleQI Q I →
    relationIsomorphism (kernelAdj Q I) (lexicographicKernelAdj Q I)
      (Equiv.refl KernelPlane7)) ∧
    (∀ x : Z7,
      coordinateFiber x = Set.prod ({x} : Set Z7) Set.univ)

def setSymmetricDifference {α : Type*} (s t : Set α) : Set α :=
  (s \ t) ∪ (t \ s)

def neighborhoodDifferenceCard (Q I : Set Z7)
    (u v : KernelPlane7) : Nat :=
  Set.ncard (setSymmetricDifference
    (kernelGraphNeighborhood Q I u) (kernelGraphNeighborhood Q I v))

def sameFiberDifferenceValues (Q I : Set Z7) : Set Nat :=
  {n | ∃ u v : KernelPlane7,
    u ≠ v ∧ u.1 = v.1 ∧
      n = neighborhoodDifferenceCard Q I u v}

def crossFiberDifferenceValues (Q I : Set Z7) : Set Nat :=
  {n | ∃ u v : KernelPlane7,
    u.1 ≠ v.1 ∧
      n = neighborhoodDifferenceCard Q I u v}

def sameFiberDifferenceCriterion (Q I : Set Z7) : Prop :=
  ∀ u v : KernelPlane7,
    u.1 = v.1 ↔ neighborhoodDifferenceCard Q I u v < 10

def graphAutomorphismPreservesFibers (Q I : Set Z7) : Prop :=
  ∀ h : Equiv.Perm KernelPlane7,
    kernelGraphAut Q I h →
      ∀ u v : KernelPlane7,
        u.1 = v.1 ↔ (h u).1 = (h v).1

def claim28694 : Prop :=
  (∀ Q I : Set Z7, admissibleQI Q I →
    sameFiberDifferenceCriterion Q I ∧
      graphAutomorphismPreservesFibers Q I) ∧
    sameFiberDifferenceValues ({1, -1} : Set Z7) ({1, -1} : Set Z7) = {2, 4} ∧
    sameFiberDifferenceValues ({1, -1, 2, -2} : Set Z7) ({1, -1} : Set Z7) = {2, 4} ∧
    sameFiberDifferenceValues ({1, -1} : Set Z7)
      ({1, -1, 2, -2} : Set Z7) = {2, 4, 6} ∧
    sameFiberDifferenceValues ({1, -1, 2, -2} : Set Z7)
      ({1, -1, 2, -2} : Set Z7) = {2, 4, 6} ∧
    crossFiberDifferenceValues ({1, -1} : Set Z7) ({1, -1} : Set Z7) =
      {18, 24, 32} ∧
    crossFiberDifferenceValues ({1, -1} : Set Z7)
      ({1, -1, 2, -2} : Set Z7) = {20, 22, 36} ∧
    crossFiberDifferenceValues ({1, -1, 2, -2} : Set Z7)
      ({1, -1} : Set Z7) = {18, 24, 38} ∧
    crossFiberDifferenceValues ({1, -1, 2, -2} : Set Z7)
      ({1, -1, 2, -2} : Set Z7) = {20, 22, 34}

def signInZ7 (a : Z7) : Prop :=
  a = 1 ∨ a = -1

def coordinateZeroForm (h : Equiv.Perm KernelPlane7)
    (a : Z7) (ε b : Z7 → Z7) : Prop :=
  signInZ7 a ∧
    (∀ x : Z7, signInZ7 (ε x)) ∧
    b 0 = 0 ∧
    ∀ x y : Z7, h (x, y) = (a * x, ε x * y + b x)

def uniqueCoordinateZeroForm (h : Equiv.Perm KernelPlane7) : Prop :=
  ∃! a : Z7, ∃! ε : Z7 → Z7, ∃! b : Z7 → Z7,
    coordinateZeroForm h a ε b

def zeroFixingKernelAutomorphism (Q I : Set Z7)
    (h : Equiv.Perm KernelPlane7) : Prop :=
  kernelGraphAut Q I h ∧ h (0, 0) = (0, 0)

def claim28697 : Prop :=
  ∀ Q I : Set Z7, admissibleQI Q I →
    ∀ h : Equiv.Perm KernelPlane7,
      zeroFixingKernelAutomorphism Q I h → uniqueCoordinateZeroForm h

end

end MathlibPlus.Open.R1081
