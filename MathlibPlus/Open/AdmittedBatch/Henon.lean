import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.AdmittedBatch

abbrev HénonX (p : ℕ) := Fin 3 → ZMod p
abbrev HénonV (p : ℕ) := HénonX p × HénonX p

def henonF {p : ℕ} (z : HénonX p) : HénonX p :=
  ![z 0 ^ 2 + z 0 * z 1 * z 2, z 1 ^ 2, z 2 ^ 2]

def henonQ {p : ℕ} (v : HénonV p) : HénonV p :=
  (v.2, v.1 + henonF v.2)

def mixedDifference {p : ℕ} (a d : HénonX p) : HénonX p :=
  henonF (a + d) - henonF a - henonF d

def mixedDifferenceNeg {p : ℕ} (a d : HénonX p) : HénonX p :=
  henonF (a - d) - henonF a - henonF (-d)

def henonFibre {p : ℕ} (d : HénonX p) : Submodule (ZMod p) (HénonX p) :=
  Submodule.span (ZMod p)
    {w | w ∈ Set.range (fun a : HénonX p => mixedDifference a d) ∨
      w ∈ Set.range (fun a : HénonX p => mixedDifferenceNeg a d)}

def henonE1 (p : ℕ) : HénonX p := ![1, 0, 0]
def henonE2 (p : ℕ) : HénonX p := ![0, 1, 0]
def henonE3 (p : ℕ) : HénonX p := ![0, 0, 1]

def henonDirections (p : ℕ) : Finset (HénonX p) :=
  {henonE1 p, henonE2 p, henonE3 p, henonE2 p + henonE3 p}

def henonSelectedDirections (p : ℕ) : Finset (HénonX p) :=
  henonDirections p ∪ (henonDirections p).image (fun d => -d)

def henonSourceRow {p : ℕ} (d : HénonX p) : Set (HénonV p) :=
  {v | ∃ w : HénonX p, w ∈ henonFibre d ∧ v = (w, d)}

def henonTargetRow {p : ℕ} (d u : HénonX p) : Set (HénonV p) :=
  {v | ∃ w : HénonX p, w ∈ henonFibre d ∧ v = (d, w + u)}

def henonConnectionSet (p : ℕ) : Set (HénonV p) :=
  ⋃ d ∈ henonSelectedDirections p, henonSourceRow d

def henonNegateSet {p : ℕ} (S : Set (HénonV p)) : Set (HénonV p) :=
  {v | -v ∈ S}

def henonA {p : ℕ} (v : HénonV p) : HénonV p :=
  (v.2, v.1 + v.2)

def henonTargetSet (p : ℕ) : Set (HénonV p) :=
  ⋃ d ∈ henonSelectedDirections p, henonTargetRow d (henonF d)

/-- Claim 57279: the all-prime Hénon connection-set construction. -/
def henonConstructionAndTransport : Prop :=
  ∀ (p : ℕ), Nat.Prime p → p % 2 = 1 →
    henonConnectionSet p = henonNegateSet (henonConnectionSet p) ∧
      (0 : HénonV p) ∉ henonConnectionSet p ∧
      Submodule.span (ZMod p) (henonConnectionSet p) = ⊤ ∧
      henonQ '' henonConnectionSet p = henonTargetSet p

/-- Claim 57280: the fibres, coset shadows, and the linear shadow. -/
def henonFibreDimensionsAndLinearShadow : Prop :=
  ∀ (p : ℕ), Nat.Prime p → p % 2 = 1 →
    (henonFibre (henonE1 p) = henonFibre (-henonE1 p) ∧
        henonFibre (henonE1 p) =
          Submodule.span (ZMod p) ({henonE1 p} : Set (HénonX p)) ∧
      henonFibre (henonE2 p) = henonFibre (-henonE2 p) ∧
        henonFibre (henonE2 p) =
          Submodule.span (ZMod p) ({henonE1 p, henonE2 p} : Set (HénonX p)) ∧
      henonFibre (henonE3 p) = henonFibre (-henonE3 p) ∧
        henonFibre (henonE3 p) =
          Submodule.span (ZMod p) ({henonE1 p, henonE3 p} : Set (HénonX p)) ∧
      henonFibre (henonE2 p + henonE3 p) =
          henonFibre (-(henonE2 p + henonE3 p)) ∧
        henonFibre (henonE2 p + henonE3 p) = ⊤) ∧
    (∀ d : HénonX p, d ∈ henonSelectedDirections p →
      henonF d - d ∈ henonFibre d) ∧
    (∀ d : HénonX p, d ∈ henonSelectedDirections p →
      (henonQ '' henonSourceRow d = henonTargetRow d (henonF d) ∧
        henonA '' henonSourceRow d = henonTargetRow d d ∧
        henonTargetRow d (henonF d) = henonTargetRow d d)) ∧
    henonA (0 : HénonV p) = 0 ∧
    (∀ x y : HénonV p, henonA (x + y) = henonA x + henonA y) ∧
    (∀ (r : ZMod p) (x : HénonV p), henonA (r • x) = r • henonA x) ∧
    henonA '' henonConnectionSet p = henonQ '' henonConnectionSet p ∧
    henonA '' henonConnectionSet p = henonTargetSet p

end MathlibPlus.Open.AdmittedBatch
