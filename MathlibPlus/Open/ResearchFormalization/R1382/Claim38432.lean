import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1382.Claim38432

noncomputable section

abbrev MaskBlock38432 := ZMod 8
abbrev PrimeFiber38432 (q : ℕ) := ZMod q
abbrev MaskPoint38432 (q : ℕ) := PrimeFiber38432 q × MaskBlock38432

def blockwiseMap38432 {A B : Type*}
    (fiberMap : B → Equiv.Perm A) : Equiv.Perm (A × B) :=
  let e : (b : B) × A ≃ B × A := Equiv.sigmaEquivProd B A
  ((((Equiv.prodComm A B).trans e.symm).trans
      (Equiv.sigmaCongrRight fiberMap)).trans e).trans
    (Equiv.prodComm A B).symm

def adjacentTranspositionChart38432 (q : ℕ)
    (μ : MaskBlock38432 → Bool) : Equiv.Perm (MaskPoint38432 q) :=
  blockwiseMap38432 (fun j =>
    if μ j then Equiv.swap (1 : PrimeFiber38432 q) 2
    else Equiv.refl (PrimeFiber38432 q))

def hallCycle38432 (q : ℕ) : Equiv.Perm (MaskPoint38432 q) :=
  Equiv.addRight ((1 : PrimeFiber38432 q), (0 : MaskBlock38432))

def outerInversion38432 (q : ℕ) : Equiv.Perm (MaskPoint38432 q) :=
  (Equiv.prodCongr (Equiv.neg (PrimeFiber38432 q))
      (Equiv.refl MaskBlock38432)).trans
    (Equiv.addRight ((0 : PrimeFiber38432 q), (1 : MaskBlock38432)))

def sourceRegularCopy38432 (q : ℕ) :
    Subgroup (Equiv.Perm (MaskPoint38432 q)) :=
  Subgroup.closure
    ({hallCycle38432 q, outerInversion38432 q} :
      Set (Equiv.Perm (MaskPoint38432 q)))

def targetRegularCopy38432 (q : ℕ) (μ : MaskBlock38432 → Bool) :
    Subgroup (Equiv.Perm (MaskPoint38432 q)) :=
  Subgroup.map
    (MulEquiv.toMonoidHom
      (MulAut.conj (adjacentTranspositionChart38432 q μ)))
    (sourceRegularCopy38432 q)

def generatedMaskAction38432 (q : ℕ)
    (μ : MaskBlock38432 → Bool) :
    Subgroup (Equiv.Perm (MaskPoint38432 q)) :=
  Subgroup.closure
    ((sourceRegularCopy38432 q : Set (Equiv.Perm (MaskPoint38432 q))) ∪
      (targetRegularCopy38432 q μ : Set (Equiv.Perm (MaskPoint38432 q))))

def orderedOrbital38432 {Ω : Type*}
    (H : Subgroup (Equiv.Perm Ω)) (p : Ω × Ω) : Set (Ω × Ω) :=
  Set.range (fun h : H =>
    ((h : Equiv.Perm Ω) p.1, (h : Equiv.Perm Ω) p.2))

def orderedOrbitalFamily38432 {Ω : Type*}
    (H : Subgroup (Equiv.Perm Ω)) : Set (Set (Ω × Ω)) :=
  {O | ∃ p : Ω × Ω, O = orderedOrbital38432 H p}

noncomputable def orderedOrbitalCount38432 {Ω : Type*}
    (H : Subgroup (Equiv.Perm Ω)) : ℕ :=
  Nat.card {O : Set (Ω × Ω) // O ∈ orderedOrbitalFamily38432 H}

def unorderedOrbital38432 {Ω : Type*}
    (H : Subgroup (Equiv.Perm Ω)) (p : Sym2 Ω) : Set (Sym2 Ω) :=
  Set.range (fun h : H => Sym2.map (h : Equiv.Perm Ω) p)

def unorderedOrbitalFamily38432 {Ω : Type*}
    (H : Subgroup (Equiv.Perm Ω)) : Set (Set (Sym2 Ω)) :=
  {O | ∃ p : Sym2 Ω, O = unorderedOrbital38432 H p}

noncomputable def unorderedOrbitalCount38432 {Ω : Type*}
    (H : Subgroup (Equiv.Perm Ω)) : ℕ :=
  Nat.card {O : Set (Sym2 Ω) // O ∈ unorderedOrbitalFamily38432 H}

def nonconstantMask38432 (μ : MaskBlock38432 → Bool) : Prop :=
  ∃ i j : MaskBlock38432, μ i ≠ μ j

def maskHasPeriod38432 (μ : MaskBlock38432 → Bool) (d : ℕ) : Prop :=
  ∀ j : MaskBlock38432, μ (j + (d : MaskBlock38432)) = μ j

def leastCyclicMaskPeriod38432
    (μ : MaskBlock38432 → Bool) (d : ℕ) : Prop :=
  (d = 2 ∨ d = 4 ∨ d = 8) ∧
    maskHasPeriod38432 μ d ∧
    ∀ e : ℕ, 0 < e → e < d → ¬ maskHasPeriod38432 μ e

/-- Claim 38432: the exact generated action has the universal orbital counts
    indexed by the least cyclic period of every nonconstant mask. -/
def claim38432 : Prop :=
  ∀ μ : MaskBlock38432 → Bool,
    nonconstantMask38432 μ →
    ∃ d : ℕ,
      leastCyclicMaskPeriod38432 μ d ∧
      ∀ q : ℕ, Nat.Prime q → 5 ≤ q →
        ((d = 2 ∧
            orderedOrbitalCount38432 (generatedMaskAction38432 q μ) = 12 ∧
            unorderedOrbitalCount38432 (generatedMaskAction38432 q μ) = 7) ∨
          (d = 4 ∧
            orderedOrbitalCount38432 (generatedMaskAction38432 q μ) = 10 ∧
            unorderedOrbitalCount38432 (generatedMaskAction38432 q μ) = 6) ∨
          (d = 8 ∧
            orderedOrbitalCount38432 (generatedMaskAction38432 q μ) = 9 ∧
            unorderedOrbitalCount38432 (generatedMaskAction38432 q μ) = 5))

end

end MathlibPlus.Open.ResearchFormalization.R1382.Claim38432
