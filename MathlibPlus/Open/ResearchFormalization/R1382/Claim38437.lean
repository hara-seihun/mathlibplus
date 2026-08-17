import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1382

private abbrev MaskBlock38437 := ZMod 8
private abbrev PrimeFiber38437 (q : ℕ) := ZMod q
private abbrev MaskPoint38437 (q : ℕ) := PrimeFiber38437 q × MaskBlock38437

private def blockwiseMap38437 {A B : Type*}
    (fiberMap : B → Equiv.Perm A) : Equiv.Perm (A × B) :=
  let e : (b : B) × A ≃ B × A := Equiv.sigmaEquivProd B A
  ((((Equiv.prodComm A B).trans e.symm).trans
      (Equiv.sigmaCongrRight fiberMap)).trans e).trans
    (Equiv.prodComm A B).symm

private def adjacentTranspositionChart38437 (q : ℕ)
    (μ : MaskBlock38437 → Bool) : Equiv.Perm (MaskPoint38437 q) :=
  blockwiseMap38437 (fun j =>
    if μ j then Equiv.swap (1 : PrimeFiber38437 q) 2
    else Equiv.refl (PrimeFiber38437 q))

private def hallCycle38437 (q : ℕ) : Equiv.Perm (MaskPoint38437 q) :=
  Equiv.addRight ((1 : PrimeFiber38437 q), (0 : MaskBlock38437))

private def outerInversion38437 (q : ℕ) : Equiv.Perm (MaskPoint38437 q) :=
  (Equiv.prodCongr (Equiv.neg (PrimeFiber38437 q))
      (Equiv.refl MaskBlock38437)).trans
    (Equiv.addRight ((0 : PrimeFiber38437 q), (1 : MaskBlock38437)))

private def sourceRegularCopy38437 (q : ℕ) :
    Subgroup (Equiv.Perm (MaskPoint38437 q)) :=
  Subgroup.closure
    ({hallCycle38437 q, outerInversion38437 q} :
      Set (Equiv.Perm (MaskPoint38437 q)))

private def targetRegularCopy38437 (q : ℕ) (μ : MaskBlock38437 → Bool) :
    Subgroup (Equiv.Perm (MaskPoint38437 q)) :=
  Subgroup.map
    (MulEquiv.toMonoidHom
      (MulAut.conj (adjacentTranspositionChart38437 q μ)))
    (sourceRegularCopy38437 q)

private def generatedMaskAction38437 (q : ℕ)
    (μ : MaskBlock38437 → Bool) :
    Subgroup (Equiv.Perm (MaskPoint38437 q)) :=
  Subgroup.closure
    ((sourceRegularCopy38437 q : Set (Equiv.Perm (MaskPoint38437 q))) ∪
      (targetRegularCopy38437 q μ : Set (Equiv.Perm (MaskPoint38437 q))))

private def orderedOrbital38437 {Ω : Type*}
    (H : Subgroup (Equiv.Perm Ω)) (p : Ω × Ω) : Set (Ω × Ω) :=
  Set.range (fun h : H =>
    ((h : Equiv.Perm Ω) p.1, (h : Equiv.Perm Ω) p.2))

private def orderedOrbitalFamily38437 {Ω : Type*}
    (H : Subgroup (Equiv.Perm Ω)) : Set (Set (Ω × Ω)) :=
  {O | ∃ p : Ω × Ω, O = orderedOrbital38437 H p}

private noncomputable def orderedOrbitalCount38437 {Ω : Type*}
    (H : Subgroup (Equiv.Perm Ω)) : ℕ :=
  Nat.card {O : Set (Ω × Ω) // O ∈ orderedOrbitalFamily38437 H}

private def unorderedOrbital38437 {Ω : Type*}
    (H : Subgroup (Equiv.Perm Ω)) (p : Sym2 Ω) : Set (Sym2 Ω) :=
  Set.range (fun h : H => Sym2.map (h : Equiv.Perm Ω) p)

private def unorderedOrbitalFamily38437 {Ω : Type*}
    (H : Subgroup (Equiv.Perm Ω)) : Set (Set (Sym2 Ω)) :=
  {O | ∃ p : Sym2 Ω, O = unorderedOrbital38437 H p}

private noncomputable def unorderedOrbitalCount38437 {Ω : Type*}
    (H : Subgroup (Equiv.Perm Ω)) : ℕ :=
  Nat.card {O : Set (Sym2 Ω) // O ∈ unorderedOrbitalFamily38437 H}

private def nonconstantMask38437 (μ : MaskBlock38437 → Bool) : Prop :=
  ∃ i j : MaskBlock38437, μ i ≠ μ j

private def maskHasPeriod38437 (μ : MaskBlock38437 → Bool) (d : ℕ) : Prop :=
  ∀ j : MaskBlock38437, μ (j + (d : MaskBlock38437)) = μ j

private def leastCyclicMaskPeriod38437
    (μ : MaskBlock38437 → Bool) (d : ℕ) : Prop :=
  (d = 2 ∨ d = 4 ∨ d = 8) ∧
    maskHasPeriod38437 μ d ∧
    ∀ e : ℕ, 0 < e → e < d → ¬ maskHasPeriod38437 μ e

private def stripLift38437 (q d : ℕ) (s : Fin d)
    (g : Equiv.Perm (PrimeFiber38437 q)) :
    Equiv.Perm (MaskPoint38437 q) :=
  blockwiseMap38437 (fun j =>
    if j.val % d = s.val then g else Equiv.refl (PrimeFiber38437 q))

private def hallKernelStripAction38437 (q d : ℕ) [NeZero q] :
    Subgroup (Equiv.Perm (MaskPoint38437 q)) :=
  Subgroup.closure
    {p | ∃ s : Fin d, ∃ g : alternatingGroup (PrimeFiber38437 q),
      p = stripLift38437 q d s (g : Equiv.Perm (PrimeFiber38437 q))}

private def controlPrime38437 (q : Fin 3) : ℕ :=
  if q.val = 0 then 3 else if q.val = 1 then 5 else 7

private noncomputable def aggregateUnorderedPeriodMultiplicity38437
    (d n : ℕ) : ℕ :=
  Nat.card
    {qm : Fin 3 × (MaskBlock38437 → Bool) //
      nonconstantMask38437 qm.2 ∧
      leastCyclicMaskPeriod38437 qm.2 d ∧
      unorderedOrbitalCount38437
        (generatedMaskAction38437 (controlPrime38437 qm.1) qm.2) = n}

private noncomputable def stripOrderedPeriodMultiplicity38437
    (q d n : ℕ) [NeZero q] : ℕ :=
  Nat.card
    {μ : MaskBlock38437 → Bool //
      nonconstantMask38437 μ ∧
      leastCyclicMaskPeriod38437 μ d ∧
      orderedOrbitalCount38437 (hallKernelStripAction38437 q d) = n}

private noncomputable def generatedDirectedPeriodMultiplicity38437
    (q d n : ℕ) [NeZero q] : ℕ :=
  Nat.card
    {μ : MaskBlock38437 → Bool //
      nonconstantMask38437 μ ∧
      leastCyclicMaskPeriod38437 μ d ∧
      orderedOrbitalCount38437 (generatedMaskAction38437 q μ) = n}

/-- Claim 38437: the q-indexed aggregate mask histogram, the per-q strip and
    directed-orbital histograms, and the one-mask q=11 controls are exact. -/
def claim38437 : Prop :=
  aggregateUnorderedPeriodMultiplicity38437 2 7 = 6 ∧
    aggregateUnorderedPeriodMultiplicity38437 4 6 = 36 ∧
    aggregateUnorderedPeriodMultiplicity38437 8 5 = 720 ∧
    (∀ (q : ℕ) [Fact q.Prime] [NeZero q],
      (q = 5 ∨ q = 7) →
      stripOrderedPeriodMultiplicity38437 q 2 96 = 2 ∧
        stripOrderedPeriodMultiplicity38437 q 4 80 = 12 ∧
        stripOrderedPeriodMultiplicity38437 q 8 72 = 240 ∧
        generatedDirectedPeriodMultiplicity38437 q 2 12 = 2 ∧
        generatedDirectedPeriodMultiplicity38437 q 4 10 = 12 ∧
        generatedDirectedPeriodMultiplicity38437 q 8 9 = 240) ∧
    (∀ (d : ℕ),
      d = 2 ∨ d = 4 ∨ d = 8 →
      ∃ μ : MaskBlock38437 → Bool,
        nonconstantMask38437 μ ∧
        leastCyclicMaskPeriod38437 μ d ∧
        orderedOrbitalCount38437 (hallKernelStripAction38437 11 d) =
          (if d = 2 then 96 else if d = 4 then 80 else 72) ∧
        orderedOrbitalCount38437 (generatedMaskAction38437 11 μ) =
          (if d = 2 then 12 else if d = 4 then 10 else 9) ∧
        unorderedOrbitalCount38437 (generatedMaskAction38437 11 μ) =
          (if d = 2 then 7 else if d = 4 then 6 else 5))

end MathlibPlus.Open.ResearchFormalization.R1382
