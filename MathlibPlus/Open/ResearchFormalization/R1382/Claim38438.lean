import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1382

private abbrev MaskBlock38438 := ZMod 8
private abbrev PrimeFiber38438 (q : ℕ) := ZMod q
private abbrev MaskPoint38438 (q : ℕ) := PrimeFiber38438 q × MaskBlock38438

private def blockwiseMap38438 {A B : Type*}
    (fiberMap : B → Equiv.Perm A) : Equiv.Perm (A × B) :=
  let e : (b : B) × A ≃ B × A := Equiv.sigmaEquivProd B A
  ((((Equiv.prodComm A B).trans e.symm).trans
      (Equiv.sigmaCongrRight fiberMap)).trans e).trans
    (Equiv.prodComm A B).symm

private def adjacentTranspositionChart38438 (q : ℕ)
    (μ : MaskBlock38438 → Bool) : Equiv.Perm (MaskPoint38438 q) :=
  blockwiseMap38438 (fun j =>
    if μ j then Equiv.swap (1 : PrimeFiber38438 q) 2
    else Equiv.refl (PrimeFiber38438 q))

private def hallCycle38438 (q : ℕ) : Equiv.Perm (MaskPoint38438 q) :=
  Equiv.addRight ((1 : PrimeFiber38438 q), (0 : MaskBlock38438))

private def outerInversion38438 (q : ℕ) : Equiv.Perm (MaskPoint38438 q) :=
  (Equiv.prodCongr (Equiv.neg (PrimeFiber38438 q))
      (Equiv.refl MaskBlock38438)).trans
    (Equiv.addRight ((0 : PrimeFiber38438 q), (1 : MaskBlock38438)))

private def sourceRegularCopy38438 (q : ℕ) :
    Subgroup (Equiv.Perm (MaskPoint38438 q)) :=
  Subgroup.closure
    ({hallCycle38438 q, outerInversion38438 q} :
      Set (Equiv.Perm (MaskPoint38438 q)))

private def targetRegularCopy38438 (q : ℕ) (μ : MaskBlock38438 → Bool) :
    Subgroup (Equiv.Perm (MaskPoint38438 q)) :=
  Subgroup.map
    (MulEquiv.toMonoidHom
      (MulAut.conj (adjacentTranspositionChart38438 q μ)))
    (sourceRegularCopy38438 q)

private def generatedMaskAction38438 (q : ℕ)
    (μ : MaskBlock38438 → Bool) :
    Subgroup (Equiv.Perm (MaskPoint38438 q)) :=
  Subgroup.closure
    ((sourceRegularCopy38438 q : Set (Equiv.Perm (MaskPoint38438 q))) ∪
      (targetRegularCopy38438 q μ : Set (Equiv.Perm (MaskPoint38438 q))))

private def regularCopy38438 {Ω : Type*} [Fintype Ω]
    (H : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ x y : Ω, ∃! h : H, (h : Equiv.Perm Ω) x = y

private def conjugatesCopies38438 {Ω : Type*}
    (u : Equiv.Perm Ω) (R T : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ g : Equiv.Perm Ω,
    g ∈ T ↔ ∃ r : Equiv.Perm Ω, r ∈ R ∧ g = u * r * u⁻¹

private def generatedConjugacy38438 {Ω : Type*}
    (H R T : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∃ h : H, ∀ g : Equiv.Perm Ω,
    g ∈ T ↔ ∃ r : Equiv.Perm Ω, r ∈ R ∧
      g = (h : Equiv.Perm Ω) * r * (h : Equiv.Perm Ω)⁻¹

private def inOrderedTwoClosure38438 {Ω : Type*}
    (H : Subgroup (Equiv.Perm Ω)) (u : Equiv.Perm Ω) : Prop :=
  ∀ x y : Ω, ∃ h : H,
    (h : Equiv.Perm Ω) x = u x ∧ (h : Equiv.Perm Ω) y = u y

private def relationInvariant38438 {Ω : Type*}
    (E : Ω → Ω → Prop) (H : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ h : H, ∀ x y : Ω,
    E x y ↔ E ((h : Equiv.Perm Ω) x) ((h : Equiv.Perm Ω) y)

private def relationAutomorphism38438 {Ω : Type*}
    (E : Ω → Ω → Prop) (u : Equiv.Perm Ω) : Prop :=
  ∀ x y : Ω, E x y ↔ E (u x) (u y)

private def nonconstantMask38438 (μ : MaskBlock38438 → Bool) : Prop :=
  ∃ i j : MaskBlock38438, μ i ≠ μ j

private abbrev InflatedPoint38438 (r q : ℕ) :=
  ZMod r × (ZMod q × ZMod 8)

private def inflatedHallCycle38438 (r q : ℕ) :
    Equiv.Perm (InflatedPoint38438 r q) :=
  Equiv.addRight
    ((1 : ZMod r), ((1 : ZMod q), (0 : ZMod 8)))

private def inflatedOuterInversion38438 (r q : ℕ) :
    Equiv.Perm (InflatedPoint38438 r q) :=
  (Equiv.prodCongr (Equiv.neg (ZMod r))
      (Equiv.prodCongr (Equiv.neg (ZMod q)) (Equiv.refl (ZMod 8)))).trans
    (Equiv.addRight ((0 : ZMod r), ((0 : ZMod q), (1 : ZMod 8))))

private def inflatedSourceRegularCopy38438 (r q : ℕ) :
    Subgroup (Equiv.Perm (InflatedPoint38438 r q)) :=
  Subgroup.closure
    ({inflatedHallCycle38438 r q, inflatedOuterInversion38438 r q} :
      Set (Equiv.Perm (InflatedPoint38438 r q)))

private def inflatedChart38438 (r q : ℕ) (μ : MaskBlock38438 → Bool) :
    Equiv.Perm (InflatedPoint38438 r q) :=
  Equiv.prodCongr (Equiv.refl (ZMod r))
    (adjacentTranspositionChart38438 q μ)

private def inflatedTargetRegularCopy38438 (r q : ℕ)
    (μ : MaskBlock38438 → Bool) :
    Subgroup (Equiv.Perm (InflatedPoint38438 r q)) :=
  Subgroup.map
    (MulEquiv.toMonoidHom (MulAut.conj (inflatedChart38438 r q μ)))
    (inflatedSourceRegularCopy38438 r q)

private def inflatedGeneratedAction38438 (r q : ℕ)
    (μ : MaskBlock38438 → Bool) :
    Subgroup (Equiv.Perm (InflatedPoint38438 r q)) :=
  Subgroup.closure
    ((inflatedSourceRegularCopy38438 r q :
        Set (Equiv.Perm (InflatedPoint38438 r q))) ∪
      (inflatedTargetRegularCopy38438 r q μ :
        Set (Equiv.Perm (InflatedPoint38438 r q))))

/-- Claim 38438: nonconjugacy inside the generated action is harmless because
    the explicit chart is in ordered two-closure, both before and after the
    stated distinct-odd-prime inflation, so it cannot obstruct any invariant
    binary relation or ordinary undirected graph. -/
def claim38438 : Prop :=
  (∀ (q : ℕ) [Fact q.Prime] [NeZero q],
    5 ≤ q →
    ∀ μ : MaskBlock38438 → Bool, nonconstantMask38438 μ →
      let R := sourceRegularCopy38438 q
      let T := targetRegularCopy38438 q μ
      let X := generatedMaskAction38438 q μ
      regularCopy38438 R ∧
        regularCopy38438 T ∧
        conjugatesCopies38438 (adjacentTranspositionChart38438 q μ) R T ∧
        inOrderedTwoClosure38438 X (adjacentTranspositionChart38438 q μ) ∧
        (¬ generatedConjugacy38438 X R T →
          ∀ E : MaskPoint38438 q → MaskPoint38438 q → Prop,
            relationInvariant38438 E R →
            relationInvariant38438 E T →
            relationAutomorphism38438 E
              (adjacentTranspositionChart38438 q μ))) ∧
  (∀ (r q : ℕ) [Fact r.Prime] [Fact q.Prime] [NeZero r] [NeZero q],
    Odd r → r ≠ q → 5 ≤ q →
    ∀ μ : MaskBlock38438 → Bool, nonconstantMask38438 μ →
      let R := inflatedSourceRegularCopy38438 r q
      let T := inflatedTargetRegularCopy38438 r q μ
      let X := inflatedGeneratedAction38438 r q μ
      regularCopy38438 R ∧
        regularCopy38438 T ∧
        conjugatesCopies38438 (inflatedChart38438 r q μ) R T ∧
        inOrderedTwoClosure38438 X (inflatedChart38438 r q μ) ∧
        (¬ generatedConjugacy38438 X R T →
          ∀ E : InflatedPoint38438 r q → InflatedPoint38438 r q → Prop,
            relationInvariant38438 E R →
            relationInvariant38438 E T →
            relationAutomorphism38438 E (inflatedChart38438 r q μ)))

end MathlibPlus.Open.ResearchFormalization.R1382
