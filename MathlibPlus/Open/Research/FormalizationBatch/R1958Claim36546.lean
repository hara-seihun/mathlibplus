import MathlibPlus.Open.FormalizationBatch.SetSystems

namespace MathlibPlus.Open.Research.FormalizationBatch.R1958Claim36546

noncomputable section

open scoped BigOperators
open MathlibPlus.Open.FormalizationBatch.SetSystems

/-- The golden-ratio constant in the incidence estimate. -/
def incidenceAlpha36546 : ℝ :=
  (3 - Real.sqrt 5) / 2

/-- The splitter entropy base. -/
def incidenceEntropyBase36546 (δ : ℝ) : ℝ :=
  δ⁻¹ * Real.rpow (1 - δ) (-(1 - δ) / δ)

/-- The structured-factor base. -/
def structuredFactorBase36546
    (k D c β : ℕ) : ℝ :=
  ((D * (k - 1) : ℕ) : ℝ) *
    Real.rpow
      (1 + (((D * (k - 1) : ℕ) : ℝ)⁻¹))
      ((β : ℝ) + (c : ℝ) * incidenceAlpha36546⁻¹)

/-- The actual coordinates used by a finite set family. -/
def familyGroundCoordinates36546
    {α : Type} [DecidableEq α]
    (F : Finset (Finset α)) : Finset α :=
  F.biUnion (fun A => A)

/-- The member-support pattern of a ground coordinate. -/
def familyMemberSupport36546
    {α : Type} [DecidableEq α]
    (F : Finset (Finset α)) (x : α) : Finset (Finset α) :=
  F.filter (fun A => x ∈ A)

/-- The distinct nonempty incidence support patterns. -/
def familySupportPatterns36546
    {α : Type} [DecidableEq α]
    (F : Finset (Finset α)) : Finset (Finset (Finset α)) :=
  (familyGroundCoordinates36546 F).image (familyMemberSupport36546 F)

/-- Laminarity of a family of support patterns. -/
def laminar36546
    {α : Type} [DecidableEq α]
    (L : Finset (Finset (Finset α))) : Prop :=
  ∀ S ∈ L, ∀ T ∈ L,
    S ⊆ T ∨ T ⊆ S ∨ Disjoint S T

/-- Union-closure of one support-pattern layer. -/
def unionClosed36546
    {α : Type} [DecidableEq α]
    (U : Finset (Finset (Finset α))) : Prop :=
  ∀ S ∈ U, ∀ T ∈ U, S ∪ T ∈ U

/-- The union of at most c union-closed support layers. -/
def unionClosedLayerUnion36546
    {α : Type} [DecidableEq α] (c : ℕ)
    (U : Fin c → Finset (Finset (Finset α))) :
    Finset (Finset (Finset α)) :=
  (Finset.univ : Finset (Fin c)).biUnion U

/-- A structured factor with its laminar, bounded, union-closed, and
exceptional support layers made explicit. -/
def structuredFactorFamily36546
    {α : Type} [DecidableEq α]
    (F : Finset (Finset α)) (r D c β : ℕ) : Prop :=
  uniformFamily F r ∧
    ∃ (L B E : Finset (Finset (Finset α)))
      (U : Fin c → Finset (Finset (Finset α))),
      familySupportPatterns36546 F =
          L ∪ B ∪ unionClosedLayerUnion36546 c U ∪ E ∧
        Disjoint L B ∧
        Disjoint L (unionClosedLayerUnion36546 c U) ∧
        Disjoint L E ∧
        Disjoint B (unionClosedLayerUnion36546 c U) ∧
        Disjoint B E ∧
        Disjoint (unionClosedLayerUnion36546 c U) E ∧
        laminar36546 L ∧
        (∀ S ∈ B, S.card ≤ D) ∧
        (∀ j : Fin c, unionClosed36546 (U j)) ∧
        E.card ≤ β * r

/-- A factor records its coordinate block, family, and uniformity. -/
abbrev FactorSpec36546 (α : Type) :=
  Finset α × Finset (Finset α) × ℕ

def factorBlock36546
    {α : Type} (s : FactorSpec36546 α) : Finset α :=
  s.1

def factorFamily36546
    {α : Type} (s : FactorSpec36546 α) : Finset (Finset α) :=
  s.2.1

def factorUniformity36546
    {α : Type} (s : FactorSpec36546 α) : ℕ :=
  s.2.2

/-- The family obtained by taking unions of one member from every factor. -/
def directProductFamily36546
    {α : Type} [DecidableEq α] :
    List (FactorSpec36546 α) → Finset (Finset α)
  | [] => {∅}
  | s :: ss =>
      (directProductFamily36546 ss).biUnion
        (fun A => (factorFamily36546 s).image (fun B => A ∪ B))

/-- The sum of the factor uniformities. -/
def factorUniformitySum36546
    {α : Type} (ss : List (FactorSpec36546 α)) : ℕ :=
  (ss.map (factorUniformity36546 (α := α))).sum

/-- Pairwise disjointness of the factor coordinate blocks. -/
def factorBlocksDisjoint36546
    {α : Type} [DecidableEq α] :
    List (FactorSpec36546 α) → Prop
  | [] => True
  | s :: ss =>
      (∀ t ∈ ss, Disjoint (factorBlock36546 s) (factorBlock36546 t)) ∧
        factorBlocksDisjoint36546 ss

/-- Every factor family is supported on its declared coordinate block. -/
def factorFamiliesWithinBlocks36546
    {α : Type} [DecidableEq α]
    (ss : List (FactorSpec36546 α)) : Prop :=
  ∀ s ∈ ss, ∀ A ∈ factorFamily36546 s,
    A ⊆ factorBlock36546 s

/-- A direct product of structured factors on disjoint coordinate blocks. -/
def structuredProductCore36546
    {α : Type} [DecidableEq α]
    (G : Finset (Finset α)) (r k D c β : ℕ) : Prop :=
  ∃ ss : List (FactorSpec36546 α),
    directProductFamily36546 ss = G ∧
      factorUniformitySum36546 ss = r ∧
      factorBlocksDisjoint36546 ss ∧
      factorFamiliesWithinBlocks36546 ss ∧
      (∀ s ∈ ss,
        structuredFactorFamily36546
            (factorFamily36546 (α := α) s)
            (factorUniformity36546 (α := α) s) D c β ∧
          ¬ containsSunflower (factorFamily36546 (α := α) s) k)

/-- A residual class has the nonconstant-coordinate alternative. -/
def hasDeltaSplitter36546
    {α : Type} [DecidableEq α]
    (G : Finset (Finset α)) (δ : ℝ) : Prop :=
  ∃ x : α, deltaSplitter (α := α) G δ x

/-- The adaptive incidence entropy theorem, including the special value of
its splitter base at delta equal to one third. -/
def adaptiveIncidenceEntropyBound_claim36546 : Prop :=
  ∀ {α : Type} [DecidableEq α]
    (F : Finset (Finset α)) (n k : ℕ) (δ : ℝ)
    (D c β : ℕ),
    3 ≤ k →
    0 < δ →
    δ < 1 →
    uniformFamily F n →
    ¬ containsSunflower F k →
    (∀ (Q1 Q0 : Finset α),
      Q1 ∩ Q0 = ∅ →
      let G := residualRestriction F Q1 Q0
      1 < G.card →
        hasDeltaSplitter36546 G δ ∨
          structuredProductCore36546 G (n - Q1.card) k D c β) →
    (F.card : ℝ) ≤
        (max
          (incidenceEntropyBase36546 δ)
          (structuredFactorBase36546 k D c β)) ^ n ∧
      incidenceEntropyBase36546 (1 / 3 : ℝ) = 27 / 4

end

end MathlibPlus.Open.Research.FormalizationBatch.R1958Claim36546
