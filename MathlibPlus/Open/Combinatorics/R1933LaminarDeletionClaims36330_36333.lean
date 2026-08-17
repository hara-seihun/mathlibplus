import Mathlib

open scoped BigOperators Classical
noncomputable section

namespace MathlibPlus.Open.Combinatorics.R1933LaminarDeletion

private def distinctUniformFamily {α : Type*} [DecidableEq α]
    {m n : ℕ} (F : Fin m → Finset α) : Prop :=
  Function.Injective F ∧ ∀ i : Fin m, (F i).card = n

private def coordinateSupport {α : Type*} [DecidableEq α]
    {m : ℕ} (F : Fin m → Finset α) (x : α) : Finset (Fin m) :=
  Finset.univ.filter (fun i => x ∈ F i)

private def groundCoordinates {α : Type*} [DecidableEq α]
    {m : ℕ} (F : Fin m → Finset α) : Finset α :=
  Finset.univ.biUnion (fun i => F i)

private def supportPatterns {α : Type*} [DecidableEq α]
    {m : ℕ} (F : Fin m → Finset α) : Finset (Finset (Fin m)) :=
  (groundCoordinates F).image (coordinateSupport F) |>.filter
    (fun S => S.Nonempty)

private def laminarSupportFamily {m : ℕ}
    (S : Finset (Finset (Fin m))) : Prop :=
  ∀ A ∈ S, ∀ B ∈ S,
    A ⊆ B ∨ B ⊆ A ∨ Disjoint A B

private def pairwiseDisjointIndices {α : Type*} [DecidableEq α]
    {m : ℕ} (F : Fin m → Finset α) (I : Finset (Fin m)) : Prop :=
  ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (F i) (F j)

private def matchingNumber {α : Type*} [DecidableEq α]
    {m : ℕ} (F : Fin m → Finset α) : ℕ :=
  (Finset.univ.powerset.filter (pairwiseDisjointIndices F)).sup Finset.card

private def pairwiseIntersecting {α : Type*} [DecidableEq α]
    {m : ℕ} (F : Fin m → Finset α) : Prop :=
  ∀ i j : Fin m, i ≠ j → ¬Disjoint (F i) (F j)

private def indexedSunflower {α : Type*} [DecidableEq α]
    {m k : ℕ} (F : Fin m → Finset α) (I : Fin k → Fin m) : Prop :=
  Function.Injective I ∧
    ∃ C : Finset α,
      ∀ a b : Fin k, a ≠ b → F (I a) ∩ F (I b) = C

private def kSunflowerFree {α : Type*} [DecidableEq α]
    {m k : ℕ} (F : Fin m → Finset α) : Prop :=
  ¬∃ I : Fin k → Fin m, indexedSunflower F I

private def setFamilyUniform {α : Type*} [DecidableEq α]
    (G : Finset (Finset α)) (n : ℕ) : Prop :=
  ∀ A ∈ G, A.card = n

private def setFamilySunflower {α : Type*} [DecidableEq α]
    (G : Finset (Finset α)) (k : ℕ) : Prop :=
  ∃ P : Finset (Finset α), P ⊆ G ∧ P.card = k ∧
    ∃ C : Finset α,
      ∀ A ∈ P, ∀ B ∈ P, A ≠ B → A ∩ B = C

private def setFamilySunflowerFree {α : Type*} [DecidableEq α]
    (G : Finset (Finset α)) (k : ℕ) : Prop :=
  ¬setFamilySunflower G k

private def setFamilyGroundCoordinates {α : Type*} [DecidableEq α]
    (G : Finset (Finset α)) : Finset α :=
  G.biUnion id

private def setFamilyCoordinateSupport {α : Type*} [DecidableEq α]
    (G : Finset (Finset α)) (x : α) : Finset (Finset α) :=
  G.filter (fun A => x ∈ A)

private def setFamilySupportPatterns {α : Type*} [DecidableEq α]
    (G : Finset (Finset α)) : Finset (Finset (Finset α)) :=
  (setFamilyGroundCoordinates G).image
      (setFamilyCoordinateSupport G) |>.filter
    (fun S => S.Nonempty)

private def setFamilyLaminarSupports {α : Type*} [DecidableEq α]
    (G : Finset (Finset α)) : Prop :=
  ∀ S ∈ setFamilySupportPatterns G, ∀ T ∈ setFamilySupportPatterns G,
    S ⊆ T ∨ T ⊆ S ∨ Disjoint S T

private def supportsOutsideLaminar {α : Type*} [DecidableEq α]
    {m : ℕ} (F : Fin m → Finset α) (H : Finset α) : Prop :=
  H ⊆ groundCoordinates F ∧
    ∀ x, x ∉ H → ∀ y, y ∉ H →
      coordinateSupport F x ⊆ coordinateSupport F y ∨
        coordinateSupport F y ⊆ coordinateSupport F x ∨
        Disjoint (coordinateSupport F x) (coordinateSupport F y)

private def traceClass {α : Type*} [DecidableEq α]
    {m : ℕ} (F : Fin m → Finset α) (H T : Finset α) : Finset (Fin m) :=
  Finset.univ.filter (fun i => F i ∩ H = T)

private def residualFamily {α : Type*} [DecidableEq α]
    {m : ℕ} (F : Fin m → Finset α) (H T : Finset α) :
    Finset (Finset α) :=
  (traceClass F H T).image (fun i => F i \ T)

private def setFamilyMatchingNumber {α : Type*} [DecidableEq α]
    (G : Finset (Finset α)) : ℕ :=
  (G.powerset.filter
    (fun P => ∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B)).sup Finset.card

private def conflictGraph {m : ℕ}
    (B : Finset (Finset (Fin m))) : SimpleGraph (Fin m) :=
  SimpleGraph.fromRel (fun i j => ∃ S ∈ B, i ∈ S ∧ j ∈ S)

private def conflictDegree {m : ℕ}
    (B : Finset (Finset (Fin m))) (i : Fin m) : ℕ :=
  (Finset.univ.filter (fun j => (conflictGraph B).Adj i j)).card

private def properConflictColoring {m r : ℕ}
    (B : Finset (Finset (Fin m))) (color : Fin m → Fin r) : Prop :=
  ∀ i j, (conflictGraph B).Adj i j → color i ≠ color j

/-- Claim 36330: exact exceptional-coordinate traces give distinct uniform,
`k`-sunflower-free laminar residual families and the exact trace sum. -/
def linearLaminarDeletionBound_claim36330 : Prop :=
  ∀ (α : Type*) [DecidableEq α]
    (m n k h : ℕ) (F : Fin m → Finset α) (H : Finset α),
    distinctUniformFamily (n := n) F →
    H.card = h →
    1 ≤ n →
    3 ≤ k →
    kSunflowerFree (k := k) F →
    supportsOutsideLaminar F H →
    let q : ℝ := (k - 1 : ℝ)
    (∀ T : Finset α, T ⊆ H →
      (residualFamily F H T).card = (traceClass F H T).card ∧
        setFamilyUniform (residualFamily F H T) (n - T.card) ∧
        setFamilySunflowerFree (residualFamily F H T) k ∧
        setFamilyLaminarSupports (residualFamily F H T) ∧
        ((residualFamily F H T).card : ℝ) ≤
          q ^ ((n : ℤ) - (T.card : ℤ))) ∧
      m = ∑ T ∈ H.powerset, (traceClass F H T).card ∧
      (m : ℝ) ≤
        ∑ T ∈ H.powerset,
          q ^ ((n : ℤ) - (T.card : ℤ)) ∧
      (∑ T ∈ H.powerset,
          q ^ ((n : ℤ) - (T.card : ℤ))) =
        q ^ n * (1 + q⁻¹) ^ h ∧
      (m : ℝ) ≤ q ^ n * (1 + q⁻¹) ^ h

/-- Claim 36331: the empty trace keeps the matching-number parameter in the
laminar bound, with the bounded-matching and three-sunflower special cases. -/
def matchingNumberSharpenedDeletionBound_claim36331 : Prop :=
  ∀ (α : Type*) [DecidableEq α]
    (m n k h : ℕ) (F : Fin m → Finset α) (H : Finset α),
    distinctUniformFamily (n := n) F →
    H.card = h →
    1 ≤ n →
    3 ≤ k →
    kSunflowerFree (k := k) F →
    supportsOutsideLaminar F H →
    setFamilyMatchingNumber (residualFamily F H ∅) ≤ matchingNumber F ∧
      let q : ℝ := (k - 1 : ℝ)
      (m : ℝ) ≤
        q ^ n *
          ((1 + q⁻¹) ^ h -
            (q - (matchingNumber F : ℝ)) / q) ∧
        (matchingNumber F ≤ k - 2 →
          (m : ℝ) ≤ q ^ n * ((1 + q⁻¹) ^ h - 1 / q)) ∧
        (k = 3 ∧ pairwiseIntersecting F →
          (m : ℝ) ≤
            (2 : ℝ) ^ n * ((3 / 2 : ℝ) ^ h - 1 / 2))

/-- Claim 36332: a linear exceptional-coordinate count gives a fixed-base
exponential bound. -/
def fixedBaseLinearDefectBound_claim36332 : Prop :=
  ∀ (α : Type*) [DecidableEq α]
    (m n k h : ℕ) (F : Fin m → Finset α) (H : Finset α) (β : ℝ),
    distinctUniformFamily (n := n) F →
    H.card = h →
    1 ≤ n →
    3 ≤ k →
    kSunflowerFree (k := k) F →
    supportsOutsideLaminar F H →
    (h : ℝ) ≤ β * (n : ℝ) →
    (m : ℝ) ≤
      (((k - 1 : ℝ) *
        (1 + (k - 1 : ℝ)⁻¹) ^ β) ^ n)

/-- Claim 36333: the bounded-support conflict graph has maximum degree at
most `(D-1)n` and admits the stated greedy coloring. -/
def boundedSupportConflictColoring_claim36333 : Prop :=
  ∀ (α : Type*) [DecidableEq α]
    (m n D : ℕ) (F : Fin m → Finset α)
    (L B : Finset (Finset (Fin m))),
    distinctUniformFamily (n := n) F →
    supportPatterns F = L ∪ B →
    Disjoint L B →
    laminarSupportFamily L →
    (∀ S ∈ B, S.card ≤ D) →
    (∀ i : Fin m, (B.filter (fun S => i ∈ S)).card ≤ n) ∧
      (∀ i : Fin m, conflictDegree B i ≤ (D - 1) * n) ∧
      ∃ color : Fin m → Fin (1 + (D - 1) * n),
        properConflictColoring B color

end MathlibPlus.Open.Combinatorics.R1933LaminarDeletion
