import Mathlib

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Claim14870

open Classical

/-- A fixed-length Dyck-word carrier.  `U` is `true` and `D` is `false`. -/
abbrev RawWord (n : ℕ) := Fin (2 * n) → Bool

private def upCount {n : ℕ} (w : RawWord n) (t : Fin (2 * n + 1)) : ℕ :=
  ((Finset.univ : Finset (Fin (2 * n))).filter
    (fun i => i.val < t.val ∧ w i = true)).card

private def downCount {n : ℕ} (w : RawWord n) (t : Fin (2 * n + 1)) : ℕ :=
  ((Finset.univ : Finset (Fin (2 * n))).filter
    (fun i => i.val < t.val ∧ w i = false)).card

private def isDyck {n : ℕ} (w : RawWord n) : Prop :=
  upCount w ⟨2 * n, by omega⟩ = n ∧
    ∀ t, downCount w t ≤ upCount w t

/-- The partition coordinates of the Dyck path, read from the last up-step. -/
private def upBefore {n : ℕ} (w : RawWord n) (i : Fin (2 * n)) : Finset (Fin (2 * n)) :=
  (Finset.univ : Finset (Fin (2 * n))).filter
    (fun j => j.val < i.val ∧ w j = true)

private def downBefore {n : ℕ} (w : RawWord n) (i : Fin (2 * n)) : Finset (Fin (2 * n)) :=
  (Finset.univ : Finset (Fin (2 * n))).filter
    (fun j => j.val < i.val ∧ w j = false)

private def shapePart {n : ℕ} (w : RawWord n) (r : Fin n) : ℕ :=
  let target := n - r.val - 1
  ((Finset.univ : Finset (Fin (2 * n))).filter
    (fun i => w i = true ∧ (upBefore w i).card = target)).sum
    (fun i => (downBefore w i).card)

private def shapeArea {n : ℕ} (w : RawWord n) : ℕ :=
  ∑ r : Fin n, shapePart w r

private def wordLE {n : ℕ} (u v : RawWord n) : Prop :=
  ∀ r : Fin n, shapePart u r ≤ shapePart v r

private def allDyck (n : ℕ) : Finset (RawWord n) :=
  (Finset.univ : Finset (RawWord n)).filter (fun w => isDyck w)

private def skewCells {n : ℕ} (lo hi : RawWord n) : Finset (Fin n × Fin n) :=
  (Finset.univ : Finset (Fin n × Fin n)).filter (fun c =>
    shapePart lo c.1 ≤ c.2.val ∧ c.2.val < shapePart hi c.1)

private def rookStrip {n : ℕ} (lo hi : RawWord n) : Prop :=
  (∀ r : Fin n, ((skewCells lo hi).filter (fun c => c.1 = r)).card ≤ 1) ∧
    (∀ c : Fin n, ((skewCells lo hi).filter (fun p => p.2 = c)).card ≤ 1)

private def intervalMember {n : ℕ} (lo hi μ : RawWord n) : Prop :=
  wordLE lo μ ∧ wordLE μ hi

private def listDyck (w : List Bool) : Prop :=
  w.count true = w.count false ∧
    ∀ k ≤ w.length,
      (w.take k).count false ≤ (w.take k).count true

private def listArea (w : List Bool) : ℕ :=
  ((Finset.univ : Finset (Fin w.length × Fin w.length)).filter
    (fun p => p.1.val < p.2.val ∧ w.get p.1 = false ∧ w.get p.2 = true)).card

/-- Split the suffix after the initial `U` at its first return to height zero. -/
def splitReturnAux : ℕ → List Bool → List Bool × List Bool
  | _, [] => ([], [])
  | level, x :: xs =>
      if x then
        let q := splitReturnAux (level + 1) xs
        (true :: q.1, q.2)
      else if level = 1 then
        ([], xs)
      else
        let q := splitReturnAux (level - 1) xs
        (false :: q.1, q.2)

private def firstReturnParts (w : List Bool) : List Bool × List Bool :=
  match w with
  | true :: rest => splitReturnAux 1 rest
  | _ => ([], [])

/-- The first-return recursive selector from Record 12.

For an odd-area word it recurses into the first odd-area first-return factor;
when both factors have even area, the odd cross-term permits the return-valley
`DU` to be toggled to `UD`.  The decreasing fuel is only an implementation
of recursion on a proper factor. -/
def canonicalSelectorFuel : ℕ → List Bool → List Bool
  | 0, w => w
  | fuel + 1, w =>
      match w with
      | true :: rest =>
          let parts := splitReturnAux 1 rest
          let A := parts.1
          let B := parts.2
          if Odd (listArea A) then
            true :: (canonicalSelectorFuel fuel A ++ [false] ++ B)
          else if Odd (listArea B) then
            true :: (A ++ [false] ++ canonicalSelectorFuel fuel B)
          else
            match B with
            | true :: tail => true :: (A ++ [true, false] ++ tail)
            | _ => w
      | _ => w

private def canonicalSelector (w : List Bool) : List Bool :=
  canonicalSelectorFuel w.length w

private def rawOfList {n : ℕ} (w : List Bool) : RawWord n :=
  fun i => w.getD i.val false

private def canonicalParent {n : ℕ} (w : RawWord n) : RawWord n :=
  rawOfList (canonicalSelector (List.ofFn w))

private def oddFacet {n : ℕ} (α τ : RawWord n) : Prop :=
  isDyck α ∧ isDyck τ ∧ Odd (shapeArea α) ∧
    wordLE α τ ∧ shapeArea τ = shapeArea α + 1

/-- Even grandparent choices forced by the two odd facets of an even upper. -/
private def forcedGrandparents {n : ℕ} (τ : RawWord n) : Finset (RawWord n) :=
  (allDyck n).filter (fun ρ =>
    Even (shapeArea ρ) ∧ wordLE ρ τ ∧ shapeArea τ = shapeArea ρ + 2 ∧
      ∃ α β : RawWord n,
        α ≠ β ∧ oddFacet α τ ∧ oddFacet β τ ∧
          canonicalParent α = ρ ∧ canonicalParent β = ρ)

/-- The singleton-or-forced-diamond basis vector selected for an upper shape. -/
noncomputable def canonicalBasis {n : ℕ} (τ : RawWord n) : RawWord n × RawWord n :=
  if _ : Odd (shapeArea τ) then
    (canonicalParent τ, τ)
  else
    let s := forcedGrandparents τ
    if h : s.Nonempty then
      (Classical.choose h, τ)
    else
      (τ, τ)

private abbrev Attachment (d : ℕ) := Fin (d + 1) → Fin (2 * (d + 1) + 1)

private def validAttachment {d : ℕ} (p : Attachment d) : Prop :=
  ∀ i, (p i).val ≤ 2 * i.val

private def attachmentList {d : ℕ} (p : Attachment d) : List ℕ :=
  List.ofFn (fun i : Fin (d + 1) => (p i).val)

private def insertUD (w : List Bool) (p : ℕ) : List Bool :=
  w.take p ++ [true, false] ++ w.drop p

private def insertUThenD (w : List Bool) (p : ℕ) : List Bool :=
  w.take p ++ [true] ++ w.drop p ++ [false]

private def dtsWord {d : ℕ} (p : Attachment d) : List Bool :=
  (attachmentList p).foldl (fun w i => insertUD w i) []

private def matchingWord {d : ℕ} (p : Attachment d) : List Bool :=
  (attachmentList p).foldl (fun w i => insertUThenD w i) []

/-- The exact DTS attachment carrier for the inverse-cup coefficients. -/
private def dtsCoefficient (d : ℕ) (lam mu : RawWord (d + 1)) : ℕ :=
  Fintype.card
    {p : Attachment d //
      validAttachment p ∧
        dtsWord p = List.ofFn lam ∧ matchingWord p = List.ofFn mu}

private def basisMember {n : ℕ} (σ μ : RawWord n) : Prop :=
  let b := canonicalBasis σ
  intervalMember b.1 b.2 μ ∧ (b.1 = b.2 ∨ rookStrip b.1 b.2)

private def rowExpansion (d : ℕ) (row : RawWord (d + 1))
    (y : RawWord (d + 1) → ℤ) : Prop :=
  ∀ μ, isDyck μ →
    (dtsCoefficient d row μ : ℤ) =
      (allDyck (d + 1)).sum (fun σ =>
        y σ * (if basisMember σ μ then 1 else 0))

private def nonnegativeCoordinates (d : ℕ) : Prop :=
  ∀ row : RawWord (d + 1), isDyck row →
    ∃ y : RawWord (d + 1) → ℤ,
      rowExpansion d row y ∧
        ∀ μ, isDyck μ → 0 ≤ y μ

private def rowFive : RawWord 6 :=
  ![true, true, true, false, true, false, false, true, false, false, true, false]

private def upperFive : RawWord 6 :=
  ![true, true, true, true, false, false, false, true, true, false, false, false]

private def selectorFailureAtFive : Prop :=
  isDyck rowFive ∧ isDyck upperFive ∧
    canonicalBasis upperFive = (upperFive, upperFive) ∧
    ∃ y : RawWord 6 → ℤ,
      rowExpansion 5 rowFive y ∧ y upperFive = (-1 : ℤ) ∧
        ∀ z : RawWord 6 → ℤ,
          rowExpansion 5 rowFive z → z upperFive = (-1 : ℤ)

/-- Claim 14870: the exact first-return selector is nonnegative through
 dimension four and its specified dimension-five row has a singleton basis
 vector whose forced coordinate is `-1`. -/
def claim14870 : Prop :=
  nonnegativeCoordinates 1 ∧
    nonnegativeCoordinates 2 ∧
    nonnegativeCoordinates 3 ∧
    nonnegativeCoordinates 4 ∧
    selectorFailureAtFive

end MathlibPlus.Open.ResearchFormalization.Claim14870
