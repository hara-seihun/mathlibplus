import Mathlib

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Claim14873

open Classical

/-- The fixed Catalan-shape carrier used by the dimension-seven odd-parent
coordinate system.  A word has `n` up-steps and `n` down-steps. -/
private abbrev RawWord (n : ℕ) := Fin (2 * n) → Bool

private def upCount {n : ℕ} (w : RawWord n) (t : Fin (2 * n + 1)) : ℕ :=
  ((Finset.univ : Finset (Fin (2 * n))).filter
    (fun i => i.val < t.val ∧ w i = true)).card

private def downCount {n : ℕ} (w : RawWord n) (t : Fin (2 * n + 1)) : ℕ :=
  ((Finset.univ : Finset (Fin (2 * n))).filter
    (fun i => i.val < t.val ∧ w i = false)).card

private def isDyck {n : ℕ} (w : RawWord n) : Prop :=
  upCount w ⟨2 * n, by omega⟩ = n ∧
    ∀ t, downCount w t ≤ upCount w t

private abbrev Shape := {w : RawWord 8 // isDyck w}

private def inversionCells (w : RawWord 8) : Finset (Fin 16 × Fin 16) :=
  (Finset.univ : Finset (Fin 16 × Fin 16)).filter
    (fun p => p.1.val < p.2.val ∧ w p.1 = false ∧ w p.2 = true)

private def shapeArea (σ : Shape) : ℕ :=
  (inversionCells σ.1).card

private def shapeLE (ρ σ : Shape) : Prop :=
  inversionCells ρ.1 ⊆ inversionCells σ.1

private def rookStrip (ρ σ : Shape) : Prop :=
  let skew := inversionCells σ.1 \ inversionCells ρ.1
  (∀ i : Fin 16, (skew.filter (fun c => c.1 = i)).card ≤ 1) ∧
    (∀ j : Fin 16, (skew.filter (fun c => c.2 = j)).card ≤ 1)

private def parentEdge (σ ρ : Shape) : Prop :=
  Odd (shapeArea σ) ∧ Even (shapeArea ρ) ∧ shapeLE ρ σ ∧
    shapeArea σ = shapeArea ρ + 1

private def oddFacet (α τ : Shape) : Prop :=
  Odd (shapeArea α) ∧ shapeLE α τ ∧ shapeArea τ = shapeArea α + 1

private def oddFacets (ρ τ : Shape) : Finset Shape :=
  (Finset.univ : Finset Shape).filter (fun α =>
    oddFacet α τ ∧ parentEdge α ρ)

/-- The actual rank-two Boolean candidates.  The two-element facet set is the
source's pair `α, β`; `rookStrip` is the exact Boolean-interval condition. -/
private def potentialDiamond (ρ τ : Shape) : Prop :=
  Even (shapeArea ρ) ∧ Even (shapeArea τ) ∧ shapeLE ρ τ ∧
    shapeArea τ = shapeArea ρ + 2 ∧ rookStrip ρ τ ∧
    (oddFacets ρ τ).card = 2

private def boolNat (b : Bool) : ℕ :=
  if b then 1 else 0

private def parentVariables (p : Shape → Shape → Bool) : Prop :=
  ∀ σ,
    (∀ ρ, ¬ parentEdge σ ρ → p σ ρ = false) ∧
      (Odd (shapeArea σ) →
        (∑ ρ ∈ (Finset.univ : Finset Shape).filter (parentEdge σ),
            boolNat (p σ ρ)) = 1)

/-- `d_(τ,ρ)` is the product of the two parent flags.  The facet cardinality
condition in `potentialDiamond` makes the displayed finite product exactly
`p_(α,ρ) p_(β,ρ)`, while also forcing all non-candidate variables to zero. -/
private def forcedDiamondFlag (p : Shape → Shape → Bool)
    (ρ τ : Shape) : Bool :=
  if h : potentialDiamond ρ τ then
    if ∀ α ∈ oddFacets ρ τ, p α ρ = true then true else false
  else false

private def diamondVariables (p d : Shape → Shape → Bool) : Prop :=
  ∀ ρ τ, d τ ρ = forcedDiamondFlag p ρ τ

private def atMostOneDiamond (d : Shape → Shape → Bool) : Prop :=
  ∀ τ,
    (∑ ρ ∈ (Finset.univ : Finset Shape).filter
        (fun ρ => potentialDiamond ρ τ),
      boolNat (d τ ρ)) ≤ 1

private def basisMember (p d : Shape → Shape → Bool)
    (σ μ : Shape) : Prop :=
  μ = σ ∨
    (Odd (shapeArea σ) ∧ p σ μ = true) ∨
      (∃ ρ, d σ ρ = true ∧ μ ≠ σ ∧ shapeLE ρ μ ∧ shapeLE μ σ)

private def basisExpansion (c y : Shape → ℕ)
    (p d : Shape → Shape → Bool) : Prop :=
  ∀ μ, c μ =
    ∑ σ : Shape, if basisMember p d σ μ then y σ else 0

private def coordinateEquation (c y : Shape → ℕ)
    (p d : Shape → Shape → Bool) (μ : Shape) : Prop :=
  c μ =
    y μ +
      (∑ σ ∈ (Finset.univ : Finset Shape).filter (fun σ =>
        Odd (shapeArea σ) ∧ p σ μ = true), y σ) +
      (∑ τ ∈ (Finset.univ : Finset Shape).filter
          (fun τ => Even (shapeArea τ)),
        ∑ ρ ∈ (Finset.univ : Finset Shape).filter (fun ρ =>
          potentialDiamond ρ τ ∧ d τ ρ = true ∧ μ ≠ τ ∧
            shapeLE ρ μ ∧ shapeLE μ τ), y τ)

private abbrev Attachment := Fin 8 → Fin 17

private def validAttachment (p : Attachment) : Prop :=
  ∀ i, (p i).val ≤ 2 * i.val

private def attachmentList (p : Attachment) : List ℕ :=
  List.ofFn (fun i : Fin 8 => (p i).val)

private def insertUD (w : List Bool) (p : ℕ) : List Bool :=
  w.take p ++ [true, false] ++ w.drop p

private def insertUThenD (w : List Bool) (p : ℕ) : List Bool :=
  w.take p ++ [true] ++ w.drop p ++ [false]

private def dtsWord (p : Attachment) : List Bool :=
  (attachmentList p).foldl (fun w i => insertUD w i) []

private def matchingWord (p : Attachment) : List Bool :=
  (attachmentList p).foldl (fun w i => insertUThenD w i) []

/-- The exact DTS insertion carrier from the admitted perfect-matching model. -/
private def dtsCoefficient (lam mu : RawWord 8) : ℕ :=
  Fintype.card
    {p : Attachment //
      validAttachment p ∧
        dtsWord p = List.ofFn lam ∧ matchingWord p = List.ofFn mu}

private def inverseCupRow (lam mu : Shape) : ℕ :=
  dtsCoefficient lam.1 mu.1

/-- Necessary coordinate equations for an odd-parent basis.  The row `c` is
restricted to an admitted inverse-cup row through the DTS carrier, while the
parent and diamond flags are the exact one-hot/product variables of the
odd-parent rule. -/
def claim14873 : Prop :=
  ∀ (lam : Shape) (c y : Shape → ℕ)
    (p d : Shape → Shape → Bool),
    (∀ μ, c μ = inverseCupRow lam μ) →
      parentVariables p →
        diamondVariables p d →
          atMostOneDiamond d →
            basisExpansion c y p d →
              ∀ μ, 0 ≤ (y μ : ℤ) ∧ y μ ≤ c μ ∧
                coordinateEquation c y p d μ

end MathlibPlus.Open.ResearchFormalization.Claim14873
