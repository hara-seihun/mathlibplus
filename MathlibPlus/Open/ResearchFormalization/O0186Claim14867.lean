import Mathlib

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.O0186Claim14867

open Classical

abbrev RawWord14867 (n : ℕ) := Fin (2 * n) → Bool

def upCount14867 {n : ℕ} (w : RawWord14867 n)
    (t : Fin (2 * n + 1)) : ℕ :=
  ((Finset.univ : Finset (Fin (2 * n))).filter
    (fun i => i.val < t.val ∧ w i = true)).card

def downCount14867 {n : ℕ} (w : RawWord14867 n)
    (t : Fin (2 * n + 1)) : ℕ :=
  ((Finset.univ : Finset (Fin (2 * n))).filter
    (fun i => i.val < t.val ∧ w i = false)).card

def isDyck14867 {n : ℕ} (w : RawWord14867 n) : Prop :=
  upCount14867 w (Fin.last (2 * n)) = n ∧
    ∀ t, downCount14867 w t ≤ upCount14867 w t

abbrev Shape14867 := {w : RawWord14867 8 // isDyck14867 w}

def inversionCells14867 (w : RawWord14867 8) :
    Finset (Fin 16 × Fin 16) :=
  (Finset.univ : Finset (Fin 16 × Fin 16)).filter
    (fun p => p.1.val < p.2.val ∧
      w p.1 = false ∧ w p.2 = true)

def shapeArea14867 (σ : Shape14867) : ℕ :=
  (inversionCells14867 σ.1).card

def shapeLE14867 (ρ σ : Shape14867) : Prop :=
  inversionCells14867 ρ.1 ⊆ inversionCells14867 σ.1

def rookStrip14867 (ρ σ : Shape14867) : Prop :=
  let skew := inversionCells14867 σ.1 \ inversionCells14867 ρ.1
  (∀ i : Fin 16, (skew.filter (fun c => c.1 = i)).card ≤ 1) ∧
    (∀ j : Fin 16, (skew.filter (fun c => c.2 = j)).card ≤ 1)

def parentEdge14867 (σ ρ : Shape14867) : Prop :=
  Odd (shapeArea14867 σ) ∧
    Even (shapeArea14867 ρ) ∧
    shapeLE14867 ρ σ ∧
    shapeArea14867 σ = shapeArea14867 ρ + 1

def oddFacet14867 (α τ : Shape14867) : Prop :=
  Odd (shapeArea14867 α) ∧
    shapeLE14867 α τ ∧
    shapeArea14867 τ = shapeArea14867 α + 1

def oddFacets14867 (ρ τ : Shape14867) : Finset Shape14867 :=
  (Finset.univ : Finset Shape14867).filter (fun α =>
    oddFacet14867 α τ ∧ parentEdge14867 α ρ)

def potentialDiamond14867 (ρ τ : Shape14867) : Prop :=
  Even (shapeArea14867 ρ) ∧
    Even (shapeArea14867 τ) ∧
    shapeLE14867 ρ τ ∧
    shapeArea14867 τ = shapeArea14867 ρ + 2 ∧
    rookStrip14867 ρ τ ∧
    (oddFacets14867 ρ τ).card = 2

def boolNat14867 (b : Bool) : ℕ :=
  if b then 1 else 0

def parentVariables14867 (p : Shape14867 → Shape14867 → Bool) : Prop :=
  ∀ σ,
    (∀ ρ, ¬ parentEdge14867 σ ρ → p σ ρ = false) ∧
      (Odd (shapeArea14867 σ) →
        (Finset.filter (parentEdge14867 σ)
          (Finset.univ : Finset Shape14867)).sum
            (fun ρ => boolNat14867 (p σ ρ)) = 1)

def forcedDiamondFlag14867 (p : Shape14867 → Shape14867 → Bool)
    (ρ τ : Shape14867) : Bool :=
  if h : potentialDiamond14867 ρ τ then
    if ∀ α ∈ oddFacets14867 ρ τ, p α ρ = true then true else false
  else false

def diamondVariables14867
    (p d : Shape14867 → Shape14867 → Bool) : Prop :=
  ∀ ρ τ, d τ ρ = forcedDiamondFlag14867 p ρ τ

def atMostOneDiamond14867 (d : Shape14867 → Shape14867 → Bool) : Prop :=
  ∀ τ,
    (Finset.filter
      (fun ρ => potentialDiamond14867 ρ τ)
      (Finset.univ : Finset Shape14867)).sum
      (fun ρ => boolNat14867 (d τ ρ)) ≤ 1

/-- The selected lower endpoint is the forced grandparent when a diamond flag
is active, and is the upper shape itself when no flag is active. -/
def selectedInterval14867
    (d : Shape14867 → Shape14867 → Bool)
    (τ ρ : Shape14867) : Prop :=
  d τ ρ = true ∨ (ρ = τ ∧ ∀ η, d τ η = false)

/-- Claim 14867: an admissible odd-parent rule on the exact Catalan-shape
carrier uses one removable even parent per odd upper shape, the exact product
flags for commuting rank-two diamonds, and singleton fallback otherwise. -/
def claim14867 : Prop :=
  ∃ (p d : Shape14867 → Shape14867 → Bool),
    parentVariables14867 p ∧
    diamondVariables14867 p d ∧
    atMostOneDiamond14867 d ∧
    (∀ τ, Even (shapeArea14867 τ) →
      ∃! ρ, selectedInterval14867 d τ ρ)

end MathlibPlus.Open.ResearchFormalization.O0186Claim14867
