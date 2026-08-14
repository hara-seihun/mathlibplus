import Mathlib

noncomputable section

open scoped BigOperators

namespace MathlibPlus.Open.Arithmetic.CRTFiberBatch

/-- The fixed-base residue fiber used by the CRT claims. -/
def crtFiber (Q₀ Q : ℕ) (t₀ : ZMod Q₀) : Type :=
  {t : ZMod Q // (ZMod.val t % Q₀ : ZMod Q₀) = t₀}

/-- The free residue of a class modulo `Q` at a positive divisor `p`. -/
def crtFreeResidue (p Q : ℕ) (t : ZMod Q) : ZMod p :=
  (ZMod.val t % p : ZMod p)

/-- The coordinate-separable sum on a CRT fiber. -/
def crtCoordinateSum {P : Finset ℕ} {Q : ℕ}
    (F : ∀ p : {p // p ∈ P}, ZMod p → ℝ) (t : ZMod Q) : ℝ :=
  ∑ p : {p // p ∈ P}, F p (crtFreeResidue p.1 Q t)

noncomputable def crtFiberSup {Q₀ : ℕ} {P : Finset ℕ} (Q : ℕ)
    (t₀ : ZMod Q₀) (F : ∀ p : {p // p ∈ P}, ZMod p → ℝ) : ℝ :=
  sSup (Set.range (fun t : crtFiber Q₀ Q t₀ => crtCoordinateSum F t.1))

noncomputable def crtFiberInf {Q₀ : ℕ} {P : Finset ℕ} (Q : ℕ)
    (t₀ : ZMod Q₀) (F : ∀ p : {p // p ∈ P}, ZMod p → ℝ) : ℝ :=
  sInf (Set.range (fun t : crtFiber Q₀ Q t₀ => crtCoordinateSum F t.1))

noncomputable def crtCoordinateSup {P : Finset ℕ}
    (F : ∀ p : {p // p ∈ P}, ZMod p → ℝ) (p : {p // p ∈ P}) : ℝ :=
  sSup (Set.range (F p))

noncomputable def crtCoordinateInf {P : Finset ℕ}
    (F : ∀ p : {p // p ∈ P}, ZMod p → ℝ) (p : {p // p ∈ P}) : ℝ :=
  sInf (Set.range (F p))

/-- Claim 34564: a fixed-base CRT fiber is canonically the product of the
free prime coordinates.  The displayed equality records the canonical map,
rather than merely asserting an unstructured equivalence. -/
def claim34564 : Prop :=
  ∀ (Q₀ : ℕ) (P : Finset ℕ),
    0 < Q₀ →
    Squarefree Q₀ →
    (∀ p ∈ P, Nat.Prime p ∧ ¬p ∣ Q₀) →
    let Q := Q₀ * P.prod id
    ∀ t₀ : ZMod Q₀,
      ∃ e : crtFiber Q₀ Q t₀ ≃ (∀ p : {p // p ∈ P}, ZMod p),
        ∀ (t : crtFiber Q₀ Q t₀) (p : {p // p ∈ P}),
          e t p = crtFreeResidue p.1 Q t.1

/-- Claim 34565: the maximum of a coordinate-separable sum separates over a
fixed CRT fiber. -/
def claim34565 : Prop :=
  ∀ (Q₀ : ℕ) (P : Finset ℕ),
    0 < Q₀ →
    Squarefree Q₀ →
    (∀ p ∈ P, Nat.Prime p ∧ ¬p ∣ Q₀) →
    let Q := Q₀ * P.prod id
    ∀ (t₀ : ZMod Q₀)
      (F : ∀ p : {p // p ∈ P}, ZMod p → ℝ),
      crtFiberSup Q t₀ F = ∑ p : {p // p ∈ P}, crtCoordinateSup F p

/-- Claim 34566: the minimum factorization corresponding to claim 34565. -/
def claim34566 : Prop :=
  ∀ (Q₀ : ℕ) (P : Finset ℕ),
    0 < Q₀ →
    Squarefree Q₀ →
    (∀ p ∈ P, Nat.Prime p ∧ ¬p ∣ Q₀) →
    let Q := Q₀ * P.prod id
    ∀ (t₀ : ZMod Q₀)
      (F : ∀ p : {p // p ∈ P}, ZMod p → ℝ),
      crtFiberInf Q t₀ F = ∑ p : {p // p ∈ P}, crtCoordinateInf F p

/-- The coordinate form of the no-cancellation assertion. -/
def coordinateExtremesSeparate {Q₀ : ℕ} {P : Finset ℕ} (Q : ℕ)
    (t₀ : ZMod Q₀) (E : ∀ p : {p // p ∈ P}, ZMod p → ℝ) : Prop :=
  crtFiberSup Q t₀ E = ∑ p : {p // p ∈ P}, crtCoordinateSup E p ∧
  crtFiberInf Q t₀ E = ∑ p : {p // p ∈ P}, crtCoordinateInf E p

/-- Claim 34568: once each section error is a function of its free tail
coordinate, an adversarial CRT choice realizes all individual extrema at once. -/
def claim34568 : Prop :=
  ∀ (Q₀ : ℕ) (P : Finset ℕ),
    0 < Q₀ →
    Squarefree Q₀ →
    (∀ p ∈ P, Nat.Prime p ∧ ¬p ∣ Q₀) →
    let Q := Q₀ * P.prod id
    ∀ (t₀ : ZMod Q₀)
      (E : ∀ p : {p // p ∈ P}, ZMod p → ℝ),
      coordinateExtremesSeparate Q t₀ E

end MathlibPlus.Open.Arithmetic.CRTFiberBatch
