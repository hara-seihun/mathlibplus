import MathlibPlus.Open.ResearchFormalizationBatch.UPolynomial

open Classical
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

namespace MathlibPlus.Open.ResearchFormalization.R0523Claim22338

noncomputable section

abbrev UPolynomial := MvPolynomial ℕ ℤ
abbrev ShiftedPolynomial := MvPolynomial (Option ℕ) ℤ

def yVariable (i : ℕ) : ShiftedPolynomial :=
  MvPolynomial.X (some i)

def yFactorIdeal (m : ℕ) : Ideal ShiftedPolynomial :=
  Ideal.span {p : ShiftedPolynomial |
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ m ∧ p = yVariable i}

def yTailIdeal (m : ℕ) : Ideal ShiftedPolynomial :=
  Ideal.span {p : ShiftedPolynomial |
    ∃ i : ℕ, 2 ≤ i ∧ i ≤ m ∧ p = yVariable i}

def setYOneZero (p : ShiftedPolynomial) : ShiftedPolynomial :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.C : ℤ →+* ShiftedPolynomial)
    (fun i : Option ℕ =>
      if i = some 1 then 0 else MvPolynomial.X i) p

def deletedVertices {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (S : Finset V) : SimpleGraph {v // v ∉ S} :=
  F.induce {v : V | v ∉ S}

def deletedUPolynomial {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (S : Finset V) : UPolynomial :=
  MvPolynomial.map (Nat.castRingHom ℤ)
    (MathlibPlus.Open.ResearchFormalizationBatch.graphUPolynomial
      (deletedVertices F S))

def independentVertexSet {V : Type*} [DecidableEq V]
    (F : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ ⦃u v : V⦄, u ∈ S → v ∈ S → u ≠ v → ¬F.Adj u v

def renameUToY (p : UPolynomial) : ShiftedPolynomial :=
  MvPolynomial.rename (fun n : ℕ => some n) p

def shiftedRootedFactor {V : Type*} [Fintype V] [DecidableEq V]
    (B : SimpleGraph V) (r : V) : ShiftedPolynomial :=
  ∑ I ∈ ((Finset.univ : Finset V).powerset).filter (fun I =>
    independentVertexSet B I ∧ r ∉ I),
    (-MvPolynomial.X none) ^ I.card * renameUToY (deletedUPolynomial B I)

def genuineOrderProduct {d : ℕ}
    (V : Fin d → Type*) [∀ i, Fintype (V i)]
    [∀ i, DecidableEq (V i)]
    (B : ∀ i : Fin d, SimpleGraph (V i))
    (r : ∀ i : Fin d, V i) : ShiftedPolynomial :=
  ∏ i : Fin d, shiftedRootedFactor (B i) (r i)

def genuineOrderFamily {d : ℕ}
    (V : Fin d → Type*) [∀ i, Fintype (V i)]
    (B : ∀ i : Fin d, SimpleGraph (V i)) (m : ℕ) : Prop :=
  ∀ i : Fin d, (B i).IsTree ∧ Fintype.card (V i) = m

def xOneIndependent (H : ShiftedPolynomial) : Prop :=
  ∀ a ∈ H.support, a (some 1) = 0

def xOneIndependentDifference (H P Q : ShiftedPolynomial) : Prop :=
  H = P - Q ∧ xOneIndependent H

/-- Genuine rooted order-m products use the displayed shifted cut factors;
independence of the x₁ coordinate is expressed on the actual polynomial
support, and the resulting specialization is placed in the tail ideal power. -/
def claim22338 : Prop :=
  ∀ {d : ℕ} (m : ℕ),
    0 < d →
      ∀ (V₁ V₂ : Fin d → Type*)
        [∀ i, Fintype (V₁ i)] [∀ i, DecidableEq (V₁ i)]
        [∀ i, Fintype (V₂ i)] [∀ i, DecidableEq (V₂ i)]
        (B₁ : ∀ i : Fin d, SimpleGraph (V₁ i))
        (r₁ : ∀ i : Fin d, V₁ i)
        (B₂ : ∀ i : Fin d, SimpleGraph (V₂ i))
        (r₂ : ∀ i : Fin d, V₂ i),
        genuineOrderFamily V₁ B₁ m →
          genuineOrderFamily V₂ B₂ m →
            let P := genuineOrderProduct V₁ B₁ r₁
            let Q := genuineOrderProduct V₂ B₂ r₂
            ∀ H : ShiftedPolynomial,
              xOneIndependentDifference H P Q →
                (∀ i : Fin d,
                  shiftedRootedFactor (B₁ i) (r₁ i) ∈ yFactorIdeal m) ∧
                  (∀ i : Fin d,
                    shiftedRootedFactor (B₂ i) (r₂ i) ∈ yFactorIdeal m) ∧
                  setYOneZero H ∈ (yTailIdeal m) ^ d

end

end MathlibPlus.Open.ResearchFormalization.R0523Claim22338
