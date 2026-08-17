import Mathlib

namespace MathlibPlus.Open.NewResearch2.R0552TraceCoatomObstruction

noncomputable section

open Classical
attribute [local instance] Classical.propDecidable Classical.decEq

private def familyGround {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) : Finset α :=
  F.biUnion (fun A => A)

private def unionClosed {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F

private def outsideSupport {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (T : Finset α) : Finset α :=
  familyGround F \ T

private def traceCell {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (T B : Finset α) : Finset (Finset α) :=
  T.powerset.filter (fun S => S ∪ B ∈ F)

private def traceProduct {α : Type*} [DecidableEq α]
    (H K : Finset (Finset α)) : Finset (Finset α) :=
  H.biUnion (fun S => K.image (fun R => S ∪ R))

private def traceProductLaw {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (T : Finset α) : Prop :=
  ∀ B ∈ (outsideSupport F T).powerset,
    ∀ C ∈ (outsideSupport F T).powerset,
      traceProduct (traceCell F T B) (traceCell F T C) ⊆
        traceCell F T (B ∪ C)

private def finiteTraceLabeledSupport {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset (Finset α)) (T : Finset α) : Prop :=
  F.Nonempty ∧ unionClosed F ∧ T.card = 3 ∧
    T ⊆ familyGround F ∧ traceProductLaw F T

private def tightTriple {α : Type*} [DecidableEq α]
    (T : Finset α) (t : Fin 3 → α) : Prop :=
  T = (Finset.univ : Finset (Fin 3)).image t ∧ Function.Injective t

private def topOnlyTarget {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset (Finset α)) (T U : Finset α) : Prop :=
  U ⊆ outsideSupport F T ∧ traceCell F T U = {T}

private def coatomCompatibleMasks {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset (Finset α)) (T U : Finset α)
    (t : Fin 3 → α) (c : Fin 3) : Finset (Finset α) :=
  U.powerset.filter (fun B =>
    (traceCell F T B ∩ (T.erase (t c)).powerset).Nonempty)

private def maskUnion {α : Type*} [DecidableEq α]
    (A : Finset (Finset α)) : Finset α :=
  A.biUnion (fun B => B)

/-- Claim 22612: under the exact finite trace-cell product law, every top-only
coatom-compatible mask union is a proper subset of the target outside mask. -/
def claim22612 : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset (Finset α)) (T U : Finset α)
    (t : Fin 3 → α) (c : Fin 3),
    finiteTraceLabeledSupport F T →
    tightTriple T t →
    topOnlyTarget F T U →
      maskUnion (coatomCompatibleMasks F T U t c) ⊆ U ∧
        maskUnion (coatomCompatibleMasks F T U t c) ≠ U

end

end MathlibPlus.Open.NewResearch2.R0552TraceCoatomObstruction
